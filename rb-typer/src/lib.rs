use std::collections::HashMap;

use indexmap::IndexSet;
use la_arena::Arena;
use rb_diagnostic::{Span, emit};
use rb_hir::{
  FunctionSpanMap,
  ast::{self as hir, ExprId, LocalId, StmtId},
};
use ty::{TypeVar, VType, VarId};

mod ty;

pub use ty::{Environment, Type};

use crate::ty::{IntId, IntVar};

#[cfg(test)]
#[macro_use]
extern crate rb_test;

/// A typechecker for a function body.
///
/// A new Typer should be constructed for every region that has inferred types.
/// So, function bodies each get a typer, as they have explicit signatures.
#[derive(Clone)]
pub struct Typer<'a> {
  // Inputs to the typer: the environment, an HIR tree, and a map of spans for diagnostics.
  env:      &'a Environment,
  function: &'a hir::Function,
  span_map: &'a FunctionSpanMap,

  // Outputs of the typer: a map of expressions to their rendered types.
  exprs: HashMap<ExprId, VType>,

  // Type variables.
  integers:  Arena<IntVar>,
  variables: Arena<TypeVar>,

  // Variables in the current block.
  //
  // TODO: This is probably wrong on a few levels, need a wrapper struct for typing each block.
  local_functions: HashMap<String, Type>,
  locals:          HashMap<hir::LocalId, VType>,
}

pub fn type_of_function(func: &hir::Function) -> Type {
  let args = func.sig.args.iter().map(|(_, ty)| type_of_type_expr(ty)).collect();
  let ret = Box::new(type_of_type_expr(&func.sig.ret));

  Type::Function(args, ret)
}

// TODO: Need a version of this that can resolve names.
pub fn type_of_type_expr(te: &hir::TypeExpr) -> Type {
  match te {
    hir::TypeExpr::Primitive(t) => Type::Primitive(*t),
    hir::TypeExpr::Struct(path) => Type::Struct(path.clone()),
    hir::TypeExpr::Tuple(tys) => Type::Tuple(tys.iter().map(type_of_type_expr).collect()),
  }
}

impl<'a> Typer<'a> {
  fn new(env: &'a Environment, function: &'a hir::Function, span_map: &'a FunctionSpanMap) -> Self {
    Typer {
      env,
      function,
      span_map,
      exprs: HashMap::new(),
      integers: Arena::new(),
      variables: Arena::new(),
      local_functions: HashMap::new(),
      locals: HashMap::new(),
    }
  }

  /// Typecheck a function body.
  pub fn check(
    env: &'a Environment,
    function: &'a hir::Function,
    span_map: &'a FunctionSpanMap,
  ) -> Self {
    let mut typer = Typer::new(env, function, span_map);

    for (id, local) in function.locals.iter() {
      if let Some(ref ty) = local.ty {
        let ty = type_of_type_expr(ty);

        typer.locals.insert(id, ty.into());
      }
    }

    for &item in function.body.iter().flatten() {
      if let hir::Stmt::FunctionDef(ref func) = function.stmts[item] {
        let args = func.args.iter().map(|(_, ty)| type_of_type_expr(ty)).collect();
        let ret = match func.ret {
          Some(ref ty) => Box::new(type_of_type_expr(ty)),
          None => Box::new(Type::unit()),
        };

        let ty = Type::Function(args, ret);
        typer.local_functions.insert(func.name.clone(), ty);
      }
    }

    if let Some(body) = &function.body {
      for &item in body {
        typer.type_stmt(item);
      }

      let ret = function.ret.clone().map_or(Type::unit(), |ty| type_of_type_expr(&ty));

      match body.last().map(|tail| &typer.function.stmts[*tail]) {
        Some(hir::Stmt::Expr(e)) => {
          typer.check_expr(*e, &VType::from(ret.clone()));
        }
        _ => {
          if !typer.is_subtype(&VType::from(ret), &VType::from(Type::unit())) {
            panic!("expected result");
          }
        }
      }
    }

    typer
  }

  pub fn type_of_expr(&self, expr: ExprId) -> Type { self.lower_type(&self.exprs[&expr]) }
  pub fn type_of_local(&self, local: LocalId) -> Type { self.lower_type(&self.locals[&local]) }

  fn lower_type(&self, ty: &VType) -> Type {
    match ty {
      VType::SelfT => Type::SelfT,
      VType::Primitive(lit) => Type::Primitive(*lit),

      // Integers default to i64.
      VType::Integer(id) => {
        Type::Primitive(self.integers[*id].concrete.unwrap_or(hir::PrimitiveType::I64))
      }

      VType::Array(ty) => Type::Array(Box::new(self.lower_type(ty))),
      VType::Tuple(tys) => Type::Tuple(tys.iter().map(|t| self.lower_type(t)).collect()),
      VType::Function(args, ret) => Type::Function(
        args.iter().map(|t| self.lower_type(t)).collect(),
        Box::new(self.lower_type(ret)),
      ),

      VType::Var(v) => self.anneal(*v),

      VType::Union(tys) => Type::Union(tys.iter().map(|ty| self.lower_type(ty)).collect()),

      VType::Struct(path) => Type::Struct(path.clone()),
    }
  }

  fn anneal(&self, v: VarId) -> Type {
    use hir::PrimitiveType::*;

    let var = &self.variables[v];

    let values = var
      .values
      .keys()
      .map(|t| match t {
        VType::Var(v) => VType::from(self.anneal(*v)),
        t => t.clone(),
      })
      .collect::<IndexSet<_>>();

    let uses = var
      .uses
      .keys()
      .map(|t| match t {
        VType::Var(v) => VType::from(self.anneal(*v)),
        t => t.clone(),
      })
      .filter(|t| !values.contains(t))
      .collect::<Vec<_>>();

    let values = values.into_iter().collect::<Vec<_>>();

    match (values.as_slice(), uses.as_slice()) {
      ([a], []) => self.lower_type(&a),
      ([a], [b]) if a == b => self.lower_type(&a),

      ([VType::Integer(_)], [VType::Primitive(I8)]) => I8.into(),
      ([VType::Integer(_)], [VType::Primitive(I16)]) => I16.into(),
      ([VType::Integer(_)], [VType::Primitive(I32)]) => I32.into(),
      ([VType::Integer(_)], [VType::Primitive(I64)]) => I64.into(),
      ([VType::Integer(_)], [VType::Primitive(U8)]) => U8.into(),
      ([VType::Integer(_)], [VType::Primitive(U16)]) => U16.into(),
      ([VType::Integer(_)], [VType::Primitive(U32)]) => U32.into(),
      ([VType::Integer(_)], [VType::Primitive(U64)]) => U64.into(),

      // Unions?
      (_, [u1, u2]) => {
        emit!(var.span => "cannot unify types {} and {}", self.display_type(&u1), self.display_type(&u2));
        Type::unit()
      }
      (_, uses) => {
        emit!(var.span => "cannot unify types {uses:?}");
        Type::unit()
      }
    }
  }

  fn span(&self, expr: ExprId) -> Span { self.span_map.exprs[expr.into_raw().into_u32() as usize] }

  fn type_stmt(&mut self, stmt: StmtId) {
    match self.function.stmts[stmt] {
      hir::Stmt::Expr(expr) => {
        self.synth_expr(expr);
      }
      hir::Stmt::Let(_, ref id, ref te, expr) => {
        if let Some(te) = te {
          let ty = VType::from(type_of_type_expr(te));
          self.check_expr(expr, &ty);
          self.locals.insert(id.unwrap(), ty);
        } else {
          match self.synth_expr(expr) {
            Some(t) => {
              self.locals.insert(id.unwrap(), t);
            }
            None => {
              emit!(self.span(expr) => "could not infer type for let binding");
            }
          }
        }
      }

      hir::Stmt::FunctionDef(_) => {}
      hir::Stmt::Struct => {}
    }
  }

  fn fresh_var(&mut self, span: Span, description: String) -> VarId {
    let var = TypeVar::new(span, description);
    self.variables.alloc(var)
  }

  fn synth_expr(&mut self, expr: ExprId) -> Option<VType> {
    let ty = match self.function.exprs[expr] {
      hir::Expr::Literal(ref lit) => match lit {
        hir::Literal::Nil => VType::unit(),
        hir::Literal::Bool(_) => VType::Primitive(hir::PrimitiveType::Bool),
        hir::Literal::Int(_) => self.fresh_int(&[]),
      },

      hir::Expr::String(ref segments) => {
        for segment in segments {
          match segment {
            hir::StringInterp::Literal(_) => {}
            hir::StringInterp::Expr(expr) => {
              // TODO: Constraint this to be stringifiable (currently everything is, but later
              // we want to restrict that).
              self.synth_expr(*expr);
            }
          }
        }

        VType::Primitive(hir::PrimitiveType::Str)
      }

      hir::Expr::Array(ref exprs) => {
        for &expr in exprs {
          let _t = self.synth_expr(expr);
        }

        VType::Array(Box::new(VType::unit()))
      }

      hir::Expr::Call(lhs_expr, ref args) => match self.function.exprs[lhs_expr] {
        hir::Expr::Field(lhs, ref method) => {
          let lhs = self.synth_expr(lhs)?;

          // We must have a concrete type by the time we resolve methods.
          if let Some(path) = self.resolve_type(&lhs) {
            if let Some(signature) = self.env.impl_type(&path, &method) {
              let ret = VType::Var(
                self.fresh_var(self.span(expr), format!("return type of calling {path}::{method}")),
              );

              // This is an impl method, so fill in `self` with the type we're calling it on.
              let signature = signature.resolve_self(&lhs);

              todo!()
              /*
              let call_type = VType::Function(
                std::iter::once(lhs.clone())
                  .chain(args.iter().map(|&arg| self.synth_expr(arg)))
                  .collect(),
                Box::new(ret.clone()),
              );

              self.constrain(&signature.clone().into(), &call_type, self.span(lhs_expr));

              ret
              */
            } else {
              emit!(self.span(expr) => "method {} not found for type {}", method, self.display_type(&lhs));

              Type::unit().into()
            }
          } else {
            emit!(self.span(expr) => "could not resolve concrete type for {}", self.display_type(&lhs));

            Type::unit().into()
          }
        }

        _ => {
          let lhs = self.synth_expr(lhs_expr);

          let ret = VType::Var(
            self.fresh_var(self.span(expr), format!("return type of calling {:?}", lhs)),
          );

          todo!()
          /*
          let call_type = VType::Function(
            args.iter().map(|&arg| self.synth_expr(arg)).collect(),
            Box::new(ret.clone()),
          );

          self.constrain(&lhs, &call_type, self.span(lhs_expr));

          ret
          */
        }
      },

      hir::Expr::Name(ref path) => {
        if let Some(ident) = path.as_single()
          && let Some(ty) = self.local_functions.get(ident)
        {
          ty.clone().into()
        } else {
          match self.env.names.get(&path) {
            Some(ty) => VType::from(ty.clone()),
            None => panic!("could not resolve {path}"),
          }
        }
      }

      hir::Expr::Local(id) => self.locals[&id].clone(),

      hir::Expr::Block(ref block) => {
        todo!()
      }

      hir::Expr::Paren(expr) => self.synth_expr(expr)?,

      hir::Expr::UnaryOp(expr, ref op) => {
        let ty = self.synth_expr(expr)?;

        let ret =
          VType::Var(self.fresh_var(self.span(expr), format!("return type of binary op {op:?}")));

        let call_type = VType::Function(vec![ty], Box::new(ret.clone()));

        ret
      }

      hir::Expr::BinaryOp(lhs_expr, ref op, rhs_expr) => {
        let lhs = self.synth_expr(lhs_expr)?;
        let rhs = self.synth_expr(rhs_expr)?;

        use hir::PrimitiveType::*;

        // NB: Binary ops are special. If either side is a specific integer type, it
        // coerces.
        //
        // This is not like `a.add(b)`, where the left hand side must be concrete.
        let res = match (&lhs, &rhs) {
          (VType::Integer(l), VType::Integer(r)) => self.fresh_int(&[*l, *r]),

          (VType::Primitive(I8), VType::Integer(_) | VType::Primitive(I8)) => I8.into(),
          (VType::Primitive(I16), VType::Integer(_) | VType::Primitive(I16)) => I16.into(),
          (VType::Primitive(I32), VType::Integer(_) | VType::Primitive(I32)) => I32.into(),
          (VType::Primitive(I64), VType::Integer(_) | VType::Primitive(I64)) => I64.into(),
          (VType::Primitive(U8), VType::Integer(_) | VType::Primitive(U8)) => U8.into(),
          (VType::Primitive(U16), VType::Integer(_) | VType::Primitive(U16)) => U16.into(),
          (VType::Primitive(U32), VType::Integer(_) | VType::Primitive(U32)) => U32.into(),
          (VType::Primitive(U64), VType::Integer(_) | VType::Primitive(U64)) => U64.into(),

          (VType::Integer(_), VType::Primitive(I8)) => I8.into(),
          (VType::Integer(_), VType::Primitive(I16)) => I16.into(),
          (VType::Integer(_), VType::Primitive(I32)) => I32.into(),
          (VType::Integer(_), VType::Primitive(I64)) => I64.into(),
          (VType::Integer(_), VType::Primitive(U8)) => U8.into(),
          (VType::Integer(_), VType::Primitive(U16)) => U16.into(),
          (VType::Integer(_), VType::Primitive(U32)) => U32.into(),
          (VType::Integer(_), VType::Primitive(U64)) => U64.into(),

          _ => {
            emit!(self.span(expr) => "cannot apply binary operator {:?} to types", op);
            return None;
          }
        };

        if !matches!(res, VType::Integer(_)) {
          self.pin_integer(&lhs, &res);
          self.pin_integer(&rhs, &res);
        }

        res
      }

      hir::Expr::Index(lhs, rhs) => {
        let lhs = self.synth_expr(lhs)?;
        let rhs = self.synth_expr(rhs)?;

        let elem = VType::Var(self.fresh_var(self.span(expr), "array element".to_string()));

        elem
      }

      hir::Expr::Field(lhs, _) => {
        let lhs = self.synth_expr(lhs)?;

        // TODO

        lhs
      }

      hir::Expr::If { cond, then, els } => {
        self.check_expr(cond, &VType::Primitive(hir::PrimitiveType::Bool));

        let then_ty = self.synth_expr(then)?;
        if let Some(els) = els {
          let els_ty = self.synth_expr(els)?;

          let res = self.fresh_var(self.span(expr), "if statment foo".to_string());
          let res = VType::Var(res);

          res
        } else {
          then_ty
        }
      }

      hir::Expr::StructInit(ref path, ref fields) => {
        let strct =
          self.env.structs.get(path).unwrap_or_else(|| panic!("no struct at path {path:?}"));

        for &(ref k, v) in fields {
          let Some(field) = strct.iter().find(|(n, _)| n == k) else {
            emit!(self.span(v) => "field {k} not found in struct {path}");
            continue;
          };

          self.check_expr(v, &VType::from(field.1.clone()));
        }

        VType::Struct(path.clone())
      }

      ref v => unimplemented!("type_expr {v:?}"),
    };

    self.exprs.insert(expr, ty.clone());
    Some(ty)
  }

  fn check_expr(&mut self, expr: ExprId, expected: &VType) -> bool {
    match self.function.exprs[expr] {
      hir::Expr::If { cond, then, els } => {
        self.check_expr(cond, &VType::Primitive(hir::PrimitiveType::Bool))
          && self.check_expr(then, expected)
          && if let Some(els) = els { self.check_expr(els, expected) } else { true }
      }

      _ => match self.synth_expr(expr) {
        Some(inferred) => {
          if self.is_subtype(&inferred, expected) {
            true
          } else {
            emit!(self.span(expr) => "expected {}, found {}", self.display_type(&expected), self.type_of_expr(expr));
            false
          }
        }
        None => {
          emit!(self.span(expr) => "expected {}, found {}", self.display_type(&expected), self.type_of_expr(expr));
          false
        }
      },
    }
  }

  fn is_subtype(&self, a: &VType, b: &VType) -> bool {
    match (a, b) {
      (a, b) if a == b => true,

      (VType::Integer(_), VType::Primitive(hir::PrimitiveType::I8)) => true,
      (VType::Integer(_), VType::Primitive(hir::PrimitiveType::I16)) => true,
      (VType::Integer(_), VType::Primitive(hir::PrimitiveType::I32)) => true,
      (VType::Integer(_), VType::Primitive(hir::PrimitiveType::I64)) => true,
      (VType::Integer(_), VType::Primitive(hir::PrimitiveType::U8)) => true,
      (VType::Integer(_), VType::Primitive(hir::PrimitiveType::U16)) => true,
      (VType::Integer(_), VType::Primitive(hir::PrimitiveType::U32)) => true,
      (VType::Integer(_), VType::Primitive(hir::PrimitiveType::U64)) => true,

      _ => false,
    }
  }

  fn fresh_int(&mut self, deps: &[IntId]) -> VType {
    let id =
      self.integers.alloc(IntVar { deps: deps.iter().copied().collect(), concrete: None });

    VType::Integer(id)
  }

  fn pin_integer(&mut self, ty: &VType, target: &VType) {
    let target = match target {
      VType::Primitive(prim) => *prim,
      _ => panic!("can only pin integer to primitive type"),
    };

    if let VType::Integer(id) = *ty {
      let mut stack = vec![id];
      while let Some(id) = stack.pop() {
        let int = &self.integers[id];
        for dep in &int.deps {
          stack.push(*dep);
        }

        if self.integers[id].concrete.is_some() {
          panic!("conflicting integer type constraints");
        }
        self.integers[id].concrete = Some(target);
      }
    }
  }

  fn resolve_type(&self, ty: &VType) -> Option<hir::Path> {
    match self.lower_type(ty) {
      Type::Primitive(hir::PrimitiveType::I8) => Some(hir::Path::from(["i8"])),
      Type::Primitive(hir::PrimitiveType::I16) => Some(hir::Path::from(["i16"])),
      Type::Primitive(hir::PrimitiveType::I32) => Some(hir::Path::from(["i32"])),
      Type::Primitive(hir::PrimitiveType::I64) => Some(hir::Path::from(["i64"])),
      Type::Primitive(hir::PrimitiveType::U8) => Some(hir::Path::from(["u8"])),
      Type::Primitive(hir::PrimitiveType::U16) => Some(hir::Path::from(["u16"])),
      Type::Primitive(hir::PrimitiveType::U32) => Some(hir::Path::from(["u32"])),
      Type::Primitive(hir::PrimitiveType::U64) => Some(hir::Path::from(["u64"])),

      Type::Struct(path) => Some(path.clone()),

      _ => None,
    }
  }
}

#[cfg(test)]
fn check(body: &str, expected: rb_test::Expect) { check_inner(body, false, expected); }
#[cfg(test)]
#[allow(dead_code)]
fn check_v(body: &str, expected: rb_test::Expect) { check_inner(body, true, expected); }

#[cfg(test)]
fn check_inner(body: &str, verbose: bool, expected: rb_test::Expect) {
  use std::fmt::Write;

  let (sources, body, span_map) = rb_hir_lower::parse_body(body);
  let mut out = String::new();
  let mut debug = String::new();
  let res = rb_diagnostic::run(sources.clone(), || {
    let env = Environment::mini();
    let typer = crate::Typer::check(&env, &body, &span_map);

    for (id, local) in body.locals.iter() {
      let ty = typer.type_of_local(id);
      writeln!(out, "{}: {}", local.name, ty).unwrap();
    }

    if verbose {
      writeln!(debug).unwrap();

      for (v, var) in typer.variables.iter() {
        writeln!(debug, "v{} ({}):", v.into_raw().into_u32(), var.description).unwrap();
        for v in var.values.keys() {
          writeln!(debug, "  + {:?}", v).unwrap();
        }
        for u in var.uses.keys() {
          writeln!(debug, "  - {:?}", u).unwrap();
        }
      }
    }
  });

  match res {
    Ok(()) => expected.assert_eq(&format!("{out}{debug}")),
    Err(e) => {
      let mut out = String::new();
      for e in e {
        write!(out, "{}", e.render(&sources)).unwrap();
      }
      expected.assert_eq(&format!("{out}{debug}"));
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn simple_check() {
    check(
      r#"
      let a: str = "hi"
      "#,
      expect![@r#"
        a: str
      "#],
    );

    check(
      r#"
      let a: i32 = "hi"
      "#,
      expect![@r#"
        error: expected i32, found str
         --> inline.rbr:2:20
          |
        2 |       let a: i32 = "hi"
          |                    ^^^^
      "#],
    );

    check(
      r#"
      let a = "hi"
      let b: i64 = a
      "#,
      expect![@r#"
        error: expected i64, found str
         --> inline.rbr:3:20
          |
        3 |       let b: i64 = a
          |                    ^
      "#],
    );
  }

  #[test]
  fn infer_numbers() {
    check(
      r#"
      let a = 3
      "#,
      expect![@r#"
        a: i64
      "#],
    );

    check(
      r#"
      let a: i32 = 3
      "#,
      expect![@r#"
        a: i32
      "#],
    );

    check(
      r#"
      let a: i32 = 3
      let b = a
      "#,
      expect![@r#"
        a: i32
        b: i32
      "#],
    );
  }

  #[test]
  fn unify_addition() {
    check(
      "
      let a: i8 = 3
      let b = a + 1
      ",
      expect![@r#"
        a: i8
        b: i8
      "#],
    );

    check(
      "
      let a: i32 = 3
      let b = a + 1
      ",
      expect![@r#"
        a: i32
        b: i32
      "#],
    );

    check(
      "
      let a: i32 = 3
      let b = 1
      let c = a + b
      ",
      expect![@r#"
        a: i32
        b: i32
        c: i32
      "#],
    );
  }

  #[test]
  fn unify_equality() {
    check(
      "
      let a: i32 = 3
      let b = 4
      let c = a == b
      ",
      expect![@r#"
        a: i32
        b: i32
        c: bool
      "#],
    );
  }

  #[test]
  fn unify_comparison() {
    check(
      "
      let a: i32 = 3
      let b = 4
      let c = a < b
      ",
      expect![@r#"
        a: i32
        b: i32
        c: bool
      "#],
    );
  }

  #[test]
  fn check_comparison() {
    check(
      r#"
      let a: i32 = 3
      let b: i8 = 4
      let c = a < b
      "#,
      expect![@r#"
        error: i8 is not a subtype of i32
         --> inline.rbr:4:19
          |
        4 |       let c = a < b
          |                   ^
      "#],
    );
  }

  #[test]
  fn trait_resolution() {
    check(
      r#"
      let a: i32 = 3
      let b = a.add(1)
      "#,
      expect![@r#"
        a: i32
        b: i32
      "#],
    );

    check_v(
      r#"
      let a: i32 = 3
      let b = 4
      let c = a.add(b)
      "#,
      expect![@r#"
        a: i32
        b: i32
        c: i32

        v0 (integer):
          + Integer
          - Primitive(I32)
        v1 (integer):
          + Integer
          - Primitive(I32)
        v2 (return type of calling i32::add):
          + Primitive(I32)
      "#],
    );
  }
}
