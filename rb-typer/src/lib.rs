use std::collections::HashMap;

use indexmap::IndexSet;
use la_arena::Arena;
use rb_diagnostic::{Span, emit};
use rb_hir::{
  FunctionSpanMap,
  ast::{self as hir, ExprId, LocalId, StmtId},
};
use ty::{TypeVar, VType, VarId};

mod constrain;
mod ty;

pub use ty::{Environment, Type};

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
  variables: Arena<TypeVar>,

  // Variables in the current block.
  //
  // TODO: This is probably wrong on a few levels, need a wrapper struct for typing each block.
  local_functions: HashMap<String, Type>,
  locals:          HashMap<hir::LocalId, VType>,
}

pub fn type_of_function(func: &hir::Function) -> Type {
  let args = func.args.iter().map(|(_, ty)| type_of_type_expr(ty)).collect();
  let ret = match func.ret {
    Some(ref ty) => Box::new(type_of_type_expr(ty)),
    None => Box::new(Type::unit()),
  };

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

    for &item in function.body.iter().flatten() {
      typer.type_stmt(item);
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
      VType::Integer => Type::Primitive(hir::PrimitiveType::I64),

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

      ([VType::Integer], [VType::Primitive(I8)]) => I8.into(),
      ([VType::Integer], [VType::Primitive(I16)]) => I16.into(),
      ([VType::Integer], [VType::Primitive(I32)]) => I32.into(),
      ([VType::Integer], [VType::Primitive(I64)]) => I64.into(),
      ([VType::Integer], [VType::Primitive(U8)]) => U8.into(),
      ([VType::Integer], [VType::Primitive(U16)]) => U16.into(),
      ([VType::Integer], [VType::Primitive(U32)]) => U32.into(),
      ([VType::Integer], [VType::Primitive(U64)]) => U64.into(),

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
        self.type_expr(expr);
      }
      hir::Stmt::Let(_, ref id, ref te, expr) => {
        let res = self.type_expr(expr);
        if let Some(te) = te {
          let ty = VType::from(type_of_type_expr(te));
          self.constrain(&res, &ty, self.span(expr));
          self.locals.insert(id.unwrap(), ty);
        } else {
          self.locals.insert(id.unwrap(), res);
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

  fn type_expr(&mut self, expr: ExprId) -> VType {
    let ty = match self.function.exprs[expr] {
      hir::Expr::Literal(ref lit) => match lit {
        hir::Literal::Nil => VType::Tuple(vec![]),
        hir::Literal::Bool(_) => VType::Primitive(hir::PrimitiveType::Bool),
        hir::Literal::Int(_) => {
          let v = self.fresh_var(self.span(expr), "integer".to_string());

          self.constrain(&VType::Integer, &VType::Var(v), self.span(expr));

          VType::Var(v)
        }
      },

      hir::Expr::String(ref segments) => {
        for segment in segments {
          match segment {
            hir::StringInterp::Literal(_) => {}
            hir::StringInterp::Expr(expr) => {
              // TODO: Constraint this to be stringifiable (currently everything is, but later
              // we want to restrict that).
              self.type_expr(*expr);
            }
          }
        }

        VType::Primitive(hir::PrimitiveType::Str)
      }

      hir::Expr::Array(ref exprs) => {
        let v = self.fresh_var(self.span(expr), "array element".to_string());

        for &expr in exprs {
          let e = self.type_expr(expr);
          self.constrain(&e, &VType::Var(v), self.span(expr));
        }

        VType::Array(Box::new(VType::Var(v)))
      }

      hir::Expr::Call(lhs_expr, ref args) => match self.function.exprs[lhs_expr] {
        hir::Expr::Field(lhs, ref method) => {
          let lhs = self.type_expr(lhs);

          // We must have a concrete type by the time we resolve methods.
          if let Some(path) = self.resolve_type(&lhs) {
            if let Some(signature) = self.env.impl_type(&path, &method) {
              let ret = VType::Var(
                self.fresh_var(self.span(expr), format!("return type of calling {path}::{method}")),
              );

              // This is an impl method, so fill in `self` with the type we're calling it on.
              let signature = signature.resolve_self(&lhs);

              let call_type = VType::Function(
                std::iter::once(lhs.clone())
                  .chain(args.iter().map(|&arg| self.type_expr(arg)))
                  .collect(),
                Box::new(ret.clone()),
              );

              self.constrain(&signature.clone().into(), &call_type, self.span(lhs_expr));

              ret
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
          let lhs = self.type_expr(lhs_expr);

          let ret = VType::Var(
            self.fresh_var(self.span(expr), format!("return type of calling {:?}", lhs)),
          );

          let call_type = VType::Function(
            args.iter().map(|&arg| self.type_expr(arg)).collect(),
            Box::new(ret.clone()),
          );

          self.constrain(&lhs, &call_type, self.span(lhs_expr));

          ret
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
        // FIXME: Make a new scope here for the block.
        for &stmt in block {
          self.type_stmt(stmt);
        }

        match block.last() {
          Some(stmt) => match self.function.stmts[*stmt] {
            hir::Stmt::Expr(expr) => self.type_expr(expr),
            _ => VType::Tuple(vec![]),
          },
          None => VType::Tuple(vec![]),
        }
      }

      hir::Expr::Paren(expr) => self.type_expr(expr),

      hir::Expr::UnaryOp(expr, ref op) => {
        let ty = self.type_expr(expr);

        let ret =
          VType::Var(self.fresh_var(self.span(expr), format!("return type of binary op {op:?}")));

        let call_type = VType::Function(vec![ty], Box::new(ret.clone()));

        match op {
          hir::UnaryOp::Neg => {
            self.constrain(
              &VType::Function(vec![VType::Integer], Box::new(VType::Integer)),
              &call_type,
              self.span(expr),
            );
          }

          hir::UnaryOp::Not => {
            self.constrain(
              &VType::Function(
                vec![hir::PrimitiveType::Bool.into()],
                Box::new(hir::PrimitiveType::Bool.into()),
              ),
              &call_type,
              self.span(expr),
            );
          }
        }

        ret
      }

      hir::Expr::BinaryOp(lhs_expr, ref op, rhs_expr) => {
        let lhs = self.type_expr(lhs_expr);
        let rhs = self.type_expr(rhs_expr);

        match op {
          hir::BinaryOp::Add
          | hir::BinaryOp::Sub
          | hir::BinaryOp::Mul
          | hir::BinaryOp::Div
          | hir::BinaryOp::Mod
          | hir::BinaryOp::BitOr
          | hir::BinaryOp::BitAnd
          | hir::BinaryOp::Xor
          | hir::BinaryOp::ShiftLeft
          | hir::BinaryOp::ShiftRight => {
            self.constrain(&lhs, &VType::Integer, self.span(rhs_expr));
            self.constrain(&rhs, &lhs, self.span(rhs_expr));

            lhs
          }

          hir::BinaryOp::Eq | hir::BinaryOp::Neq => {
            self.constrain(&lhs, &rhs, self.span(rhs_expr));

            hir::PrimitiveType::Bool.into()
          }

          hir::BinaryOp::Lt | hir::BinaryOp::Lte | hir::BinaryOp::Gt | hir::BinaryOp::Gte => {
            self.constrain(&lhs, &VType::Integer, self.span(rhs_expr));
            self.constrain(&rhs, &lhs, self.span(rhs_expr));

            hir::PrimitiveType::Bool.into()
          }

          _ => unimplemented!("binary op {op:?}"),
        }
      }

      hir::Expr::Index(lhs, rhs) => {
        let lhs = self.type_expr(lhs);
        let rhs = self.type_expr(rhs);

        let elem = VType::Var(self.fresh_var(self.span(expr), "array element".to_string()));

        self.constrain(&lhs, &VType::Array(Box::new(elem.clone())), self.span(expr));
        self.constrain(&rhs, &VType::Primitive(hir::PrimitiveType::U64), self.span(expr));

        elem
      }

      hir::Expr::Field(lhs, _) => {
        let lhs = self.type_expr(lhs);

        // TODO

        lhs
      }

      hir::Expr::If { cond, then, els } => {
        let cond_ty = self.type_expr(cond);

        self.constrain(&cond_ty, &VType::Primitive(hir::PrimitiveType::Bool), self.span(cond));

        let then_ty = self.type_expr(then);
        if let Some(els) = els {
          let els_ty = self.type_expr(els);

          let res = self.fresh_var(self.span(expr), "if statment foo".to_string());
          let res = VType::Var(res);

          self.constrain(&then_ty, &res, self.span(then));
          self.constrain(&els_ty, &res, self.span(then));

          res
        } else {
          then_ty
        }
      }

      hir::Expr::StructInit(ref path, ref fields) => {
        let strct =
          self.env.structs.get(path).unwrap_or_else(|| panic!("no struct at path {path:?}"));

        for &(ref k, v) in fields {
          let ty = self.type_expr(v);
          let Some(field) = strct.iter().find(|(n, _)| n == k) else {
            emit!(self.span(v) => "field {k} not found in struct {path}");
            continue;
          };

          self.constrain(&ty, &VType::from(field.1.clone()), self.span(v));
        }

        VType::Struct(path.clone())
      }

      ref v => unimplemented!("type_expr {v:?}"),
    };

    self.exprs.insert(expr, ty.clone());
    ty
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
