use std::collections::HashMap;

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

    let values = var.values.keys().collect::<Vec<_>>();
    let uses = var.uses.keys().collect::<Vec<_>>();

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
          let ty = type_of_type_expr(te);
          self.constrain(&res, &VType::from(ty), self.span(expr));
        }
        self.locals.insert(id.unwrap(), res);
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

      hir::Expr::Call(lhs_expr, ref args) => {
        let lhs = self.type_expr(lhs_expr);

        let ret =
          VType::Var(self.fresh_var(self.span(expr), format!("return type of calling {:?}", lhs)));

        let call_type = VType::Function(
          args.iter().map(|&arg| self.type_expr(arg)).collect(),
          Box::new(ret.clone()),
        );

        self.constrain(&lhs, &call_type, self.span(lhs_expr));

        ret
      }

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

        let ret =
          VType::Var(self.fresh_var(self.span(expr), format!("return type of binary op {op:?}")));

        let call_type = VType::Function(vec![lhs, rhs], Box::new(ret.clone()));

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
            self.constrain(
              &VType::Function(
                vec![hir::PrimitiveType::I64.into(), hir::PrimitiveType::I64.into()],
                Box::new(hir::PrimitiveType::I64.into()),
              ),
              &call_type,
              self.span(expr),
            );
          }

          hir::BinaryOp::Eq | hir::BinaryOp::Neq => {
            let arg = VType::Var(self.fresh_var(self.span(expr), format!("arg for {op:?}")));

            self.constrain(
              &VType::Function(vec![arg.clone(), arg], Box::new(hir::PrimitiveType::Bool.into())),
              &call_type,
              self.span(expr),
            );
          }

          hir::BinaryOp::Lt | hir::BinaryOp::Lte | hir::BinaryOp::Gt | hir::BinaryOp::Gte => {
            self.constrain(
              &VType::Function(
                vec![VType::Integer, VType::Integer],
                Box::new(hir::PrimitiveType::Bool.into()),
              ),
              &call_type,
              self.span(expr),
            );
          }

          _ => unimplemented!("binary op {op:?}"),
        }

        ret
      }

      hir::Expr::Index(lhs, rhs) => {
        let lhs = self.type_expr(lhs);
        let rhs = self.type_expr(rhs);

        let elem = VType::Var(self.fresh_var(self.span(expr), "array element".to_string()));

        self.constrain(&lhs, &VType::Array(Box::new(elem.clone())), self.span(expr));
        self.constrain(&rhs, &VType::Primitive(hir::PrimitiveType::U64), self.span(expr));

        elem
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
}
