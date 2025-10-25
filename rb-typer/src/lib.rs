use std::collections::HashMap;

use la_arena::Arena;
use rb_diagnostic::{emit, Span};
use rb_hir::{
  ast::{self as hir, ExprId, StmtId},
  SpanMap,
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
  span_map: &'a SpanMap,

  // Outputs of the typer: a map of expressions to their rendered types.
  exprs: HashMap<ExprId, VType>,

  // Type variables.
  variables: Arena<TypeVar>,

  // Variables in the current block.
  //
  // TODO: This is probably wrong on a few levels, need a wrapper struct for typing each block.
  local_functions: HashMap<String, Type>,
  locals:          HashMap<String, VType>,
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
  fn new(env: &'a Environment, function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
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
  pub fn check(env: &'a Environment, function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
    let mut typer = Typer::new(env, function, span_map);

    for (arg, ty) in &function.args {
      let ty = type_of_type_expr(ty);

      typer.locals.insert(arg.clone(), ty.into());
    }

    for &item in function.body.iter().flatten() {
      match function.stmts[item] {
        hir::Stmt::FunctionDef(ref func) => {
          let args = func.args.iter().map(|(_, ty)| type_of_type_expr(ty)).collect();
          let ret = match func.ret {
            Some(ref ty) => Box::new(type_of_type_expr(&ty)),
            None => Box::new(Type::unit()),
          };

          let ty = Type::Function(args, ret);
          typer.local_functions.insert(func.name.clone(), ty);
        }
        _ => {}
      }
    }

    for &item in function.body.iter().flatten() {
      typer.type_stmt(item);
    }

    typer
  }

  pub fn type_of_expr(&self, expr: ExprId) -> Type { self.lower_type(&self.exprs[&expr]) }

  fn lower_type(&self, ty: &VType) -> Type {
    match ty {
      VType::Primitive(lit) => Type::Primitive(*lit),
      VType::Integer => Type::Primitive(hir::PrimitiveType::I64),
      VType::Array(ty) => Type::Array(Box::new(self.lower_type(ty))),
      VType::Tuple(tys) => Type::Tuple(tys.iter().map(|t| self.lower_type(t)).collect()),
      VType::Function(args, ret) => Type::Function(
        args.iter().map(|t| self.lower_type(t)).collect(),
        Box::new(self.lower_type(ret)),
      ),

      // TODO: Render type variables correctly.
      VType::Var(v) => {
        let var = &self.variables[*v];

        if var.values.is_empty() {
          Type::unit()
        } else if var.values.len() == 1 {
          self.lower_type(&var.values.iter().next().unwrap())
        } else {
          let mut types = vec![];
          for ty in &var.values {
            types.push(self.lower_type(ty));
          }
          // TODO: Need to sort types.
          // types.sort_unstable();
          Type::Union(types)
        }
      }

      VType::Union(tys) => Type::Union(tys.iter().map(|ty| self.lower_type(ty)).collect()),

      VType::Struct(path) => Type::Struct(path.clone()),
    }
  }

  fn span(&self, expr: ExprId) -> Span { self.span_map.exprs[expr.into_raw().into_u32() as usize] }

  fn type_stmt(&mut self, stmt: StmtId) {
    match self.function.stmts[stmt] {
      hir::Stmt::Expr(expr) => {
        self.type_expr(expr);
      }
      hir::Stmt::Let(ref name, expr) => {
        let res = self.type_expr(expr);
        self.locals.insert(name.clone(), res);
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
        hir::Literal::Int(_) => VType::Integer,
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
        let v = self.fresh_var(self.span(expr), format!("array element"));

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

      hir::Expr::Name(ref name) => match self.locals.get(name) {
        Some(ty) => ty.clone(),
        None => match self.local_functions.get(name) {
          Some(ty) => ty.clone().into(),
          None => match self.env.names.get(name) {
            Some(ty) => VType::from(ty.clone()),
            None => {
              emit!(self.span(expr) => "undeclared name {name:?}");

              VType::Var(self.fresh_var(self.span(expr), format!("")))
            }
          },
        },
      },

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
              &VType::Function(vec![VType::Integer, VType::Integer], Box::new(VType::Integer)),
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

        let elem = VType::Var(self.fresh_var(self.span(expr), format!("array element")));

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

          let res = self.fresh_var(self.span(expr), format!("if statment foo"));
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
