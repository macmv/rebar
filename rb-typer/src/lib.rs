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

pub use ty::{Environment, Literal, Type};

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
      let ty = typer.type_of_type_expr(ty);

      typer.locals.insert(arg.clone(), ty.into());
    }

    for &item in function.items.iter() {
      match function.stmts[item] {
        hir::Stmt::Def(ref name, ref args, ref ret) => {
          let args = args.iter().map(|(_, ty)| typer.type_of_type_expr(ty)).collect();
          let ret = match ret {
            Some(ty) => Box::new(typer.type_of_type_expr(ty)),
            None => Box::new(Type::Literal(Literal::Unit)),
          };

          let ty = Type::Function(args, ret);
          typer.local_functions.insert(name.clone(), ty);
        }
        _ => {}
      }
    }

    for &item in function.items.iter() {
      typer.type_stmt(item);
    }

    typer
  }

  pub fn type_of_type_expr(&self, te: &hir::TypeExpr) -> Type {
    match te {
      hir::TypeExpr::Nil => Type::Literal(Literal::Unit),
      hir::TypeExpr::Bool => Type::Literal(Literal::Bool),
      hir::TypeExpr::Int => Type::Literal(Literal::Int),
      hir::TypeExpr::Union(tys) => {
        Type::Union(tys.iter().map(|ty| self.type_of_type_expr(&ty)).collect())
      }
    }
  }

  pub fn type_of_expr(&self, expr: ExprId) -> Type { self.lower_type(&self.exprs[&expr]) }

  fn lower_type(&self, ty: &VType) -> Type {
    match ty {
      VType::Literal(lit) => Type::Literal(*lit),
      VType::Function(args, ret) => Type::Function(
        args.iter().map(|t| self.lower_type(t)).collect(),
        Box::new(self.lower_type(ret)),
      ),

      // TODO: Render type variables correctly.
      VType::Var(v) => {
        let var = &self.variables[*v];

        if var.values.is_empty() {
          Type::Literal(Literal::Unit)
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

      ref ty => panic!("invalid type: {ty:?}"),
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
      hir::Stmt::Def(_, _, _) => {}
    }
  }

  fn fresh_var(&mut self, span: Span, description: String) -> VarId {
    let var = TypeVar::new(span, description);
    self.variables.alloc(var)
  }

  fn type_expr(&mut self, expr: ExprId) -> VType {
    let ty = match self.function.exprs[expr] {
      hir::Expr::Literal(ref lit) => match lit {
        hir::Literal::Nil => VType::Literal(ty::Literal::Unit),
        hir::Literal::Bool(_) => VType::Literal(ty::Literal::Bool),
        hir::Literal::Int(_) => VType::Literal(ty::Literal::Int),
      },

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
              emit!(format!("undeclared name {name:?}"), self.span(expr));

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
            hir::Stmt::Let(_, _) | hir::Stmt::Def(_, _, _) => VType::Literal(ty::Literal::Unit),
          },
          None => VType::Literal(ty::Literal::Unit),
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
              &VType::Function(vec![ty::Literal::Int.into()], Box::new(ty::Literal::Int.into())),
              &call_type,
              self.span(expr),
            );
          }

          hir::UnaryOp::Not => {
            self.constrain(
              &VType::Function(vec![ty::Literal::Bool.into()], Box::new(ty::Literal::Bool.into())),
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
          | hir::BinaryOp::Mod => {
            self.constrain(
              &VType::Function(
                vec![ty::Literal::Int.into(), ty::Literal::Int.into()],
                Box::new(ty::Literal::Int.into()),
              ),
              &call_type,
              self.span(expr),
            );
          }

          hir::BinaryOp::Eq | hir::BinaryOp::Neq => {
            let arg = VType::Var(self.fresh_var(self.span(expr), format!("arg for {op:?}")));

            self.constrain(
              &VType::Function(vec![arg.clone(), arg], Box::new(ty::Literal::Bool.into())),
              &call_type,
              self.span(expr),
            );
          }

          hir::BinaryOp::Lt | hir::BinaryOp::Lte | hir::BinaryOp::Gt | hir::BinaryOp::Gte => {
            self.constrain(
              &VType::Function(
                vec![ty::Literal::Int.into(), ty::Literal::Int.into()],
                Box::new(ty::Literal::Bool.into()),
              ),
              &call_type,
              self.span(expr),
            );
          }

          _ => unimplemented!("binary op {op:?}"),
        }

        ret
      }

      hir::Expr::If { cond, then, els } => {
        let cond_ty = self.type_expr(cond);

        self.constrain(&cond_ty, &VType::Literal(ty::Literal::Bool), self.span(cond));

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

      ref v => unimplemented!("type_expr {v:?}"),
    };

    self.exprs.insert(expr, ty.clone());
    ty
  }
}
