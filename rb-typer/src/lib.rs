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
  locals: HashMap<String, VType>,
}

impl<'a> Typer<'a> {
  fn new(env: &'a Environment, function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
    Typer {
      env,
      function,
      span_map,
      exprs: HashMap::new(),
      variables: Arena::new(),
      locals: HashMap::new(),
    }
  }

  /// Typecheck a function body.
  pub fn check(env: &'a Environment, function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
    let mut typer = Typer::new(env, function, span_map);

    for &item in function.items.iter() {
      typer.type_stmt(item);
    }

    typer
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

        assert!(var.values.len() == 1, "variable {var:?} has multiple values");
        self.lower_type(&var.values[0])
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
    }
  }

  fn fresh_var(&mut self, span: Span, description: String) -> VarId {
    let var = TypeVar::new(span, description);
    self.variables.alloc(var)
  }

  fn type_expr(&mut self, expr: ExprId) -> VType {
    let ty = match self.function.exprs[expr] {
      hir::Expr::Literal(ref lit) => match lit {
        hir::Literal::Int(_) => VType::Literal(ty::Literal::Int),
        hir::Literal::Bool(_) => VType::Literal(ty::Literal::Bool),
        hir::Literal::Unit => VType::Literal(ty::Literal::Unit),
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
        None => match self.env.names.get(name) {
          Some(ty) => VType::from(ty.clone()),
          None => {
            emit!(format!("undeclared name {name:?}"), self.span(expr));

            VType::Var(self.fresh_var(self.span(expr), format!("")))
          }
        },
      },

      hir::Expr::BinaryOp(lhs_expr, ref op, rhs_expr) => {
        let lhs = self.type_expr(lhs_expr);
        let rhs = self.type_expr(rhs_expr);

        let ret =
          VType::Var(self.fresh_var(self.span(expr), format!("return type of binary op {op:?}")));

        let call_type = VType::Function(vec![lhs, rhs], Box::new(ret.clone()));

        self.constrain(
          &VType::Function(
            vec![ty::Literal::Int.into(), ty::Literal::Int.into()],
            Box::new(ty::Literal::Int.into()),
          ),
          &call_type,
          self.span(expr),
        );

        ret
      }

      _ => ty::Literal::Unit.into(),
    };

    self.exprs.insert(expr, ty.clone());
    ty
  }
}
