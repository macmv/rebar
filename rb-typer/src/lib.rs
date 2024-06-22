use std::collections::HashMap;

use la_arena::Arena;
use rb_diagnostic::Span;
use rb_hir::{
  ast::{self as hir, ExprId, StmtId},
  SpanMap,
};
use ty::{TypeVar, VType, VarId};

mod constrain;
mod ty;

pub use ty::Type;

/// A typechecker for a function body.
///
/// A new Typer should be constructed for every region that has inferred types.
/// So, function bodies each get a typer, as they have explicit signatures.
#[derive(Clone)]
pub struct Typer<'a> {
  // Inputs to the typer: an HIR tree, and a map of spans for diagnostics.
  function: &'a hir::Function,
  span_map: &'a SpanMap,

  // Outputs of the typer: a map of expressions to their rendered types.
  exprs: HashMap<ExprId, VType>,

  // Type variables.
  variables: Arena<TypeVar>,
}

impl<'a> Typer<'a> {
  fn new(function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
    Typer { function, span_map, exprs: HashMap::new(), variables: Arena::new() }
  }

  /// Typecheck a function body.
  pub fn check(function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
    let mut typer = Typer::new(function, span_map);

    for &item in function.items.iter() {
      typer.type_stmt(item);
    }

    typer
  }

  pub fn type_of_expr(&self, expr: ExprId) -> Type {
    fn lower_type(ty: &VType) -> Type {
      match ty {
        VType::Literal(lit) => Type::Literal(lit.clone()),
        VType::Function(args, ret) => {
          Type::Function(args.iter().map(lower_type).collect(), Box::new(lower_type(ret)))
        }

        ref ty => panic!("invalid type: {ty:?}"),
      }
    }

    lower_type(&self.exprs[&expr])
  }

  fn span(&self, expr: ExprId) -> Span { self.span_map.exprs[expr.into_raw().into_u32() as usize] }

  fn type_stmt(&mut self, stmt: StmtId) {
    match self.function.stmts[stmt] {
      hir::Stmt::Expr(expr) => self.type_expr(expr),
    };
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

      hir::Expr::Name(_) => {
        VType::Function(vec![ty::Literal::Int.into()], Box::new(ty::Literal::Unit.into()))
      }

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
