mod ty;

use rb_diagnostic::{emit, Span};
use rb_hir::{
  ast::{self as hir, ExprId, StmtId},
  SpanMap,
};
pub use ty::Type;

/// A typechecker for a function body.
///
/// A new Typer should be constructed for every region that has inferred types.
/// So, function bodies each get a typer, as they have explicit signatures.
pub struct Typer<'a> {
  function: &'a hir::Function,
  span_map: &'a SpanMap,
}

impl<'a> Typer<'a> {
  fn new(function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
    Typer { function, span_map }
  }

  /// Typecheck a function body.
  pub fn check(function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
    let mut typer = Typer::new(function, span_map);

    for &item in function.items.iter() {
      typer.type_stmt(item);
    }

    typer
  }

  fn span(&self, expr: ExprId) -> Span { self.span_map.exprs[expr.into_raw().into_u32() as usize] }

  fn type_stmt(&mut self, stmt: StmtId) {
    match self.function.stmts[stmt] {
      hir::Stmt::Expr(expr) => self.type_expr(expr),
    };
  }

  fn type_expr(&mut self, expr: ExprId) -> Type {
    match self.function.exprs[expr] {
      hir::Expr::Literal(ref lit) => match lit {
        hir::Literal::Int(_) => Type::Int,
        hir::Literal::Bool(_) => Type::Bool,
        hir::Literal::Unit => Type::Bool,
      },

      hir::Expr::Call(lhs_expr, ref args) => {
        let lhs = self.type_expr(lhs_expr);

        match lhs {
          Type::Function(sig_args, sig_ret) => {
            if sig_args.len() != args.len() {
              emit!(
                format!("expected {} arguments, found {}", sig_args.len(), args.len()),
                self.span(expr)
              );
            }

            for (&arg, sig) in args.iter().zip(sig_args.into_iter()) {
              let ty = self.type_expr(arg);
              self.constrain(&ty, &sig, self.span(arg));
            }

            *sig_ret
          }

          _ => {
            emit!(format!("expected function, found {:?}", lhs), self.span(lhs_expr));
            Type::Unit
          }
        }
      }

      hir::Expr::Name(_) => Type::Function(vec![Type::Int], Box::new(Type::Unit)),

      hir::Expr::BinaryOp(lhs_expr, ref _op, rhs_expr) => {
        let lhs = self.type_expr(lhs_expr);
        let rhs = self.type_expr(rhs_expr);

        self.constrain(&lhs, &Type::Union(vec![Type::Int, Type::Bool]), self.span(lhs_expr));
        self.constrain(&rhs, &Type::Union(vec![Type::Int, Type::Bool]), self.span(rhs_expr));

        lhs
      }

      _ => Type::Unit,
    }
  }
}

enum TypeError<'a> {
  NotSubtype(&'a Type, &'a Type),
  Union(Vec<TypeError<'a>>),
}

impl Typer<'_> {
  fn constrain<'a>(&self, v: &Type, u: &Type, span: Span) {
    fn render_err(e: &TypeError) -> String {
      match e {
        TypeError::NotSubtype(v, u) => format!("{v:?} is not a subtype of {u:?}"),
        TypeError::Union(errors) => {
          let mut buf = String::new();

          for error in errors {
            buf.push_str(&render_err(error));
            buf.push('\n');
          }

          buf
        }
      }
    }

    match self.constrain0(v, u, span) {
      Ok(()) => {}
      Err(e) => emit!(render_err(&e), span),
    }
  }

  fn constrain0<'a>(&self, v: &'a Type, u: &'a Type, span: Span) -> Result<(), TypeError<'a>> {
    if v == u {
      return Ok(());
    }

    match (v, u) {
      (v, Type::Union(us)) => {
        let mut results = vec![];

        for u in us {
          results.push(self.constrain0(v, u, span));
        }

        if results.iter().any(Result::is_ok) {
          Ok(())
        } else {
          Err(TypeError::Union(results.into_iter().map(Result::unwrap_err).collect()))
        }
      }

      // (v, Type::Inter(us)) => {
      //   for u in us {
      //     self.constrain(v, u, span);
      //   }
      // }
      (v, u) => Err(TypeError::NotSubtype(v, u)),
    }
  }
}
