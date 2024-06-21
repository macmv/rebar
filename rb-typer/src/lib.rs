mod ty;

use la_arena::Arena;
use rb_diagnostic::{emit, Span};
use rb_hir::{
  ast::{self as hir, ExprId, StmtId},
  SpanMap,
};
pub use ty::Type;
use ty::{TypeVar, VarId};

/// A typechecker for a function body.
///
/// A new Typer should be constructed for every region that has inferred types.
/// So, function bodies each get a typer, as they have explicit signatures.
pub struct Typer<'a> {
  function: &'a hir::Function,
  span_map: &'a SpanMap,

  // Type variables.
  variables: Arena<TypeVar>,
}

impl<'a> Typer<'a> {
  fn new(function: &'a hir::Function, span_map: &'a SpanMap) -> Self {
    Typer { function, span_map, variables: Arena::new() }
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

  fn fresh_var(&mut self) -> VarId {
    let var = TypeVar::new();
    self.variables.alloc(var)
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

        let ret = Type::Var(self.fresh_var());

        let call_type = Type::Function(
          args.iter().map(|&arg| self.type_expr(arg)).collect(),
          Box::new(ret.clone()),
        );

        self.constrain(&lhs, &call_type, self.span(lhs_expr));

        ret
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
  fn constrain<'a>(&mut self, v: &Type, u: &Type, span: Span) {
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

  fn constrain0<'a>(&mut self, v: &'a Type, u: &'a Type, span: Span) -> Result<(), TypeError<'a>> {
    if v == u {
      return Ok(());
    }

    match (v, u) {
      (Type::Var(v), u) => {
        self.variables[*v].constraints.push(u.clone());
        Ok(())
      }
      (v, Type::Var(u)) => {
        self.variables[*u].constraints.push(v.clone());
        Ok(())
      }

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

      (Type::Function(va, vr), Type::Function(ua, ur)) => {
        if va.len() != ua.len() {
          return Err(TypeError::NotSubtype(v, u));
        }

        for (v, u) in va.iter().zip(ua.iter()) {
          self.constrain0(v, u, span)?;
        }
        self.constrain0(vr, ur, span)?;

        Ok(())
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
