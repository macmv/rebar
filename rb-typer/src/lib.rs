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
#[derive(Clone)]
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

      hir::Expr::BinaryOp(lhs_expr, ref op, rhs_expr) => {
        let lhs = self.type_expr(lhs_expr);
        let rhs = self.type_expr(rhs_expr);

        let ret = Type::Var(self.fresh_var());

        let call_type = Type::Function(vec![lhs, rhs], Box::new(ret.clone()));

        match op {
          hir::BinaryOp::Mul => {
            self.constrain(
              &Type::Function(vec![Type::Int, Type::Int], Box::new(Type::Bool)),
              &call_type,
              self.span(expr),
            );
          }
          _ => {
            self.constrain(
              &Type::Function(vec![Type::Bool, Type::Bool], Box::new(Type::Bool)),
              &call_type,
              self.span(expr),
            );
          }
        }

        ret
      }

      _ => Type::Unit,
    }
  }
}

enum TypeError {
  NotSubtype(Type, Type),
  Union(Vec<TypeError>),
  UnresolvedUnion(Type, Type, Vec<TypeError>),
}

struct Constrain<'a: 'b, 'b> {
  typer:  &'b mut Typer<'a>,
  errors: Vec<TypeError>,
}

impl Typer<'_> {
  fn constrain<'a>(&mut self, v: &Type, u: &Type, span: Span) {
    let mut constrain = Constrain { typer: self, errors: vec![] };

    fn render_err(e: &TypeError) -> String {
      match e {
        TypeError::NotSubtype(v, u) => format!("{v:?} is not a subtype of {u:?}"),
        TypeError::UnresolvedUnion(v, u, errors) => {
          let mut buf = String::new();
          buf += &format!("could not resolve union, {v:?} is not a subtype of {u:?}");

          for error in errors {
            buf.push_str(&render_err(error));
            buf.push('\n');
          }

          buf
        }
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
    constrain.constrain(v, u, span);

    for e in constrain.errors {
      emit!(render_err(&e), span);
    }
  }
}

impl Constrain<'_, '_> {
  fn constrain(&mut self, v: &Type, u: &Type, span: Span) {
    if v == u {
      return;
    }

    match (v, u) {
      (Type::Var(v), u) => {
        let vvar = &mut self.typer.variables[*v];
        vvar.uses.push(u.clone());
        for v0 in vvar.values.clone() {
          self.constrain(&v0, u, span);
        }
      }
      (v, Type::Var(u)) => {
        let uvar = &mut self.typer.variables[*u];
        uvar.values.push(v.clone());
        for u0 in uvar.uses.clone() {
          self.constrain(v, &u0, span);
        }
      }

      (Type::Union(vs), u) => {
        for v in vs {
          self.constrain(v, u, span);
        }
      }

      // This is our solution to overloads: try all the paths in a `try_constrain` check, which is
      // similar to constrain, but doesn't actually mutate any type variables. `try_constrain` is
      // best-effort, and may fail to unify certain constraints.
      (v, Type::Union(us)) => {
        let mut results = vec![];

        for u in us {
          results.push(self.try_constrain(v, u, span));
        }

        if results.iter().any(Result::is_ok) {
          for (result, u) in results.iter().zip(us.iter()) {
            if result.is_ok() {
              self.constrain(v, u, span);
            }
          }
        } else {
          // All constraints failed, produce an error.
          self.errors.push(TypeError::Union(results.into_iter().map(Result::unwrap_err).collect()))
        }
      }

      (Type::Function(va, vr), Type::Function(ua, ur)) => {
        if va.len() != ua.len() {
          self.errors.push(TypeError::NotSubtype(v.clone(), u.clone()));
        }

        for (v, u) in va.iter().zip(ua.iter()) {
          self.constrain(u, v, span);
        }
        self.constrain(vr, ur, span);
      }

      (v, u) => self.errors.push(TypeError::NotSubtype(v.clone(), u.clone())),
    }
  }

  fn try_constrain(&self, v: &Type, u: &Type, span: Span) -> Result<(), TypeError> {
    if v == u {
      return Ok(());
    }

    let mut tmp = Constrain { typer: &mut self.typer.clone(), errors: vec![] };
    tmp.constrain(v, u, span);
    if tmp.errors.is_empty() {
      Ok(())
    } else {
      Err(TypeError::UnresolvedUnion(v.clone(), u.clone(), tmp.errors))
    }
  }
}
