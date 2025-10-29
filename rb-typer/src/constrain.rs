use rb_diagnostic::{Span, emit};
use rb_hir::ast as hir;

use crate::{Typer, ty::VType};

enum TypeError {
  NotSubtype(VType, VType),
  Union(Vec<TypeError>),
  UnresolvedUnion(VType, VType, Vec<(TypeError, Vec<(String, Option<Span>)>)>),
}

struct Constrain<'a: 'b, 'b> {
  typer:  &'b mut Typer<'a>,
  errors: Vec<(TypeError, Vec<(String, Option<Span>)>)>,

  ctx: Vec<(String, Option<Span>)>,
}

impl Typer<'_> {
  pub(crate) fn constrain(&mut self, v: &VType, u: &VType, span: Span) {
    let mut constrain = Constrain { typer: self, errors: vec![], ctx: vec![] };

    fn render_err(e: &TypeError, ctx: &[(String, Option<Span>)]) -> String {
      let mut buf = String::new();

      match e {
        TypeError::NotSubtype(v, u) => {
          buf.push_str(&format!("{v:?} is not a subtype of {u:?}"));
          buf.push('\n');
        }
        TypeError::UnresolvedUnion(v, u, errors) => {
          buf.push_str(&format!("could not resolve union, {v:?} is not a subtype of {u:?}"));
          buf.push('\n');

          for (error, ctx) in errors {
            buf.push_str(&render_err(error, ctx));
            buf.push('\n');
          }
        }
        TypeError::Union(errors) => {
          for error in errors {
            buf.push_str(&render_err(error, &[]));
            buf.push('\n');
          }
        }
      }

      for (desc, _) in ctx {
        buf.push_str(desc);
        buf.push('\n');
      }

      buf
    }
    constrain.constrain(v, u, span);

    for (e, ctx) in constrain.errors {
      for (ctx, span) in &ctx {
        if let Some(sp) = span {
          emit!(*sp => "{ctx:?}");
        }
      }
      emit!(span => render_err(&e, &ctx));
    }
  }
}

impl Constrain<'_, '_> {
  fn ctx(&mut self, ctx: String, span: Option<Span>, f: impl FnOnce(&mut Self)) {
    self.ctx.push((ctx, span));
    f(self);
    self.ctx.pop();
  }

  fn error(&mut self, error: TypeError) { self.errors.push((error, self.ctx.clone())); }

  fn constrain(&mut self, v: &VType, u: &VType, span: Span) {
    if v == u {
      return;
    }

    match (v, u) {
      (VType::Var(v), u) => {
        let desc = &self.typer.variables[*v].description;
        let sp = self.typer.variables[*v].span;
        self.ctx(format!("constraining {desc} to {u:?}"), Some(sp), |c| {
          let vvar = &mut c.typer.variables[*v];
          if vvar.uses.insert(u.clone()) {
            for v0 in vvar.values.clone() {
              c.constrain(&v0, u, span);
            }
          }
        });
      }
      (v, VType::Var(u)) => {
        let desc = &self.typer.variables[*u].description;
        let sp = self.typer.variables[*u].span;
        self.ctx(format!("constraining {v:?} to {desc}"), Some(sp), |c| {
          let uvar = &mut c.typer.variables[*u];
          if uvar.values.insert(v.clone()) {
            for u0 in uvar.uses.clone() {
              c.constrain(v, &u0, span);
            }
          }
        });
      }

      (VType::Union(vs), u) => {
        self.ctx(format!("constraining {v:?} to {u:?}"), None, |c| {
          for v in vs {
            c.constrain(v, u, span);
          }
        });
      }

      // This is our solution to overloads: try all the paths in a `try_constrain` check, which is
      // similar to constrain, but doesn't actually mutate any type variables. `try_constrain` is
      // best-effort, and may fail to unify certain constraints.
      (v, VType::Union(us)) => {
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
          self.error(TypeError::Union(results.into_iter().map(Result::unwrap_err).collect()))
        }
      }

      (VType::Array(v), VType::Array(u)) => {
        self.ctx(format!("constraining {v:?} to {u:?}"), None, |c| {
          c.constrain(v, u, span);
        });
      }

      (VType::Function(va, vr), VType::Function(ua, ur)) => {
        if va.len() != ua.len() {
          self.error(TypeError::NotSubtype(v.clone(), u.clone()));
        }

        self.ctx(format!("constraining {v:?} to {u:?}"), None, |c| {
          for (v, u) in va.iter().zip(ua.iter()) {
            c.constrain(u, v, span);
          }
          c.constrain(vr, ur, span);
        });
      }

      (VType::Integer, VType::Primitive(hir::PrimitiveType::I64)) => {}

      (v, u) => self.error(TypeError::NotSubtype(v.clone(), u.clone())),
    }
  }

  fn try_constrain(&self, v: &VType, u: &VType, span: Span) -> Result<(), TypeError> {
    if v == u {
      return Ok(());
    }

    let mut tmp =
      Constrain { typer: &mut self.typer.clone(), errors: vec![], ctx: self.ctx.clone() };
    tmp.constrain(v, u, span);
    if tmp.errors.is_empty() {
      Ok(())
    } else {
      Err(TypeError::UnresolvedUnion(v.clone(), u.clone(), tmp.errors))
    }
  }
}

#[cfg(test)]
mod tests {
  use rb_test::{Expect, expect};

  use crate::Environment;

  fn check(body: &str, expected: Expect) {
    let (body, span_map) = rb_hir_lower::parse_body(body);
    let env = Environment::empty();
    let typer = crate::Typer::check(&env, &body, &span_map);

    let mut out = String::new();
    for (id, local) in body.locals.iter() {
      let ty = typer.type_of_local(id);
      out.push_str(&format!("{}: {}\n", local.name, ty));
    }
    expected.assert_eq(&out);
  }

  #[test]
  fn it_works() {
    check(
      "
      let a = 1 + 2
      let b = 3
      ",
      expect![@r#"
        a: i64
        b: i64
      "#],
    );
  }
}
