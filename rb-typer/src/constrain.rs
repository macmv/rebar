use std::fmt;

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

    constrain.constrain(v, u, span);

    for (e, ctx) in constrain.errors {
      for (ctx, span) in &ctx {
        if let Some(sp) = span {
          emit!(*sp => "{ctx:?}");
        }
      }
      emit!(span => self.render_err(&e, &ctx));
    }
  }

  fn render_err(&self, e: &TypeError, ctx: &[(String, Option<Span>)]) -> String {
    let mut buf = String::new();

    match e {
      TypeError::NotSubtype(v, u) => {
        buf.push_str(&format!(
          "{} is not a subtype of {}",
          self.display_type(v),
          self.display_type(u)
        ));
        buf.push('\n');
      }
      TypeError::UnresolvedUnion(v, u, errors) => {
        buf.push_str(&format!("could not resolve union, {v:?} is not a subtype of {u:?}"));
        buf.push('\n');

        for (error, ctx) in errors {
          buf.push_str(&self.render_err(error, ctx));
          buf.push('\n');
        }
      }
      TypeError::Union(errors) => {
        for error in errors {
          buf.push_str(&self.render_err(error, &[]));
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

  pub(crate) fn display_type<'a>(&'a self, ty: &'a VType) -> VTypeDisplay<'a> {
    VTypeDisplay { typer: self, vtype: ty }
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
          if vvar.uses.insert(u.clone(), span).is_none() {
            for v0 in vvar.values.clone().keys() {
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
          if uvar.values.insert(v.clone(), span).is_none() {
            for u0 in uvar.uses.clone().keys() {
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

      (VType::Integer, VType::Primitive(hir::PrimitiveType::I8)) => {}
      (VType::Integer, VType::Primitive(hir::PrimitiveType::I16)) => {}
      (VType::Integer, VType::Primitive(hir::PrimitiveType::I32)) => {}
      (VType::Integer, VType::Primitive(hir::PrimitiveType::I64)) => {}
      (VType::Integer, VType::Primitive(hir::PrimitiveType::U8)) => {}
      (VType::Integer, VType::Primitive(hir::PrimitiveType::U16)) => {}
      (VType::Integer, VType::Primitive(hir::PrimitiveType::U32)) => {}
      (VType::Integer, VType::Primitive(hir::PrimitiveType::U64)) => {}

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

pub(crate) struct VTypeDisplay<'a> {
  typer: &'a Typer<'a>,
  vtype: &'a VType,
}

impl fmt::Display for VTypeDisplay<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.vtype {
      VType::Primitive(lit) => write!(f, "{lit}"),
      VType::Integer => write!(f, "integer"),
      VType::Array(ty) => {
        write!(f, "array<")?;
        write!(f, "{}", self.typer.display_type(ty))?;
        write!(f, ">")
      }
      VType::Tuple(tys) => {
        write!(f, "(")?;
        for (i, ty) in tys.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", self.typer.display_type(ty))?;
        }
        write!(f, ")")
      }

      VType::Function(args, ret) => {
        write!(f, "fn(")?;
        for (i, ty) in args.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", self.typer.display_type(ty))?;
        }
        write!(f, ") -> {}", self.typer.display_type(ret))
      }

      // TODO: Render type variables correctly.
      VType::Var(v) => {
        let var = &self.typer.variables[*v];

        if var.values.is_empty() {
          write!(f, "()")
        } else if var.values.len() == 1 {
          write!(f, "{}", self.typer.display_type(var.values.keys().next().unwrap()))
        } else {
          let mut types = vec![];
          for ty in var.values.keys() {
            types.push(self.typer.display_type(ty));
          }
          // TODO: Need to sort types.
          // types.sort_unstable();

          for (i, t) in types.iter().enumerate() {
            if i != 0 {
              write!(f, " | ")?;
            }
            write!(f, "{}", t)?;
          }
          Ok(())
        }
      }

      VType::Union(tys) => {
        for (i, t) in tys.iter().enumerate() {
          if i != 0 {
            write!(f, " | ")?;
          }
          write!(f, "{}", self.typer.display_type(t))?;
        }
        Ok(())
      }

      VType::Struct(path) => write!(f, "{path}"),
    }
  }
}

#[cfg(test)]
mod tests {
  use rb_test::{Expect, expect};
  use std::fmt::Write;

  use crate::Environment;

  fn check(body: &str, expected: Expect) {
    let (sources, body, span_map) = rb_hir_lower::parse_body(body);
    let mut out = String::new();
    let res = rb_diagnostic::run(sources.clone(), || {
      let env = Environment::empty();
      let typer = crate::Typer::check(&env, &body, &span_map);

      for (id, local) in body.locals.iter() {
        let ty = typer.type_of_local(id);
        writeln!(out, "{}: {}", local.name, ty).unwrap();
      }
    });

    match res {
      Ok(()) => expected.assert_eq(&out),
      Err(e) => {
        let mut out = String::new();
        for e in e {
          write!(out, "{}", e.render(&sources)).unwrap();
        }
        expected.assert_eq(&out);
      }
    }
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

  #[test]
  fn let_types() {
    check(
      "
      let a: i32 = 3
      let b = a
      ",
      expect![@r#"
        a: i32
        b: i32
      "#],
    );

    check(
      "
      let a: i32 = 3
      let b: i8 = a
      ",
      expect![@r#"
        error: cannot unify types i32 and i8
         --> inline.rbr:2:20
          |
        2 |       let a: i32 = 3
          |                    ^
        error: cannot unify types i32 and i8
         --> inline.rbr:2:20
          |
        2 |       let a: i32 = 3
          |                    ^
      "#],
    );
  }
}
