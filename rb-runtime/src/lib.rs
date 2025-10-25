use std::sync::Arc;

use rb_diagnostic::{emit, Diagnostic, Source, SourceId, Sources, Span};
use rb_syntax::cst;

pub use rb_std::Environment;

const NUM_CPUS: usize = 32;

pub struct RuntimeEnvironment {
  pub env: Environment,
}

pub fn eval(src: &str) {
  let env = RuntimeEnvironment::new(Environment::std());

  let mut sources = Sources::new();
  let id = sources.add(Source::new("inline.rbr".into(), src.into()));
  let sources = Arc::new(sources);

  rb_diagnostic::run_or_exit(sources.clone(), || compile_diagnostics(env, sources, id))
    .expect("error with no diagnostics emitted");
}

pub fn run(
  env: RuntimeEnvironment,
  sources: Arc<Sources>,
  id: SourceId,
) -> Result<(), Vec<Diagnostic>> {
  rb_diagnostic::run(sources.clone(), || compile_diagnostics(env, sources, id)).map(|_| ())
}

fn compile_diagnostics(
  mut env: RuntimeEnvironment,
  sources: Arc<Sources>,
  id: SourceId,
) -> Result<(), ()> {
  let src = sources.get(id);

  let res = cst::SourceFile::parse(&src.source);

  let (hir, span_map, _) = if res.errors().is_empty() {
    rb_hir_lower::lower_source(res.tree(), id)
  } else {
    for error in res.errors() {
      emit!(Span { file: id, range: error.span() } => error.message());
    }

    return Err(());
  };

  rb_diagnostic::check()?;

  // TODO: This is where we join all the threads, collect all the functions up,
  // and then split out to a thread pool to typecheck and lower each function.
  let mut functions = vec![];

  let (typer_env, mir_env) = env.build(&hir, &span_map);

  rb_diagnostic::check()?;

  for (id, function) in hir.functions {
    let span_map = &span_map.functions[&id];

    let typer = rb_typer::Typer::check(&typer_env, &function, &span_map);
    if rb_diagnostic::is_ok() {
      if let Some(mut func) = rb_mir_lower::lower_function(&mir_env, &typer, &function) {
        func.id = rb_mir::ast::UserFunctionId(id.into_raw().into_u32() as u64);

        functions.push(func);
      }
    }
  }

  rb_diagnostic::check()?;

  // If we get to this point, all checks have passed, and we can compile to
  // cranelift IR. Collect all the functions, split them into chunks, and compile
  // them on a thread pool.

  compile_mir(env, functions);

  Ok(())
}

fn compile_mir(env: RuntimeEnvironment, functions: Vec<rb_mir::ast::Function>) {
  let mut compiler = rb_backend::Compiler::new(env.env.mir_ctx.clone());

  for func in &functions {
    compiler.declare_function(func);
  }

  let compiled =
    run_parallel(&functions, || compiler.new_thread(), |ctx, f| ctx.compile_function(f));

  for func in compiled.into_iter() {
    compiler.finish_function(func);
  }

  compiler.finish();
}

impl RuntimeEnvironment {
  pub fn new(env: Environment) -> Self { RuntimeEnvironment { env } }

  fn build(
    &mut self,
    hir: &rb_hir::ast::SourceFile,
    spans: &rb_hir::SpanMap,
  ) -> (rb_typer::Environment, rb_mir_lower::Env<'_>) {
    let mut typer_env = self.env.typer_env();

    for (id, s) in hir.structs.values().enumerate() {
      let id = rb_mir::ast::StructId(id as u64);

      typer_env.structs.insert(
        s.name.clone(),
        s.fields.iter().map(|(name, te)| (name.clone(), rb_typer::type_of_type_expr(te))).collect(),
      );
      self.env.mir_ctx.struct_paths.insert(s.name.clone(), id);
      self.env.mir_ctx.structs.insert(
        id,
        rb_mir::Struct {
          fields: s
            .fields
            .iter()
            .map(|(name, te)| (name.clone(), rb_typer::type_of_type_expr(te)))
            .collect(),
        },
      );
    }

    let mut mir_env = self.mir_env();
    for (id, f) in hir.functions.iter() {
      mir_env.declare_user_function(id.into_raw().into_u32() as u64, f, &spans.functions[&id]);
    }

    (typer_env, mir_env)
  }

  fn mir_env(&self) -> rb_mir_lower::Env<'_> {
    rb_mir_lower::Env {
      ctx:   &self.env.mir_ctx,
      items: self
        .env
        .ids
        .iter()
        .enumerate()
        .map(|(k, v)| {
          (v.clone(), rb_mir_lower::Item::NativeFunction(rb_mir::ast::NativeFunctionId(k as u64)))
        })
        .collect(),
    }
  }
}

pub fn run_parallel<I: Send + Sync, C: Send, O: Send + Sync>(
  input: &[I],
  mut ctx: impl (FnMut() -> C) + Copy,
  mut f: impl (FnMut(&mut C, &I) -> O) + Copy + Send,
) -> Vec<O> {
  if input.len() < NUM_CPUS {
    let mut out = Vec::with_capacity(input.len());
    let mut ctx = ctx();

    for i in input {
      out.push(f(&mut ctx, i));
    }

    return out;
  };

  let chunk_size = (input.len() / NUM_CPUS).max(1);

  let mut results = vec![];
  for _ in 0..NUM_CPUS {
    results.push(Vec::with_capacity(chunk_size));
  }

  std::thread::scope(|scope| {
    for (chunk, out) in input.chunks(chunk_size).zip(results.iter_mut()) {
      let mut ctx = ctx();

      scope.spawn(move || {
        for i in chunk {
          out.push(f(&mut ctx, i));
        }
      });
    }
  });

  results.into_iter().flatten().collect()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  #[ignore] // TODO: Add `assert_eq`
  fn foo() {
    eval(
      r#"
        assert_eq(2 * 3 + 4 + 5, 15)
        4
      "#,
    );
  }
}
