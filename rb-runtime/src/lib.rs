use std::sync::Arc;

mod gc;
mod gc_value;
mod intrinsics;
mod owned_arg_parser;

pub use gc_value::{GcArray, GcValue};

use gc::GcArena;
use rb_diagnostic::{emit, Diagnostic, Source, SourceId, Sources, Span};
use rb_syntax::cst;

pub use rb_std::Environment;

const NUM_CPUS: usize = 32;

pub struct RuntimeEnvironment {
  pub env: Environment,

  gc: GcArena,
}

pub fn eval(src: &str) {
  let env = RuntimeEnvironment::new(Environment::std());

  let mut sources = Sources::new();
  let id = sources.add(Source::new("inline.rbr".into(), src.into()));
  let sources = Arc::new(sources);

  let hir = rb_diagnostic::run_or_exit(sources.clone(), || {
    let res = cst::SourceFile::parse(src);

    if res.errors().is_empty() {
      rb_hir_lower::lower_source(res.tree(), id)
    } else {
      for error in res.errors() {
        emit!(error.message(), Span { file: id, range: error.span() });
      }

      Default::default()
    }
  });

  // TODO: This is where we join all the threads, collect all the functions up,
  // and then split out to a thread pool to typecheck and lower each function.
  let mut functions = vec![];

  let (typer_env, mir_env) = env.build(&hir.0);

  rb_diagnostic::run_or_exit(sources, || {
    let (hir, span_maps) = hir;

    for (idx, function) in hir.functions {
      let span_map = &span_maps[idx.into_raw().into_u32() as usize];

      let typer = rb_typer::Typer::check(&typer_env, &function, &span_map);
      if rb_diagnostic::is_ok() {
        let mut func = rb_mir_lower::lower_function(&mir_env, &typer, &function);
        func.id = rb_mir::ast::UserFunctionId(idx.into_raw().into_u32() as u64);

        functions.push(func);
      }
    }
  });

  // If we get to this point, all checks have passed, and we can compile to
  // cranelift IR. Collect all the functions, split them into chunks, and compile
  // them on a thread pool.

  eval_mir(env, functions);
}

pub fn run(
  env: RuntimeEnvironment,
  sources: Arc<Sources>,
  id: SourceId,
) -> Result<(), Vec<Diagnostic>> {
  let src = sources.get(id);

  let hir = rb_diagnostic::run(sources.clone(), || {
    let res = cst::SourceFile::parse(&src.source);

    if res.errors().is_empty() {
      rb_hir_lower::lower_source(res.tree(), id)
    } else {
      for error in res.errors() {
        emit!(error.message(), Span { file: id, range: error.span() });
      }

      Default::default()
    }
  })?;

  // TODO: This is where we join all the threads, collect all the functions up,
  // and then split out to a thread pool to typecheck and lower each function.
  let mut functions = vec![];

  let (typer_env, mir_env) = env.build(&hir.0);

  rb_diagnostic::run(sources, || {
    let (hir, span_maps) = hir;

    for (idx, function) in hir.functions {
      let span_map = &span_maps[idx.into_raw().into_u32() as usize];

      let typer = rb_typer::Typer::check(&typer_env, &function, &span_map);
      if rb_diagnostic::is_ok() {
        let mut func = rb_mir_lower::lower_function(&mir_env, &typer, &function);
        func.id = rb_mir::ast::UserFunctionId(idx.into_raw().into_u32() as u64);

        functions.push(func);
      }
    }
  })?;

  // If we get to this point, all checks have passed, and we can compile to
  // cranelift IR. Collect all the functions, split them into chunks, and compile
  // them on a thread pool.

  eval_mir(env, functions);

  Ok(())
}

fn eval_mir(env: RuntimeEnvironment, functions: Vec<rb_mir::ast::Function>) {
  let mut jit = rb_jit::JIT::new(env.intrinsics());

  for func in &functions {
    jit.declare_function(func);
  }

  let compiled = run_parallel(&functions, || jit.new_thread(), |ctx, f| ctx.compile_function(f));

  let mut function_ids = vec![];
  for func in compiled.into_iter() {
    function_ids.push(jit.define_function(func).unwrap());
  }

  jit.finalize();
  jit.eval(*function_ids.last().unwrap());
}

impl RuntimeEnvironment {
  fn build(&self, hir: &rb_hir::ast::SourceFile) -> (rb_typer::Environment, rb_mir_lower::Env) {
    let mut typer_env = self.env.typer_env();
    let mut mir_env = self.mir_env();

    for (id, f) in hir.functions.values().enumerate() {
      mir_env.declare_user_function(id as u64, f);
    }
    for (id, s) in hir.structs.values().enumerate() {
      typer_env.structs.insert(
        s.name.clone(),
        s.fields.iter().map(|(name, te)| (name.clone(), rb_typer::type_of_type_expr(te))).collect(),
      );
      mir_env.structs.insert(s.name.clone(), rb_mir::ast::StructId(id as u64));
    }

    (typer_env, mir_env)
  }

  fn mir_env(&self) -> rb_mir_lower::Env {
    rb_mir_lower::Env {
      items:   self
        .env
        .ids
        .iter()
        .enumerate()
        .map(|(k, v)| {
          (v.clone(), rb_mir_lower::Item::NativeFunction(rb_mir::ast::NativeFunctionId(k as u64)))
        })
        .collect(),
      structs: Default::default(),
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
  fn foo() {
    eval(
      r#"
        assert_eq(2 * 3 + 4 + 5, 15)
        4
      "#,
    );
  }
}
