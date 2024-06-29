use std::sync::Arc;

mod stdlib;

pub use stdlib::*;

use rb_diagnostic::{emit, Source, Sources, Span};
use rb_syntax::cst;

const NUM_CPUS: usize = 32;

pub fn eval(src: &str) {
  let env = Environment::std();

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

  let static_env = env.static_env();
  let mir_env = env.mir_env();
  rb_diagnostic::run_or_exit(sources, || {
    let (hir, span_map) = hir;

    for function in hir.functions.values() {
      let typer = rb_typer::Typer::check(&static_env, function, &span_map);
      functions.push(rb_mir_lower::lower_function(&mir_env, &typer, function));
    }
  });

  // If we get to this point, all checks have passed, and we can compile to
  // cranelift IR. Collect all the functions, split them into chunks, and compile
  // them on a thread pool.

  let mut jit = rb_jit::jit::JIT::new(env.dyn_call_ptr());

  let mut results = vec![vec![]; NUM_CPUS];

  let chunk_size = (functions.len() / NUM_CPUS).max(1);
  // Double check that `zip` doesn't skip anything.
  assert!(functions.chunks(chunk_size).len() <= results.len());

  std::thread::scope(|scope| {
    for (chunk, out) in functions.chunks_mut(chunk_size).zip(results.iter_mut()) {
      let mut thread_ctx = jit.new_thread();

      scope.spawn(move || {
        for f in chunk {
          thread_ctx.translate_function(f);
          let res = thread_ctx.compile();
          out.push((
            res.code_buffer().to_vec().into_boxed_slice(),
            res.buffer.alignment as u64,
            res.buffer.relocs().to_vec().into_boxed_slice(),
            thread_ctx.func().clone(),
          ));

          thread_ctx.clear();
        }
      });
    }
  });

  let mut function_ids = vec![];
  for (code, alignment, relocs, func) in results.iter().flatten() {
    function_ids.push(jit.define_function(code, *alignment, func, relocs).unwrap());
  }

  jit.finalize();
  jit.eval(function_ids[0]);
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn foo() {
    eval(
      r#"
        println(2 * 3 + 4 + 5)
        4
      "#,
    );

    panic!();
  }
}
