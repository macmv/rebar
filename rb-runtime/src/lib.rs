use std::sync::Arc;

mod stdlib;

pub use stdlib::*;

use rb_diagnostic::{emit, Source, Sources, Span};
use rb_syntax::cst;

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
  rb_diagnostic::run_or_exit(sources, || {
    let (hir, span_map) = hir;

    for function in hir.functions.values() {
      let typer = rb_typer::Typer::check(&static_env, function, &span_map);
      functions.push(rb_mir_lower::lower_function(&typer, function));
    }
  });

  // TODO: If we get to this point, all checks have passed, and we can compile to
  // cranelift IR. Again, join on the above pool, collect all the functions, and
  // dispatch the MIR to a thread pool.

  let mut jit = rb_jit::jit::JIT::new();
  let mut function_ids = vec![];
  for f in functions {
    function_ids.push(jit.compile_function(&f));
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
