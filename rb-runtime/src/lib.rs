use std::sync::Arc;

use rb_diagnostic::{emit, Source, Sources, Span};
use rb_syntax::cst;

pub fn eval(src: &str) {
  let cst = cst::SourceFile::parse(src).tree();
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
  // let mut functions = vec![];

  rb_diagnostic::run_or_exit(sources, || {
    let (hir, span_map) = hir;

    for function in hir.functions.values() {
      let typer = rb_typer::Typer::check(&function, &span_map);
      // functions.push(rb_mir_lower::lower_expr(&typer, function));
    }
  });

  rb_jit::jit::interpret(src);
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn foo() {
    eval(
      r#"print_impl(2 * 3 + 4 + 5)
         4
      "#,
    );

    panic!();
  }
}
