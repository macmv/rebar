use std::sync::Arc;

use rb_diagnostic::{emit, Sources, Span};
use rb_syntax::cst;

pub fn eval(src: &str) {
  let cst = cst::SourceFile::parse(src).tree();
  let mut sources = Sources::new();
  let id = sources.add(src.into());
  let sources = Arc::new(sources);

  rb_diagnostic::run_or_exit(sources, || {
    let res = cst::SourceFile::parse(src);
    for error in res.errors() {
      emit!(error.message(), Span { file: id, range: error.span() });
    }

    // let hir = rb_hir_lower::lower_expr(&res.tree());
  });
  // let mir = rb_diagnostic::run_or_exit(sources, || {
  //   let mut functions = vec![];
  //   for function in hir.functions {
  //     let typer = rb_typer::Typer::check(&function);
  //     functions.push(rb_mir_lower::lower_expr(&typer, function));
  //   }
  //   functions
  // });

  rb_jit::jit::interpret(src);
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn foo() {
    eval(
      r#"print_impl(2 * 3 + 4 +)
         4
      "#,
    );

    panic!();
  }
}
