mod context;
mod diagnostic;
mod sources;

use std::sync::Arc;

pub use diagnostic::Diagnostic;
pub use sources::{Source, Sources};

use context::Context;

pub fn run_or_exit<T>(sources: Arc<Sources>, f: impl FnOnce() -> T) -> T {
  Context::init(sources);
  let res = f();
  Context::run(|ctx| {
    ctx.exit_if_error();
  });
  Context::cleanup();
  res
}

pub fn emit(diagnostic: Diagnostic) {
  Context::run(|ctx| {
    ctx.error();
    // let source = diagnostic.render(ctx.sources());
    eprintln!("error!");
  });
}

#[macro_export]
macro_rules! emit {
  ($message:expr, $span:expr) => {
    $crate::emit($crate::Diagnostic::error($message, $span))
  };
}
