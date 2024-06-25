mod context;
mod diagnostic;
mod sources;

use std::sync::Arc;

pub use diagnostic::*;
pub use sources::*;

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

pub fn run<T>(sources: Arc<Sources>, f: impl FnOnce() -> T) -> Result<T, Vec<Diagnostic>> {
  Context::init(sources);
  Context::run(|ctx| {
    ctx.collect_errors();
  });

  let res = f();
  let errors = Context::run(|ctx| ctx.take_errors());
  Context::cleanup();

  if errors.is_empty() {
    Ok(res)
  } else {
    Err(errors)
  }
}

pub fn emit(diagnostic: Diagnostic) {
  Context::run(|ctx| {
    ctx.error(diagnostic);
  });
}

#[macro_export]
macro_rules! emit {
  ($message:expr, $span:expr) => {
    $crate::emit($crate::Diagnostic::error($message, $span))
  };
}
