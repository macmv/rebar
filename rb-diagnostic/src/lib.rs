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
  Context::run(|ctx| ctx.exit_if_error());
  Context::cleanup();
  res
}

pub fn run<T>(sources: Arc<Sources>, f: impl FnOnce() -> T) -> Result<T, Vec<Diagnostic>> {
  Context::init(sources);
  Context::run(|ctx| ctx.enable_error_collection());

  let res = f();
  let errors = Context::run(|ctx| ctx.take_errors());
  Context::cleanup();

  if errors.is_empty() { Ok(res) } else { Err(errors) }
}

pub fn run_both<T>(sources: Arc<Sources>, f: impl FnOnce() -> T) -> (T, Vec<Diagnostic>) {
  Context::init(sources);
  Context::run(|ctx| ctx.enable_error_collection());

  let res = f();
  let errors = Context::run(|ctx| ctx.take_errors());
  Context::cleanup();

  (res, errors)
}

#[repr(transparent)]
pub struct Scope<'scope, 'env: 'scope> {
  scope: std::thread::Scope<'scope, 'env>,
}

pub fn scope<'env, F, T>(f: F) -> T
where
  F: for<'scope> FnOnce(&'scope Scope<'scope, 'env>) -> T,
{
  std::thread::scope(|scope| {
    // SAFETY: It's `repr(transparent)`, with all the same lifetimes.
    let scope =
      unsafe { std::mem::transmute::<&std::thread::Scope<'_, 'env>, &Scope<'_, 'env>>(scope) };
    f(scope)
  })
}

impl<'scope> Scope<'scope, '_> {
  pub fn spawn<F, T>(&'scope self, f: F) -> std::thread::ScopedJoinHandle<'scope, T>
  where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
  {
    let clone = Context::run(|ctx| ctx.clone_for_thread());
    self.scope.spawn(|| {
      clone.overwrite_thread();
      f()
    })
  }
}

pub fn emit(diagnostic: Diagnostic) {
  Context::run(|ctx| {
    ctx.error(diagnostic);
  });
}

pub fn check() -> Result<(), ()> { if is_ok() { Ok(()) } else { Err(()) } }
pub fn is_ok() -> bool { Context::run(|ctx| ctx.is_ok()) }

#[macro_export]
macro_rules! emit {
  ($span:expr => $msg_str:literal $($msg_args:tt)*) => {
    $crate::emit($crate::Diagnostic::error(format!($msg_str $($msg_args)*), $span))
  };

  ($span:expr => $message:expr) => {
    $crate::emit($crate::Diagnostic::error($message, $span))
  };
}
