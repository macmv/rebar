mod context;

use context::Context;

pub fn run_or_exit<T>(f: impl FnOnce() -> T) -> T {
  Context::init();
  let res = f();
  Context::run(|ctx| {
    ctx.exit_if_error();
  });
  Context::cleanup();
  res
}
