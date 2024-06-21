use std::{cell::RefCell, sync::Arc};

use crate::Sources;

pub struct Context {
  error:   bool,
  sources: Arc<Sources>,
}

thread_local! {
  static CONTEXT: RefCell<Option<Context>> = RefCell::new(None);
}

impl Context {
  fn new(sources: Arc<Sources>) -> Self { Context { error: false, sources } }

  pub fn init(sources: Arc<Sources>) {
    CONTEXT.with(|c| {
      if (*c.borrow()).is_some() {
        panic!("context already initialized");
      }

      *c.borrow_mut() = Some(Context::new(sources));
    });
  }
  pub fn cleanup() {
    CONTEXT.with(|c| {
      *c.borrow_mut() = None;
    });
  }

  pub fn run<T>(f: impl FnOnce(&mut Context) -> T) -> T {
    CONTEXT.with(|c| f(c.borrow_mut().as_mut().expect("context not initialized")))
  }

  pub fn error(&mut self) { self.error = true; }
  pub fn sources(&self) -> &Sources { &self.sources }

  pub fn exit_if_error(&self) {
    if self.error {
      std::process::exit(1);
    }
  }
}
