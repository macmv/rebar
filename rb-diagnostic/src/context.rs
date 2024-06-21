use std::cell::RefCell;

pub struct Context {
  error: bool,
}

thread_local! {
  static CONTEXT: RefCell<Option<Context>> = RefCell::new(None);
}

impl Context {
  fn new() -> Self { Context { error: false } }

  pub fn init() {
    CONTEXT.with(|c| {
      if (*c.borrow()).is_some() {
        panic!("context already initialized");
      }

      *c.borrow_mut() = Some(Context::new());
    });
  }
  pub fn cleanup() {
    CONTEXT.with(|c| {
      *c.borrow_mut() = None;
    });
  }

  pub fn run<T>(f: impl FnOnce(&Context) -> T) -> T {
    CONTEXT.with(|c| f(c.borrow().as_ref().expect("context not initialized")))
  }

  pub fn exit_if_error(&self) {
    if self.error {
      std::process::exit(1);
    }
  }
}
