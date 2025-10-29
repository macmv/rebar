use std::{
  cell::RefCell,
  sync::{Arc, atomic::AtomicBool},
};

use parking_lot::Mutex;

use crate::{Diagnostic, Sources};

pub struct Context {
  error:       AtomicBool,
  diagnostics: Mutex<Option<Vec<Diagnostic>>>,

  sources: Arc<Sources>,
}

// This is a bit ugly, but we want two things:
// - In tests (in various places) we want contexts to be isolated. So this is a
//   thread-local.
// - In the runtime, we need to spawn threads and collect diagnostics from those
//   threads.
//
// So, the context provides a method to spawn a thread, and copy the context to
// that other thread. This is why we need an Arc<> in here.
thread_local! {
  static CONTEXT: RefCell<Option<Arc<Context>>> = const { RefCell::new(None) };
}

impl Context {
  fn new(sources: Arc<Sources>) -> Self {
    Context { error: AtomicBool::new(false), diagnostics: Mutex::new(None), sources }
  }

  pub fn is_ok(&self) -> bool { !self.error.load(std::sync::atomic::Ordering::SeqCst) }

  pub fn enable_error_collection(&self) { *self.diagnostics.lock() = Some(vec![]); }
  pub fn take_errors(&self) -> Vec<Diagnostic> {
    match *self.diagnostics.lock() {
      Some(ref mut diagnostics) => std::mem::take(diagnostics),
      None => panic!("Context::collect_errors() not called"),
    }
  }

  pub fn init(sources: Arc<Sources>) {
    CONTEXT.with(|c| {
      let mut c = c.borrow_mut();

      if c.is_some() {
        panic!("context already initialized");
      }

      *c = Some(Arc::new(Context::new(sources)));
    });
  }
  pub fn cleanup() {
    CONTEXT.with(|c| {
      let mut c = c.borrow_mut();

      if c.is_none() {
        panic!("context not initialized");
      }

      *c = None;
    });
  }

  pub fn run<T>(f: impl FnOnce(&Context) -> T) -> T {
    CONTEXT.with(|c| {
      let c = c.borrow_mut();
      f(c.as_ref().expect("context not initialized"))
    })
  }

  pub fn error(&self, diagnostic: Diagnostic) {
    self.error.store(true, std::sync::atomic::Ordering::SeqCst);

    match *self.diagnostics.lock() {
      Some(ref mut diagnostics) => diagnostics.push(diagnostic),
      None => {
        eprintln!("{}", diagnostic.render(self.sources()));
      }
    }
  }
  pub fn sources(&self) -> &Sources { &self.sources }

  pub fn exit_if_error(&self) {
    if self.error.load(std::sync::atomic::Ordering::SeqCst) {
      #[cfg(feature = "test")]
      panic!("errors were emitted");

      #[cfg(not(feature = "test"))]
      std::process::exit(1);
    }
  }
}
