use std::{cell::RefCell, sync::Arc};

use crate::{Diagnostic, Sources};

pub struct Context {
  error:       bool,
  diagnostics: Option<Vec<Diagnostic>>,

  sources: Arc<Sources>,
}

thread_local! {
  static CONTEXT: RefCell<Option<Context>> = const { RefCell::new(None) };
}

impl Context {
  fn new(sources: Arc<Sources>) -> Self { Context { error: false, diagnostics: None, sources } }

  pub fn is_ok(&self) -> bool { !self.error }

  pub fn enable_error_collection(&mut self) { self.diagnostics = Some(vec![]); }
  pub fn take_errors(&mut self) -> Vec<Diagnostic> {
    match self.diagnostics {
      Some(ref mut diagnostics) => std::mem::take(diagnostics),
      None => panic!("Context::collect_errors() not called"),
    }
  }

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

  pub fn error(&mut self, diagnostic: Diagnostic) {
    self.error = true;

    match self.diagnostics {
      Some(ref mut diagnostics) => diagnostics.push(diagnostic),
      None => {
        eprintln!("{}", diagnostic.render(self.sources()));
      }
    }
  }
  pub fn sources(&self) -> &Sources { &self.sources }

  pub fn exit_if_error(&self) {
    if self.error {
      std::process::exit(1);
    }
  }
}
