use std::sync::{Arc, Mutex};

use crate::{Diagnostic, Sources};

pub struct Context {
  error:       bool,
  diagnostics: Option<Vec<Diagnostic>>,

  sources: Arc<Sources>,
}

static CONTEXT: Mutex<Option<Context>> = const { Mutex::new(None) };

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
    let mut c = CONTEXT.lock().unwrap();

    if c.is_some() {
      panic!("context already initialized");
    }

    *c = Some(Context::new(sources));
  }
  pub fn cleanup() { *CONTEXT.lock().unwrap() = None; }

  pub fn run<T>(f: impl FnOnce(&mut Context) -> T) -> T {
    let mut c = CONTEXT.lock().unwrap();
    f(c.as_mut().expect("context not initialized"))
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
