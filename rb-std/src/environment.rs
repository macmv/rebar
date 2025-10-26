use rb_mir::MirContext;
use rb_typer::Type;
use std::collections::HashMap;

use crate::{OwnedValue, Value};

pub struct Environment {
  pub static_functions: HashMap<String, Function>,
  pub mir_ctx:          MirContext,
}

pub struct Function {
  pub args: Vec<Type>,
  pub ret:  Type,

  pub imp: Box<dyn Fn(Vec<Value>) -> OwnedValue>,
}

impl Environment {
  pub fn empty() -> Self {
    Environment { static_functions: HashMap::new(), mir_ctx: MirContext::default() }
  }
}
