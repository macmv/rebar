use std::collections::HashMap;

use ast::StructId;
use rb_typer::Type;

pub mod ast;

// Global context needed in the JIT, that is produced by `rb-mir-lower`.
pub struct MirContext {
  pub structs: HashMap<StructId, Struct>,
}

pub struct Struct {
  pub fields: Vec<(String, Type)>,
}
