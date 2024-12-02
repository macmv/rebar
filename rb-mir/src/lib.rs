use std::collections::HashMap;

use ast::StructId;
use rb_typer::Type;

pub mod ast;

// Global context needed in the JIT, that is produced by `rb-mir-lower`.
#[derive(Default, Clone)]
pub struct MirContext {
  pub struct_paths: HashMap<String, StructId>,
  pub structs:      HashMap<StructId, Struct>,
}

#[derive(Clone)]
pub struct Struct {
  pub fields: Vec<(String, Type)>,
}
