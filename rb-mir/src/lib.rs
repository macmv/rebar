use std::collections::HashMap;

use ast::StructId;
use rb_hir::ast::Path;
use rb_typer::Type;

pub mod ast;

// Global context needed in the JIT, that is produced by `rb-mir-lower`.
#[derive(Default, Clone)]
pub struct MirContext {
  pub struct_paths: HashMap<Path, StructId>,
  pub structs:      HashMap<StructId, Struct>,
  pub items:        HashMap<Path, Item>,
}

#[derive(Clone)]
pub enum Item {
  NativeFunction(ast::NativeFunctionId),
  UserFunction(UserFunction),
}

#[derive(Clone)]
pub struct UserFunction {
  pub id:        ast::UserFunctionId,
  pub intrinsic: Option<ast::Intrinsic>,
}

#[derive(Clone)]
pub struct Struct {
  pub fields: Vec<(String, Type)>,
}
