use std::collections::{HashMap, HashSet};

use la_arena::Idx;
use rb_diagnostic::Span;
use rb_hir::ast as hir;

/// A rendered type. This is the result of typechecking.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  Primitive(hir::PrimitiveType),
  Array(Box<Type>),
  Tuple(Vec<Type>),

  Function(Vec<Type>, Box<Type>),
  Union(Vec<Type>),

  Struct(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
  pub names:   HashMap<String, Type>,
  pub structs: HashMap<String, Vec<(String, Type)>>,
}

/// A type with variables in it. Internal to the typer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum VType {
  Integer,
  Primitive(hir::PrimitiveType),

  Array(Box<VType>),
  Tuple(Vec<VType>),

  Function(Vec<VType>, Box<VType>),

  // TODO: Build unions sometimes.
  #[allow(dead_code)]
  Union(Vec<VType>),

  Var(VarId),

  // FIXME: Replace with resolved Path.
  Struct(String),
}

impl Type {
  pub const fn unit() -> Self { Type::Tuple(vec![]) }
}

impl From<Type> for VType {
  fn from(ty: Type) -> Self {
    match ty {
      Type::Primitive(lit) => VType::Primitive(lit),
      Type::Array(ty) => VType::Array(Box::new((*ty).into())),
      Type::Tuple(types) => VType::Tuple(types.into_iter().map(Into::into).collect()),
      Type::Function(args, ret) => {
        VType::Function(args.into_iter().map(Into::into).collect(), Box::new((*ret).into()))
      }
      Type::Union(types) => VType::Union(types.into_iter().map(Into::into).collect()),
      Type::Struct(name) => VType::Struct(name),
    }
  }
}

impl From<hir::PrimitiveType> for Type {
  fn from(literal: hir::PrimitiveType) -> Self { Type::Primitive(literal) }
}
impl From<hir::PrimitiveType> for VType {
  fn from(literal: hir::PrimitiveType) -> Self { VType::Primitive(literal) }
}

pub type VarId = Idx<TypeVar>;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeVar {
  pub values: HashSet<VType>,
  pub uses:   HashSet<VType>,

  pub span:        Span,
  pub description: String,
}

impl TypeVar {
  pub fn new(span: Span, description: String) -> Self {
    TypeVar { values: HashSet::new(), uses: HashSet::new(), span, description }
  }
}
