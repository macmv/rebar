use std::collections::{HashMap, HashSet};

use la_arena::Idx;
use rb_diagnostic::Span;

/// A rendered type. This is the result of typechecking.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  Literal(Literal),

  Function(Vec<Type>, Box<Type>),
  Union(Vec<Type>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
  pub names: HashMap<String, Type>,
}

/// A type with variables in it. Internal to the typer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VType {
  Literal(Literal),

  Function(Vec<VType>, Box<VType>),

  // TODO: Build unions sometimes.
  #[allow(dead_code)]
  Union(Vec<VType>),

  // TODO: Get this out of the public API.
  Var(VarId),
}

impl From<Type> for VType {
  fn from(ty: Type) -> Self {
    match ty {
      Type::Literal(lit) => VType::Literal(lit),
      Type::Function(args, ret) => {
        VType::Function(args.into_iter().map(Into::into).collect(), Box::new((*ret).into()))
      }
      Type::Union(types) => VType::Union(types.into_iter().map(Into::into).collect()),
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Literal {
  Unit,
  Int,
  Bool,
  String,
}

impl From<Literal> for Type {
  fn from(literal: Literal) -> Self { Type::Literal(literal) }
}
impl From<Literal> for VType {
  fn from(literal: Literal) -> Self { VType::Literal(literal) }
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
