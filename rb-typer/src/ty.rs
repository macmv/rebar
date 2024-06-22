use la_arena::Idx;
use rb_diagnostic::Span;

/// A rendered type. This is the result of typechecking.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  Literal(Literal),

  Function(Vec<Type>, Box<Type>),
  Union(Vec<Type>),
}

/// A type with variables in it. Internal to the typer.
#[derive(Debug, Clone, PartialEq)]
pub enum VType {
  Literal(Literal),

  Function(Vec<VType>, Box<VType>),
  Union(Vec<VType>),

  // TODO: Get this out of the public API.
  Var(VarId),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
  Int,
  Bool,
  Unit,
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
  pub values: Vec<VType>,
  pub uses:   Vec<VType>,

  pub span:        Span,
  pub description: String,
}

impl TypeVar {
  pub fn new(span: Span, description: String) -> Self {
    TypeVar { values: vec![], uses: vec![], span, description }
  }
}
