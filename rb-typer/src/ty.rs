use la_arena::Idx;
use rb_diagnostic::Span;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  Literal(Literal),

  Function(Vec<Type>, Box<Type>),

  Union(Vec<Type>),

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

pub type VarId = Idx<TypeVar>;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeVar {
  pub values: Vec<Type>,
  pub uses:   Vec<Type>,

  pub span:        Span,
  pub description: String,
}

impl TypeVar {
  pub fn new(span: Span, description: String) -> Self {
    TypeVar { values: vec![], uses: vec![], span, description }
  }
}
