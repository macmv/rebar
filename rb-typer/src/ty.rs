use la_arena::Idx;

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  Int,
  Bool,
  Unit,

  Function(Vec<Type>, Box<Type>),

  Union(Vec<Type>),

  // TODO: Get this out of the public API.
  Var(VarId),
}

pub type VarId = Idx<TypeVar>;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeVar {
  pub values: Vec<Type>,
  pub uses:   Vec<Type>,

  pub description: String,
}

impl TypeVar {
  pub fn new(description: String) -> Self { TypeVar { values: vec![], uses: vec![], description } }
}
