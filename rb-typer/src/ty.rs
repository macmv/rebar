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
  pub constraints: Vec<Type>,
}

impl TypeVar {
  pub fn new() -> Self { Self { constraints: Vec::new() } }
}
