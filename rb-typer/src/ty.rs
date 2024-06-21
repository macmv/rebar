#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  Int,
  Bool,
  Unit,

  Function(Vec<Type>, Box<Type>),

  Union(Vec<Type>),
}
