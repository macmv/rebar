use codegen::ir;
use cranelift::prelude::*;

#[derive(Debug, Clone)]
pub enum Slot<T = ir::Value> {
  Empty,
  Single(T),
  Multiple(Vec<T>),
}

impl<T> Slot<T> {
  pub fn len(&self) -> usize {
    match self {
      Slot::Empty => 0,
      Slot::Single(_) => 1,
      Slot::Multiple(vs) => vs.len(),
    }
  }
}

impl Slot<Variable> {
  pub fn set(&self, builder: &mut FunctionBuilder, values: &[ir::Value]) {
    match self {
      Slot::Empty => {}
      Slot::Single(v) => {
        assert!(!values.is_empty(), "ir must have at least one element, got {values:?}");
        builder.def_var(*v, values[0]);
      }
      Slot::Multiple(vs) => {
        assert!(!values.is_empty(), "ir must have at least one element, got {values:?}");
        for (i, v) in vs.iter().enumerate() {
          builder.def_var(*v, values[i]);
        }
      }
    }
  }
}

impl<I, T> From<I> for Slot<T>
where
  I: Iterator<Item = T>,
{
  fn from(value: I) -> Self {
    let mut values = vec![];
    for v in value {
      values.push(v);
    }

    if values.is_empty() {
      Slot::Empty
    } else if values.len() == 1 {
      Slot::Single(values.remove(0))
    } else {
      Slot::Multiple(values)
    }
  }
}
