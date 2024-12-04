use codegen::ir::{self, StackSlot};
use cranelift::prelude::*;

use crate::FuncBuilder;

#[derive(Debug, Clone)]
pub enum Slot<T = ir::Value> {
  Empty,
  Single(T),
  Multiple(usize, StackSlot),
}

impl<T> Slot<T> {
  pub fn len(&self) -> usize {
    match self {
      Slot::Empty => 0,
      Slot::Single(_) => 1,
      Slot::Multiple(len, _) => *len,
    }
  }
}

impl Slot<Variable> {
  pub fn new(func: &mut FuncBuilder, len: usize) -> Self {
    if len == 0 {
      Slot::Empty
    } else if len == 1 {
      let var = Variable::new(func.next_variable);
      func.builder.declare_var(var, ir::types::I64);
      func.next_variable += 1;

      Slot::Single(var)
    } else {
      Slot::Multiple(
        len,
        func
          .builder
          .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, len as u32 * 8)),
      )
    }
  }

  pub fn set(&self, builder: &mut FunctionBuilder, values: &[ir::Value]) {
    match self {
      Slot::Empty => {}
      Slot::Single(v) => {
        assert!(!values.is_empty(), "ir must have at least one element, got {values:?}");
        builder.def_var(*v, values[0]);
      }
      Slot::Multiple(len, slot) => {
        assert!(!values.is_empty(), "ir must have at least one element, got {values:?}");
        assert!(values.len() <= *len, "ir must have at most {len} elements, got {values:?}");
        for (i, v) in values.iter().enumerate() {
          builder.ins().stack_store(v.clone(), *slot, i as i32 * 8);
        }
      }
    }
  }
}
