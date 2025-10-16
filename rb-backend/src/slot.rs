use crate::FuncBuilder;

#[derive(Debug, Copy, Clone)]
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

impl Slot<Value> {
  #[track_caller]
  pub fn new_multiple(builder: &mut FunctionBuilder, len: usize) -> Self {
    assert!(len >= 2);

    Slot::Multiple(
      len,
      builder
        .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, len as u32 * 8)),
    )
  }

  #[track_caller]
  pub fn set(&self, builder: &mut FunctionBuilder, index: usize, value: ir::Value) {
    match self {
      Slot::Multiple(len, slot) => {
        assert!(index < *len, "cannot set index {index} in slot with {len} elements");
        builder.ins().stack_store(value, *slot, index as i32 * 8);
      }
      _ => panic!("cannot set value in non-multiple slot"),
    }
  }

  pub fn get(&self, builder: &mut FunctionBuilder, index: usize) -> ir::Value {
    match self {
      Slot::Multiple(len, slot) => {
        assert!(index < *len, "index out of bounds");
        builder.ins().stack_load(ir::types::I64, *slot, index as i32 * 8)
      }
      _ => panic!("cannot set value in non-multiple slot"),
    }
  }

  pub fn addr(&self, builder: &mut FunctionBuilder, index: usize) -> ir::Value {
    match self {
      Slot::Multiple(len, slot) => {
        assert!(index < *len, "index out of bounds");
        builder.ins().stack_addr(ir::types::I64, *slot, index as i32 * 8)
      }
      _ => panic!("cannot set value in non-multiple slot"),
    }
  }

  pub fn copy_to(&self, func: &mut FuncBuilder, addr: ir::Value) {
    match *self {
      Slot::Empty => {}
      Slot::Single(v) => {
        func.builder.ins().store(MemFlags::new(), v, addr, 0);
      }
      Slot::Multiple(len, slot) => {
        let len = func.builder.ins().iconst(ir::types::I64, len as i64 * 8);
        let ptr = func.builder.ins().stack_addr(ir::types::I64, slot.clone(), 0);

        func.builder.call_memcpy(func.target_frontend_config(), addr, ptr, len);
      }
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

  pub fn copy_from(&self, builder: &mut FunctionBuilder, slot: &Slot) {
    match (*self, *slot) {
      (Slot::Empty, _) => {}
      (Slot::Single(_), Slot::Empty) => panic!("cannot assign empty slot to variable"),
      (Slot::Single(v), Slot::Single(value)) => {
        builder.def_var(v, value);
      }
      (Slot::Single(v), Slot::Multiple(_, slot)) => {
        let value = builder.ins().stack_load(ir::types::I64, slot, 0);
        builder.def_var(v, value);
      }
      (Slot::Multiple(_, _), Slot::Empty) => panic!("cannot assign empty slot to variable"),
      (Slot::Multiple(_, slot), Slot::Single(v)) => {
        builder.ins().stack_store(v, slot, 0);
      }
      (Slot::Multiple(len, slot), Slot::Multiple(value_len, value_slot)) => {
        assert!(value_len <= len, "ir must have at most {len} elements, got {value_len}");

        for i in 0..value_len {
          let value = builder.ins().stack_load(ir::types::I64, value_slot, i as i32 * 8);

          builder.ins().stack_store(value, slot, i as i32 * 8);
        }
      }
    }
  }

  pub fn copy_from_slice(&self, builder: &mut FunctionBuilder, values: &[ir::Value]) {
    match self {
      Slot::Empty => {}
      Slot::Single(v) => {
        assert!(values.len() <= 1, "expected at least one 1 value, got none");
        builder.def_var(*v, values[0]);
      }
      Slot::Multiple(len, slot) => {
        assert!(values.len() <= *len, "expected at least {len} values, got {values:?}");

        for (i, value) in values.iter().enumerate() {
          builder.ins().stack_store(*value, *slot, i as i32 * 8);
        }
      }
    }
  }
}
