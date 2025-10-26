use crate::FuncBuilder;

use rb_codegen::{Variable, VariableSize::*};
use rb_value::ValueType;

#[derive(Debug, Clone)]
pub struct RValue {
  pub ty:   ValueType,
  pub kind: RValueKind,
}

#[derive(Debug, Clone)]
pub enum RValueKind {
  Const(Vec<u64>),
  Dyn(Vec<Variable>),
}

impl RValue {
  pub fn new(ty: ValueType, ir: Vec<Variable>) -> Self { RValue { ty, kind: RValueKind::Dyn(ir) } }
  pub fn single(ty: ValueType, ir: Variable) -> Self {
    RValue { ty, kind: RValueKind::Dyn(vec![ir]) }
  }

  pub fn nil() -> Self { RValue { ty: ValueType::Nil, kind: RValueKind::Const(vec![]) } }

  pub fn const_bool(ir: bool) -> Self {
    RValue { ty: ValueType::Bool, kind: RValueKind::Const(vec![ir as u64]) }
  }
  pub fn const_user_function(v: u64) -> Self {
    RValue { ty: ValueType::UserFunction, kind: RValueKind::Const(vec![v]) }
  }

  pub fn bool(ir: Variable) -> Self { RValue::single(ValueType::Bool, ir) }
  pub fn int(ir: Variable) -> Self { RValue::single(ValueType::Int, ir) }
  pub fn function(ir: Variable) -> Self { RValue::single(ValueType::Function, ir) }
  pub fn slice(ptr: Variable, len: Variable) -> Self {
    RValue::new(ValueType::Slice, vec![ptr, len])
  }
}

impl RValue {
  #[track_caller]
  pub fn unwrap_single(&self, func: &mut FuncBuilder) -> Variable {
    match self.kind {
      RValueKind::Const(ref items) => {
        assert_eq!(items.len(), 1, "expected single value, got {items:?}");
        func.builder.instr().mov(Bit64, items[0])
      }
      RValueKind::Dyn(ref v) => {
        assert_eq!(v.len(), 1, "expected single value, got {v:?}");

        v[0]
      } /*
        Self::Untyped(slot) => match slot {
          Slot::Empty => panic!(),
          Slot::Single(_) => panic!(),
          Slot::Multiple(_, _) => slot.get(&mut func.builder, 1),
        },

        Self::TypedPtr(_, ptr) => func.builder.ins().load(ir::types::I64, MemFlags::new(), *ptr, 0),
        Self::UntypedPtr(_, ptr) => func.builder.ins().load(ir::types::I64, MemFlags::new(), *ptr, 8),
        */
    }
  }

  pub fn const_ty(&self) -> Option<ValueType> { Some(self.ty) }

  /*
  /// Returns the extended form of this value. This is used when passing a value
  /// into a union slot, or back to native code. The number of values may change
  /// depending on the type (so this works for function calls, but not for
  /// block arguments).
  fn to_extended_ir(&self, func: &mut FuncBuilder, len: Option<NonZero<u32>>) -> Variable {
    match self {
      Self::TypedConst(ty, items) => {
        let ty = ty.as_i64();
        let ty_ir = func.builder.ins().iconst(ir::types::I64, ty);

        let len = match len {
          Some(v) => v.get() as usize,
          None => items.len() + 1,
        };

        assert!(items.len() + 1 <= len, "value {self:?} cannot fit into slot of length {len:?}");

        if len == 1 {
          Slot::Single(ty_ir)
        } else {
          let slot = Slot::new_multiple(&mut func.builder, len);

          slot.set(&mut func.builder, 0, ty_ir);

          for (i, v) in items.iter().enumerate() {
            let ir = func.builder.ins().iconst(ir::types::I64, *v);
            slot.set(&mut func.builder, i + 1, ir);
          }

          slot
        }
      }
      Self::TypedDyn(ty, values) => {
        let ty = ty.as_i64();
        let ty_ir = func.builder.ins().iconst(ir::types::I64, ty);

        let len = match len {
          Some(v) => v.get() as usize,
          None => values.len() + 1,
        };

        assert!(values.len() + 1 <= len, "value {self:?} cannot fit into slot of length {len:?}");

        if len == 1 {
          Slot::Single(ty_ir)
        } else {
          let slot = Slot::new_multiple(&mut func.builder, len);

          slot.set(&mut func.builder, 0, ty_ir);

          let addr = slot.addr(&mut func.builder, 1);
          values.copy_to(func, addr);

          slot
        }
      }
      Self::Untyped(slot) => *slot,

      // FIXME: Add a `Slot` variant for this.
      Self::TypedPtr(ty, ptr) => {
        let ty_ir = func.builder.ins().iconst(ir::types::I64, ty.as_i64());

        let len = match len {
          Some(v) => v.get(),
          None => ty.len(&func.ctx) + 1,
        };

        if len == 1 {
          Slot::Single(ty_ir)
        } else {
          let slot = Slot::new_multiple(&mut func.builder, len as usize);

          let ty_ir = func.builder.ins().iconst(ir::types::I64, ty.as_i64());
          slot.set(&mut func.builder, 0, ty_ir);

          for i in 0..len - 1 {
            let v = func.builder.ins().load(ir::types::I64, MemFlags::new(), *ptr, i as i32 * 8);
            slot.set(&mut func.builder, i as usize + 1, v);
          }

          slot
        }
      }
      Self::UntypedPtr(len, ptr) => {
        let slot = Slot::new_multiple(&mut func.builder, *len as usize);

        for i in 0..*len {
          let v = func.builder.ins().load(ir::types::I64, MemFlags::new(), *ptr, i as i32 * 8);
          slot.set(&mut func.builder, i as usize + 1, v);
        }

        slot
      }
    }
  }
  */

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union), and when the number of
  /// values can change depending on the type (so this works for function
  /// arguments, but not for block arguments).
  #[track_caller]
  fn to_compact_ir(&self, func: &mut FuncBuilder) -> Vec<Variable> {
    match self.kind {
      RValueKind::Const(ref items) => {
        items.into_iter().map(|it| func.builder.instr().mov(Bit64, *it)).collect()
      }
      RValueKind::Dyn(ref v) => v.clone(),
    }
  }

  /// Returns the dynamic IR values for this RValue. This should be used
  /// whenever the length of arguments can change (for example in a function
  /// call). For block arguments, which must have a consistent size, use
  /// `to_sized_ir`.
  #[track_caller]
  pub fn to_ir(&self, func: &mut FuncBuilder) -> Vec<Variable> { self.to_compact_ir(func) }
}
