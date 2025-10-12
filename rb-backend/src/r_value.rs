use std::num::NonZero;

use crate::{slot::Slot, FuncBuilder};

use cranelift::{
  codegen::ir,
  prelude::{InstBuilder, MemFlags},
};
use rb_value::{ParamKind, ValueType};

#[derive(Debug, Clone)]
pub enum RValue {
  TypedConst(ValueType, Vec<i64>),
  TypedDyn(ValueType, Slot),
  Untyped(Slot),

  TypedPtr(ValueType, ir::Value),
  UntypedPtr(u32, ir::Value),
}

impl RValue {
  pub fn nil() -> Self { RValue::TypedConst(ValueType::Nil, vec![]) }

  pub fn const_bool(ir: bool) -> Self { RValue::TypedConst(ValueType::Bool, vec![ir as i64]) }

  pub fn bool(ir: ir::Value) -> Self { RValue::TypedDyn(ValueType::Bool, Slot::Single(ir)) }
  pub fn int(ir: ir::Value) -> Self { RValue::TypedDyn(ValueType::Int, Slot::Single(ir)) }
  pub fn function(ir: ir::Value) -> Self { RValue::TypedDyn(ValueType::Function, Slot::Single(ir)) }
}

impl RValue {
  pub fn unwrap_single(&self, func: &mut FuncBuilder) -> ir::Value {
    match self {
      Self::TypedConst(_, items) => {
        assert_eq!(items.len(), 1, "expected single value, got {items:?}");
        func.builder.ins().iconst(ir::types::I64, items[0])
      }
      Self::TypedDyn(_, slot) => match slot {
        Slot::Empty => panic!(),
        Slot::Single(v) => *v,
        Slot::Multiple(_, _) => slot.get(&mut func.builder, 0),
      },
      Self::Untyped(slot) => match slot {
        Slot::Empty => panic!(),
        Slot::Single(_) => panic!(),
        Slot::Multiple(_, _) => slot.get(&mut func.builder, 1),
      },

      Self::TypedPtr(_, ptr) => func.builder.ins().load(ir::types::I64, MemFlags::new(), *ptr, 0),
      Self::UntypedPtr(_, ptr) => func.builder.ins().load(ir::types::I64, MemFlags::new(), *ptr, 8),
    }
  }

  pub fn const_ty(&self) -> Option<ValueType> {
    match self {
      Self::TypedConst(ty, _) => Some(*ty),
      Self::TypedDyn(ty, _) => Some(*ty),
      Self::TypedPtr(ty, _) => Some(*ty),
      _ => None,
    }
  }

  /// Returns the extended form of this value. This is used when passing a value
  /// into a union slot, or back to native code. The number of values may change
  /// depending on the type (so this works for function calls, but not for
  /// block arguments).
  fn to_extended_ir(&self, func: &mut FuncBuilder, len: Option<NonZero<u32>>) -> Slot {
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

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union), and when the number of
  /// values can change depending on the type (so this works for function
  /// arguments, but not for block arguments).
  fn to_compact_ir(&self, func: &mut FuncBuilder) -> Slot {
    match self {
      Self::TypedConst(_, items) => {
        if items.is_empty() {
          Slot::Empty
        } else if items.len() == 1 {
          let ir = func.builder.ins().iconst(ir::types::I64, items[0]);
          Slot::Single(ir)
        } else {
          let slot = Slot::new_multiple(&mut func.builder, items.len());

          for (i, v) in items.iter().enumerate() {
            let ir = func.builder.ins().iconst(ir::types::I64, *v);
            slot.set(&mut func.builder, i, ir);
          }

          slot
        }
      }
      Self::TypedDyn(_, slot) => *slot,
      Self::Untyped(_) => panic!("cannot convert an untyped value to compact form"),

      // FIXME: Add a `Slot` variant for this.
      Self::TypedPtr(ty, ptr) => {
        let len = ty.len(&func.ctx);
        let slot = Slot::new_multiple(&mut func.builder, len as usize);

        for i in 0..len {
          let v = func.builder.ins().load(ir::types::I64, MemFlags::new(), *ptr, i as i32 * 8);
          slot.set(&mut func.builder, i as usize, v);
        }

        slot
      }
      Self::UntypedPtr(_, _) => panic!("cannot convert an untyped value to compact form"),
    }
  }

  /// Returns the dynamic IR values for this RValue. This should be used
  /// whenever the length of arguments can change (for example in a function
  /// call). For block arguments, which must have a consistent size, use
  /// `to_sized_ir`.
  pub fn to_ir(&self, kind: ParamKind, func: &mut FuncBuilder) -> Slot {
    match kind {
      ParamKind::Compact => self.to_compact_ir(func),
      ParamKind::Extended(len) => self.to_extended_ir(func, Some(len)),
      ParamKind::Unsized => self.to_extended_ir(func, None),
    }
  }
}
