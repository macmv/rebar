use std::num::NonZero;

use crate::slot::Slot;

use super::IRValue;
use cranelift::prelude::FunctionBuilder;
use rb_mir::MirContext;
use rb_typer::Type;
use rb_value::{DynamicValueType, ParamKind, ValueType};

#[derive(Debug, Clone)]
pub struct RValue {
  pub ty:     IRValue<ValueType>,
  pub values: Vec<IRValue<i64>>,
}

impl RValue {
  pub fn nil() -> Self { RValue { ty: IRValue::Const(ValueType::Nil), values: vec![] } }

  pub fn bool<T>(v: T) -> Self
  where
    IRValue<i64>: From<T>,
  {
    RValue { ty: IRValue::Const(ValueType::Bool), values: vec![IRValue::from(v)] }
  }

  pub fn int<T>(v: T) -> Self
  where
    IRValue<i64>: From<T>,
  {
    RValue { ty: IRValue::Const(ValueType::Int), values: vec![IRValue::from(v)] }
  }

  pub fn function<T>(v: T) -> Self
  where
    IRValue<i64>: From<T>,
  {
    RValue { ty: IRValue::Const(ValueType::Function), values: vec![IRValue::from(v)] }
  }
}

impl RValue {
  /// Returns the extended form of this value. This is used when passing a value
  /// into a union slot, or back to native code. The number of values may change
  /// depending on the type (so this works for function calls, but not for
  /// block arguments).
  fn to_extended_ir(&self, builder: &mut FunctionBuilder, len: Option<NonZero<u32>>) -> Slot {
    let ty_ir = self.ty.to_ir(builder);

    let len = match len {
      Some(v) => v.get() as usize,
      None => self.values.len() + 1,
    };

    assert!(self.values.len() + 1 <= len, "value {self:?} cannot fit into slot of length {len:?}");

    if len == 1 {
      Slot::Single(ty_ir)
    } else {
      let slot = Slot::new_multiple(builder, len);

      slot.set(builder, 0, ty_ir);

      for (i, v) in self.values.iter().enumerate() {
        let ir = v.to_ir(builder);
        slot.set(builder, i + 1, ir);
      }

      slot
    }
  }

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union), and when the number of
  /// values can change depending on the type (so this works for function
  /// arguments, but not for block arguments).
  fn to_compact_ir(&self, builder: &mut FunctionBuilder) -> Slot {
    match self.values.as_slice() {
      [] => Slot::Empty,
      [v] => Slot::Single(v.to_ir(builder)),
      _ => {
        let slot = Slot::new_multiple(builder, self.values.len());

        for (i, v) in self.values.iter().enumerate() {
          let ir = v.to_ir(builder);
          slot.set(builder, i, ir);
        }

        slot
      }
    }
  }

  /// Returns the dynamic IR values for this RValue. This should be used
  /// whenever the length of arguments can change (for example in a function
  /// call). For block arguments, which must have a consistent size, use
  /// `to_sized_ir`.
  pub fn to_ir(&self, kind: ParamKind, builder: &mut FunctionBuilder) -> Slot {
    match kind {
      ParamKind::Compact => self.to_compact_ir(builder),
      ParamKind::Extended(len) => self.to_extended_ir(builder, Some(len)),
      ParamKind::Unsized => self.to_extended_ir(builder, None),
    }
  }

  // TODO: Need to actually use this with a function return.
  #[track_caller]
  pub fn from_ir(ctx: &MirContext, ir: &[cranelift::codegen::ir::Value], ty: &Type) -> RValue {
    let dty = DynamicValueType::for_type(ctx, ty);
    assert_eq!(ir.len() as u32, dty.len(ctx), "variable length mismatch");

    match dty {
      DynamicValueType::Const(ty) => RValue {
        ty:     IRValue::Const(ty),
        values: ir.iter().map(|v| IRValue::Dyn(*v)).collect::<Vec<_>>(),
      },

      DynamicValueType::Union(_) => RValue {
        ty:     IRValue::Dyn(ir[0]),
        values: ir[1..].iter().map(|v| IRValue::Dyn(*v)).collect::<Vec<_>>(),
      },
    }
  }
}
