use std::num::NonZero;

use super::IRValue;
use cranelift::prelude::{FunctionBuilder, InstBuilder};
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
  fn to_extended_ir(
    &self,
    builder: &mut FunctionBuilder,
    len: Option<NonZero<u32>>,
  ) -> Vec<cranelift::codegen::ir::Value> {
    let mut ret = vec![];

    ret.push(self.ty.to_ir(builder));
    for v in &self.values {
      ret.push(v.to_ir(builder));
    }

    if let Some(l) = len {
      while ret.len() < l.get() as usize {
        ret.push(builder.ins().iconst(cranelift::codegen::ir::types::I64, 0));
      }

      assert_eq!(
        ret.len(),
        l.get() as usize,
        "value {self:?} cannot fit into slot of length {len:?}"
      );
    }

    ret
  }

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union), and when the number of
  /// values can change depending on the type (so this works for function
  /// arguments, but not for block arguments).
  fn to_compact_ir(&self, builder: &mut FunctionBuilder) -> Vec<cranelift::codegen::ir::Value> {
    let mut ret = vec![];

    for v in &self.values {
      ret.push(v.to_ir(builder));
    }

    ret
  }

  /// Returns the dynamic IR values for this RValue. This should be used
  /// whenever the length of arguments can change (for example in a function
  /// call). For block arguments, which must have a consistent size, use
  /// `to_sized_ir`.
  pub fn to_ir(
    &self,
    kind: ParamKind,
    builder: &mut FunctionBuilder,
  ) -> Vec<cranelift::codegen::ir::Value> {
    match kind {
      ParamKind::Compact => self.to_compact_ir(builder),
      ParamKind::Extended(len) => self.to_extended_ir(builder, len),
    }
  }

  // TODO: Need to actually use this with a function return.
  pub fn from_ir(ir: &[cranelift::codegen::ir::Value], ty: &Type) -> RValue {
    let dty = DynamicValueType::for_type(ty);
    assert_eq!(ir.len() as u32, dty.len(), "variable length mismatch");

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
