use cranelift::{codegen::ir, frontend::FunctionBuilder, prelude::InstBuilder};

#[derive(Clone, Copy)]
pub enum RValue {
  /// Nil stores no value.
  Nil,

  /// Stores a single i8 value.
  Bool(ir::Value),

  /// Stores a single i64 value.
  Int(ir::Value),

  /// Stores a function pointer.
  Function(ir::Value),
}

impl RValue {
  /// Returns the extended form of this value. This is used when passing a value
  /// into a union slot, or back to native code.
  pub fn extended_ir(&self, builder: &mut FunctionBuilder) -> (ir::Value, Option<ir::Value>) {
    let id = match self {
      RValue::Nil => 0,
      RValue::Bool(_) => 1,
      RValue::Int(_) => 2,
      RValue::Function(_) => 3,
    };
    let ty = builder.ins().iconst(ir::types::I8, id);

    let value = match self {
      RValue::Nil => None,
      RValue::Bool(v) => Some(*v),
      RValue::Int(v) => Some(*v),
      RValue::Function(v) => Some(*v),
    };

    (ty, value)
  }

  pub fn as_bool(&self) -> Option<ir::Value> {
    match self {
      RValue::Bool(v) => Some(*v),
      _ => None,
    }
  }
  pub fn as_int(&self) -> Option<ir::Value> {
    match self {
      RValue::Int(v) => Some(*v),
      _ => None,
    }
  }
  pub fn as_function(&self) -> Option<ir::Value> {
    match self {
      RValue::Function(v) => Some(*v),
      _ => None,
    }
  }
}
