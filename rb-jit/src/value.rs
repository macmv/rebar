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

#[derive(Clone, Copy)]
pub enum CompactValues<T> {
  None,
  One(T),
  Two(T, T),
}

impl<T> CompactValues<T> {
  pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> CompactValues<U> {
    match self {
      CompactValues::None => CompactValues::None,
      CompactValues::One(a) => CompactValues::One(f(a)),
      CompactValues::Two(a, b) => CompactValues::Two(f(a), f(b)),
    }
  }

  pub fn with_slice<R>(self, f: impl FnOnce(&[T]) -> R) -> R {
    match self {
      CompactValues::None => f(&[]),
      CompactValues::One(a) => f(&[a]),
      CompactValues::Two(a, b) => f(&[a, b]),
    }
  }
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

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union).
  pub fn to_ir(&self) -> CompactValues<ir::Value> {
    match self {
      RValue::Nil => CompactValues::None,
      RValue::Bool(v) => CompactValues::One(*v),
      RValue::Int(v) => CompactValues::One(*v),
      RValue::Function(v) => CompactValues::One(*v),
    }
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
