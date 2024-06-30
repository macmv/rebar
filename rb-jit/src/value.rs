use cranelift::{
  codegen::ir,
  frontend::FunctionBuilder,
  prelude::{Block, InstBuilder},
};
use rb_typer::{Literal, Type};

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

#[derive(Clone, Copy)]
pub enum ParamSize {
  Unit,
  Single,
  Double,
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

  pub fn first(self) -> T {
    match self {
      CompactValues::None => panic!("cannot call first() on empty compact values"),
      CompactValues::One(a) => a,
      CompactValues::Two(a, _) => a,
    }
  }

  pub fn len(&self) -> usize {
    match self {
      CompactValues::None => 0,
      CompactValues::One(_) => 1,
      CompactValues::Two(_, _) => 2,
    }
  }
}

impl<T: Copy> CompactValues<T> {
  pub fn from_slice(elems: &[T]) -> Self {
    match elems {
      [] => CompactValues::None,
      [a] => CompactValues::One(*a),
      [a, b] => CompactValues::Two(*a, *b),
      _ => panic!("expected 0..=2 values"),
    }
  }
}

impl RValue {
  /// Returns the extended form of this value. This is used when passing a value
  /// into a union slot, or back to native code.
  fn to_extended_ir(&self, builder: &mut FunctionBuilder) -> CompactValues<ir::Value> {
    let id = match self {
      RValue::Nil => 0,
      RValue::Bool(_) => 1,
      RValue::Int(_) => 2,
      RValue::Function(_) => 3,
    };
    let ty = builder.ins().iconst(ir::types::I64, id);

    let value = match self {
      RValue::Nil => None,
      RValue::Bool(v) => Some(*v),
      RValue::Int(v) => Some(*v),
      RValue::Function(v) => Some(*v),
    };

    match value {
      None => CompactValues::One(ty),
      Some(v) => CompactValues::Two(ty, v),
    }
  }

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union).
  fn to_compact_ir(&self) -> CompactValues<ir::Value> {
    match self {
      RValue::Nil => CompactValues::None,
      RValue::Bool(v) => CompactValues::One(*v),
      RValue::Int(v) => CompactValues::One(*v),
      RValue::Function(v) => CompactValues::One(*v),
    }
  }

  pub fn from_compact_ir(ir: CompactValues<ir::Value>, ty: &Type) -> Self {
    match ir {
      CompactValues::None => RValue::Nil,
      CompactValues::One(v) => match ty {
        Type::Literal(Literal::Bool) => RValue::Bool(v),
        Type::Literal(Literal::Int) => RValue::Int(v),
        Type::Function(_, _) => RValue::Function(v),
        _ => panic!("invalid type"),
      },
      _ => panic!("expected 0 or 1 values"),
    }
  }

  pub fn to_sized_ir(
    &self,
    size: ParamSize,
    builder: &mut FunctionBuilder,
  ) -> CompactValues<ir::Value> {
    match size {
      ParamSize::Unit => self.to_compact_ir(),
      ParamSize::Single => self.to_compact_ir(),
      ParamSize::Double => self.to_extended_ir(builder),
    }
  }

  pub fn from_sized_ir(ir: &[ir::Value], ty: &Type) -> RValue {
    let values = CompactValues::from_slice(ir);

    RValue::from_compact_ir(values, ty)
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

impl ParamSize {
  pub fn append_block_params(&self, builder: &mut FunctionBuilder, block: Block) {
    match self {
      ParamSize::Unit => {}
      ParamSize::Single => {
        builder.append_block_param(block, ir::types::I64);
      }
      ParamSize::Double => {
        builder.append_block_param(block, ir::types::I64);
        builder.append_block_param(block, ir::types::I64);
      }
    }
  }

  pub fn len(&self) -> u32 {
    match self {
      ParamSize::Unit => 0,
      ParamSize::Single => 1,
      ParamSize::Double => 2,
    }
  }
}
