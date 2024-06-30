use cranelift::{
  codegen::ir,
  frontend::FunctionBuilder,
  prelude::{Block, InstBuilder},
};
use rb_typer::{Literal, Type};

#[derive(Debug, Clone, Copy)]
pub enum RValue {
  /// Nil stores no value.
  Nil,

  /// Stores a single i8 value.
  Bool(ir::Value),

  /// Stores a single i64 value.
  Int(ir::Value),

  /// Stores a function pointer.
  Function(ir::Value),

  /// Stores a value that can change type at runtime.
  Dynamic(ir::Value, ir::Value),
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

/// The parameter kind for passing a value around. This is most commonly used
/// for local variables. Compact values have their static type known, wheras
/// extended types have a static type that is a union or unknown.
#[derive(Clone, Copy)]
pub enum ParamKind {
  /// The compact format. This will returns in a `CompactValues` containing zero
  /// or one values. Zero values will show up for a `nil`, and one value will
  /// show up for everything else.
  Compact,

  /// The extended format. This will always return one or two `CompactValues`.
  /// Nil will produce a single value, and everything else will produce two
  /// values.
  Extended,
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

  pub fn first(self) -> Option<T> {
    match self {
      CompactValues::None => None,
      CompactValues::One(a) => Some(a),
      CompactValues::Two(a, _) => Some(a),
    }
  }

  pub fn second(self) -> Option<T> {
    match self {
      CompactValues::None => None,
      CompactValues::One(_) => None,
      CompactValues::Two(_, b) => Some(b),
    }
  }

  pub fn len(&self) -> u32 {
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
    let ty = match self {
      RValue::Nil => builder.ins().iconst(ir::types::I64, 0),
      RValue::Bool(_) => builder.ins().iconst(ir::types::I64, 1),
      RValue::Int(_) => builder.ins().iconst(ir::types::I64, 2),
      RValue::Function(_) => builder.ins().iconst(ir::types::I64, 3),
      RValue::Dynamic(ty, _) => *ty,
    };

    let value = match self {
      RValue::Nil => None,
      RValue::Bool(v) => Some(*v),
      RValue::Int(v) => Some(*v),
      RValue::Function(v) => Some(*v),
      RValue::Dynamic(_, v) => Some(*v),
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
      RValue::Dynamic(ty, v) => CompactValues::Two(*ty, *v),
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
      CompactValues::Two(ty, v) => RValue::Dynamic(ty, v),
    }
  }

  pub fn to_ir(&self, kind: ParamKind, builder: &mut FunctionBuilder) -> CompactValues<ir::Value> {
    match kind {
      ParamKind::Compact => self.to_compact_ir(),
      ParamKind::Extended => self.to_extended_ir(builder),
    }
  }

  /// Returns an IR value that is always exactly `size` elements. This should
  /// only be used for conditionals, where blocks need an exact number of
  /// arguments. Prefer `to_ir` when possible.
  pub fn to_sized_ir(
    &self,
    size: ParamSize,
    builder: &mut FunctionBuilder,
  ) -> CompactValues<ir::Value> {
    match size {
      ParamSize::Unit => self.to_compact_ir(),
      ParamSize::Single => self.to_compact_ir(),
      ParamSize::Double => match self.to_extended_ir(builder) {
        CompactValues::None => unreachable!(),
        CompactValues::One(ty) => CompactValues::Two(ty, builder.ins().iconst(ir::types::I64, 0)),
        CompactValues::Two(ty, v) => CompactValues::Two(ty, v),
      },
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

  pub fn for_type(ty: &Type) -> ParamSize {
    match ty {
      Type::Literal(Literal::Unit) => ParamSize::Unit,
      Type::Union(_) => ParamSize::Double,
      _ => ParamSize::Single,
    }
  }
}

impl ParamKind {
  pub fn for_type(ty: &Type) -> Self {
    match ty {
      Type::Union(_) => ParamKind::Extended,
      _ => ParamKind::Compact,
    }
  }
}
