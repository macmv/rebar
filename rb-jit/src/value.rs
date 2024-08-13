use cranelift::{
  codegen::ir,
  frontend::FunctionBuilder,
  prelude::{Block, InstBuilder},
};
use rb_typer::{Literal, Type};

#[derive(Debug, Clone, Copy)]
pub struct RValue {
  pub ty:    Value<ValueType>,
  pub value: Value<i64>,
}

#[derive(Debug, Clone, Copy)]
pub enum Value<T: AsIR> {
  Const(T),
  Dyn(ir::Value),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueType {
  Nil,
  Bool,
  Int,
  Function,
  UserFunction, // FIXME: Fix names
  String,
}

impl<T: AsIR> From<T> for Value<T> {
  fn from(t: T) -> Self { Value::Const(t) }
}
impl<T: AsIR> From<ir::Value> for Value<T> {
  fn from(t: ir::Value) -> Self { Value::Dyn(t) }
}

pub trait AsIR {
  fn ty(&self) -> ir::Type;
  fn as_i64(&self) -> i64;
}

impl AsIR for i64 {
  fn ty(&self) -> ir::Type { ir::types::I64 }
  fn as_i64(&self) -> i64 { *self }
}

impl AsIR for i8 {
  fn ty(&self) -> ir::Type { ir::types::I8 }
  fn as_i64(&self) -> i64 { (*self).into() }
}

impl AsIR for ValueType {
  fn ty(&self) -> ir::Type { ir::types::I64 }

  fn as_i64(&self) -> i64 {
    match self {
      ValueType::Nil => 0,
      ValueType::Bool => 1,
      ValueType::Int => 2,
      ValueType::Function => 3,
      ValueType::UserFunction => 4,
      ValueType::String => 5,
    }
  }
}

impl<T: AsIR> Value<T> {
  pub fn to_ir(&self, builder: &mut FunctionBuilder) -> ir::Value {
    match self {
      Value::Const(t) => builder.ins().iconst(t.ty(), t.as_i64()),
      Value::Dyn(v) => *v,
    }
  }
}

impl<T: AsIR + Copy> Value<T> {
  pub fn as_const(&self) -> Option<T> {
    match self {
      Value::Const(t) => Some(*t),
      Value::Dyn(_) => None,
    }
  }
}

impl RValue {
  pub fn nil() -> Self { RValue { ty: Value::Const(ValueType::Nil), value: Value::Const(0) } }

  pub fn bool<T>(v: T) -> Self
  where
    Value<i64>: From<T>,
  {
    RValue { ty: Value::Const(ValueType::Bool), value: Value::from(v) }
  }

  pub fn int<T>(v: T) -> Self
  where
    Value<i64>: From<T>,
  {
    RValue { ty: Value::Const(ValueType::Int), value: Value::from(v) }
  }

  pub fn function<T>(v: T) -> Self
  where
    Value<i64>: From<T>,
  {
    RValue { ty: Value::Const(ValueType::Function), value: Value::from(v) }
  }

  pub fn string<T>(v: T) -> Self
  where
    Value<i64>: From<T>,
  {
    RValue { ty: Value::Const(ValueType::String), value: Value::from(v) }
  }
}

#[derive(Clone, Copy, Debug)]
pub enum CompactValues<T> {
  None,
  One(T),
  Two(T, T),
}

/// The parameter kind for passing a value around. This is most commonly used
/// for local variables. Compact values have their static type known, wheras
/// extended types have a static type that is a union or unknown.
#[derive(Clone, Copy)]
pub enum ParamKind {
  /// This parameter doesn't require any information at runtime. Everything
  /// there is to know about this parameter is in its type. Most commonly,
  /// this will show up for `nil`, but it can show up for other zero-sized
  /// types.
  Zero,

  /// The compact format. This will returns in a `CompactValues` containing one
  /// value.
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
  /// into a union slot, or back to native code. The number of values may change
  /// depending on the type (so this works for function calls, but not for
  /// block arguments).
  fn to_extended_ir(&self, builder: &mut FunctionBuilder) -> CompactValues<ir::Value> {
    let ty = self.ty.to_ir(builder);
    let val = self.value.to_ir(builder);

    CompactValues::Two(ty, val)
  }

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union), and when the number of
  /// values can change depending on the type (so this works for function
  /// arguments, but not for block arguments).
  fn to_compact_ir(&self, builder: &mut FunctionBuilder) -> CompactValues<ir::Value> {
    let val = self.value.to_ir(builder);

    CompactValues::One(val)
  }

  /// Returns the dynamic IR values for this RValue. This should be used
  /// whenever the length of arguments can change (for example in a function
  /// call). For block arguments, which must have a consistent size, use
  /// `to_sized_ir`.
  pub fn to_ir(&self, kind: ParamKind, builder: &mut FunctionBuilder) -> CompactValues<ir::Value> {
    match kind {
      ParamKind::Zero => CompactValues::None,
      ParamKind::Compact => self.to_compact_ir(builder),
      ParamKind::Extended => self.to_extended_ir(builder),
    }
  }

  // TODO: Need to actually use this with a function return.
  pub fn from_ir(ir: &[ir::Value], ty: &Type) -> RValue {
    match ParamKind::for_type(ty) {
      ParamKind::Zero => {
        assert_eq!(ir.len(), 0);
        RValue::nil()
      }
      ParamKind::Compact => {
        assert_eq!(ir.len(), 1);
        let v = ir[0];

        match ty {
          Type::Literal(Literal::Unit) => panic!("zero sized type shouldn't take up space"),
          Type::Literal(Literal::Bool) => RValue::bool(v),
          Type::Literal(Literal::Int) => RValue::int(v),
          Type::Function(_, _) => RValue::function(v),
          _ => panic!("invalid type"),
        }
      }
      ParamKind::Extended => {
        assert_eq!(ir.len(), 2);

        RValue { ty: ir[0].into(), value: ir[1].into() }
      }
    }
  }
}

impl ParamKind {
  pub fn append_block_params(&self, builder: &mut FunctionBuilder, block: Block) {
    match self {
      ParamKind::Zero => {}
      ParamKind::Compact => {
        builder.append_block_param(block, ir::types::I64);
      }
      ParamKind::Extended => {
        builder.append_block_param(block, ir::types::I64);
        builder.append_block_param(block, ir::types::I64);
      }
    }
  }

  pub fn for_type(ty: &Type) -> Self {
    match ty {
      Type::Union(_) => ParamKind::Extended,
      Type::Literal(Literal::Unit) => ParamKind::Zero,
      _ => ParamKind::Compact,
    }
  }
}
