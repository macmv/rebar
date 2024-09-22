use std::num::NonZero;

use cranelift::{
  codegen::ir,
  frontend::FunctionBuilder,
  prelude::{Block, InstBuilder},
};
use rb_typer::{Literal, Type};

#[derive(Debug, Clone)]
pub struct RValue {
  pub ty:     Value<ValueType>,
  pub values: Vec<Value<i64>>,
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

  /// Array is a bit mystical. The value that lives on the stack is always a
  /// pointer (arrays are thin pointers, so that they can be grown/shrunk
  /// easily). However, the layout of the memory on the heap is defined by a
  /// `DynamicValueType`. So, we don't need to store the array type here,
  /// as that's only required when looking up array elements (which is a
  /// specific operator, that can lookup the static type of the array
  /// directly).
  Array,
}

pub enum DynamicValueType {
  Const(ValueType),
  Union(Vec<ValueType>),
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
      ValueType::Array => 6,
    }
  }
}

impl TryFrom<i64> for ValueType {
  type Error = ();

  fn try_from(value: i64) -> Result<Self, Self::Error> {
    match value {
      0 => Ok(ValueType::Nil),
      1 => Ok(ValueType::Bool),
      2 => Ok(ValueType::Int),
      3 => Ok(ValueType::Function),
      4 => Ok(ValueType::UserFunction),
      5 => Ok(ValueType::String),
      6 => Ok(ValueType::Array),
      _ => Err(()),
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
  pub fn nil() -> Self { RValue { ty: Value::Const(ValueType::Nil), values: vec![] } }

  pub fn bool<T>(v: T) -> Self
  where
    Value<i64>: From<T>,
  {
    RValue { ty: Value::Const(ValueType::Bool), values: vec![Value::from(v)] }
  }

  pub fn int<T>(v: T) -> Self
  where
    Value<i64>: From<T>,
  {
    RValue { ty: Value::Const(ValueType::Int), values: vec![Value::from(v)] }
  }

  pub fn function<T>(v: T) -> Self
  where
    Value<i64>: From<T>,
  {
    RValue { ty: Value::Const(ValueType::Function), values: vec![Value::from(v)] }
  }

  pub fn string(v: &str) -> Self {
    RValue {
      ty:     Value::Const(ValueType::String),
      values: vec![Value::from(v.len() as i64), Value::from(v.as_ptr() as i64)],
    }
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
  /// The compact format. This will returns in a `CompactValues` containing one
  /// value.
  Compact,

  /// The extended format of a value. This includes an i64 at the start for the
  /// type, and then some number of values after that. Given the type, the
  /// number of following values is constant.
  ///
  /// The length given is the expected length of the value. When set (for direct
  /// rebar calls), an RValue must produce exactly that number of values. When
  /// unset (for dynamic rust calls), the RValue must produce exactly the
  /// number of values for the current value.
  Extended(Option<NonZero<u32>>),
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
  fn to_extended_ir(
    &self,
    builder: &mut FunctionBuilder,
    len: Option<NonZero<u32>>,
  ) -> Vec<ir::Value> {
    let mut ret = vec![];

    ret.push(self.ty.to_ir(builder));
    for v in &self.values {
      ret.push(v.to_ir(builder));
    }

    if let Some(l) = len {
      while ret.len() < l.get() as usize {
        ret.push(builder.ins().iconst(ir::types::I64, 0));
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
  fn to_compact_ir(&self, builder: &mut FunctionBuilder) -> Vec<ir::Value> {
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
  pub fn to_ir(&self, kind: ParamKind, builder: &mut FunctionBuilder) -> Vec<ir::Value> {
    match kind {
      ParamKind::Compact => self.to_compact_ir(builder),
      ParamKind::Extended(len) => self.to_extended_ir(builder, len),
    }
  }

  // TODO: Need to actually use this with a function return.
  pub fn from_ir(ir: &[ir::Value], ty: &Type) -> RValue {
    let dty = DynamicValueType::for_type(ty);
    assert_eq!(ir.len() as u32, dty.len(), "variable length mismatch");

    match dty {
      DynamicValueType::Const(ty) => RValue {
        ty:     Value::Const(ty),
        values: ir.iter().map(|v| Value::Dyn(*v)).collect::<Vec<_>>(),
      },

      DynamicValueType::Union(_) => RValue {
        ty:     Value::Dyn(ir[0]),
        values: ir[1..].iter().map(|v| Value::Dyn(*v)).collect::<Vec<_>>(),
      },
    }
  }
}

impl ValueType {
  pub fn len(&self) -> u32 {
    match self {
      ValueType::Nil => 0,
      ValueType::Int => 1,
      ValueType::Bool => 1,
      ValueType::String => 2, // Fat pointer.
      ValueType::Array => 1,  // Thin pointer.

      ValueType::Function => 1,
      ValueType::UserFunction => 1,
    }
  }
}

impl DynamicValueType {
  pub fn len(&self) -> u32 {
    match self {
      DynamicValueType::Const(ty) => ty.len(),
      DynamicValueType::Union(tys) => {
        let max = tys.iter().map(ValueType::len).max().unwrap();
        max + 1 // Add in the type tag
      }
    }
  }

  pub fn append_block_params(&self, builder: &mut FunctionBuilder, block: Block) {
    for _ in 0..self.len() {
      builder.append_block_param(block, ir::types::I64);
    }
  }

  pub fn param_kind(&self) -> ParamKind {
    match self {
      DynamicValueType::Const(_) => ParamKind::Compact,
      DynamicValueType::Union(_) => ParamKind::Extended(Some(NonZero::new(self.len()).unwrap())),
    }
  }

  pub fn for_type(ty: &Type) -> Self {
    match ty {
      Type::Literal(Literal::Unit) => DynamicValueType::Const(ValueType::Nil),
      Type::Literal(Literal::Int) => DynamicValueType::Const(ValueType::Int),
      Type::Literal(Literal::Bool) => DynamicValueType::Const(ValueType::Bool),
      Type::Literal(Literal::String) => DynamicValueType::Const(ValueType::String),
      Type::Array(_) => DynamicValueType::Const(ValueType::Array),
      Type::Union(tys) => DynamicValueType::Union(
        tys
          .iter()
          .flat_map(|ty| match DynamicValueType::for_type(ty) {
            DynamicValueType::Const(ty) => vec![ty],
            DynamicValueType::Union(tys) => tys,
          })
          .collect(),
      ),
      Type::Function(..) => todo!("function types to values"),
    }
  }
}
