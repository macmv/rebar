use std::num::NonZero;

use cranelift::{frontend::FunctionBuilder, prelude::Block};
use ir::AsIR;
use rb_typer::{Literal, Type};

mod arg;
mod array;
mod ir;

pub use arg::RebarArgs;
pub use array::RbArray;
pub use ir::IRValue;

pub struct IntrinsicImpls {
  pub call: fn(i64, *const RebarArgs, *mut RebarArgs),

  pub push_frame:          fn(),
  pub pop_frame:           fn(),
  pub gc_collect:          fn(),
  pub track:               fn(*const RebarArgs),
  pub string_append_value: fn(*const String, *const RebarArgs),
  pub string_append_str:   fn(*const String, *const u8, i64),
  pub string_new:          fn() -> *const String,
  pub array_new:           fn(i64, i64) -> *const u8,
  pub value_equals:        fn(*const RebarArgs, *const RebarArgs) -> i8,
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

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum DynamicValueType {
  Const(ValueType),

  /// Maximum size of any type that can be stored in this slot. NB: Doesn't
  /// include the type tag.
  Union(u32),
}

impl DynamicValueType {
  pub fn encode(&self) -> i64 {
    match self {
      DynamicValueType::Const(ty) => ty.as_i64(),
      DynamicValueType::Union(len) => -(*len as i64),
    }
  }

  pub fn decode(value: i64) -> Self {
    if value >= 0 {
      DynamicValueType::Const(ValueType::try_from(value).unwrap())
    } else {
      DynamicValueType::Union(-value as u32)
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

impl ValueType {
  pub fn len(&self) -> u32 {
    match self {
      ValueType::Nil => 0,
      ValueType::Int => 1,
      ValueType::Bool => 1,
      ValueType::String => 1,
      ValueType::Array => 1,

      ValueType::Function => 1,
      ValueType::UserFunction => 1,
    }
  }
}

impl DynamicValueType {
  pub fn len(&self) -> u32 {
    match self {
      DynamicValueType::Const(ty) => ty.len(),
      DynamicValueType::Union(len) => *len + 1, // Add 1 for the type tag.
    }
  }

  pub fn append_block_params(&self, builder: &mut FunctionBuilder, block: Block) {
    for _ in 0..self.len() {
      builder.append_block_param(block, cranelift::codegen::ir::types::I64);
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
          .map(|ty| match DynamicValueType::for_type(ty) {
            DynamicValueType::Const(ty) => ty.len(),
            DynamicValueType::Union(len) => len,
          })
          .max()
          .unwrap(),
      ),
      Type::Function(..) => todo!("function types to values"),
    }
  }
}
