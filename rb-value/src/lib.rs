use std::num::NonZero;

use rb_mir::{MirContext, ast::StructId};
use rb_typer::Type;

mod arg;
mod array;

pub use arg::RebarArgs;
pub use array::RbVec;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueType {
  Nil,
  Bool,
  Int,
  Function,
  UserFunction, // FIXME: Fix names
  Slice,

  /// Array is a bit mystical. The value that lives on the stack is always a
  /// pointer (arrays are thin pointers, so that they can be grown/shrunk
  /// easily). However, the layout of the memory on the heap is defined by a
  /// `DynamicValueType`. So, we don't need to store the array type here,
  /// as that's only required when looking up array elements (which is a
  /// specific operator, that can lookup the static type of the array
  /// directly).
  Array,

  Struct(StructId),
}

impl ValueType {
  pub fn as_i64(&self) -> i64 {
    match self {
      ValueType::Nil => 0,
      ValueType::Bool => 1,
      ValueType::Int => 2,
      ValueType::Function => 3,
      ValueType::UserFunction => 4,
      ValueType::Slice => 5,
      ValueType::Array => 6,

      // Leave the first 32 ids for the built-in types.
      ValueType::Struct(id) => id.0 as i64 + 32,
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
      5 => Ok(ValueType::Slice),
      6 => Ok(ValueType::Array),

      v if v >= 32 => Ok(ValueType::Struct(StructId(v as u64 - 32))),

      _ => Err(()),
    }
  }
}

/// The parameter kind for passing a value around. This is most commonly used
/// for local variables. Compact values have their static type known, wheras
/// extended types have a static type that is a union or unknown.
#[derive(Clone, Copy)]
pub enum ParamKind {
  Compact,

  /// The extended format of a value. This includes an i64 at the start for the
  /// type, and then some number of values after that. Given the type, the
  /// number of following values is constant.
  ///
  /// The length given is the expected length of the value. When set (for direct
  /// rebar calls), an RValue must produce exactly that number of values. When
  /// unset (for dynamic rust calls), the RValue must produce exactly the
  /// number of values for the current value.
  Extended(NonZero<u32>),

  /// Used when passing a value to rust, where the length will be inferred by
  /// the parser.
  Unsized,
}

impl ValueType {
  pub fn len(&self, ctx: &MirContext) -> u32 {
    match self {
      ValueType::Nil => 0,
      ValueType::Int => 1,
      ValueType::Bool => 1,
      ValueType::Slice => 2,
      ValueType::Array => 1,

      ValueType::Function => 1,
      ValueType::UserFunction => 1,

      ValueType::Struct(id) => {
        ctx.structs[id].fields.iter().map(|f| ValueType::for_type(ctx, &f.1).len(ctx)).sum()
      }
    }
  }

  pub fn for_type(ctx: &MirContext, ty: &Type) -> Self {
    match ty {
      Type::Array(_) => ValueType::Array,
      Type::Primitive(rb_hir::ast::PrimitiveType::Str) => ValueType::Slice,
      Type::Primitive(_) => ValueType::Int,
      Type::Union(_) => todo!("unions in backend"),
      Type::Function(..) => todo!("function types to values"),

      // This requires some type of MIR-context to resolve this.
      Type::Struct(path) => {
        let id = ctx.struct_paths[path];
        ValueType::Struct(id)
      }

      _ => todo!(),
    }
  }
}
