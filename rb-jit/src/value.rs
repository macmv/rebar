use cranelift::{
  codegen::ir,
  frontend::FunctionBuilder,
  prelude::{Block, InstBuilder},
};
use rb_mir::ast as mir;
use rb_typer::{Literal, Type};

#[derive(Debug, Clone, Copy)]
pub enum RValue {
  /// Nil stores no value.
  Nil,

  /// Stores a single i8 value.
  Bool(ir::Value),

  /// Stores a single i64 value.
  Int(ir::Value),

  /// Stores a user-defined function.
  UserFunction(mir::UserFunctionId),

  /// Stores a function pointer.
  Function(ir::Value),

  /// Stores a value that can change type at runtime.
  Dynamic(ir::Value, ir::Value),
}

mod ty {
  pub const NIL: i64 = 0;
  pub const BOOL: i64 = 1;
  pub const INT: i64 = 2;
  pub const FUNCTION: i64 = 3;
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
    let ty = match self {
      RValue::Nil => builder.ins().iconst(ir::types::I64, ty::NIL),
      RValue::Bool(_) => builder.ins().iconst(ir::types::I64, ty::BOOL),
      RValue::Int(_) => builder.ins().iconst(ir::types::I64, ty::INT),
      RValue::Function(_) => builder.ins().iconst(ir::types::I64, ty::FUNCTION),
      RValue::Dynamic(ty, _) => *ty,

      RValue::UserFunction(_) => todo!(),
    };

    let value = match self {
      // TODO: Optimize this into an undefined value.
      RValue::Nil => builder.ins().iconst(ir::types::I64, 0),
      RValue::Bool(v) => *v,
      RValue::Int(v) => *v,
      RValue::Function(v) => *v,
      RValue::Dynamic(_, v) => *v,

      RValue::UserFunction(_) => todo!(),
    };

    CompactValues::Two(ty, value)
  }

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union), and when the number of
  /// values can change depending on the type (so this works for function
  /// arguments, but not for block arguments).
  fn to_compact_ir(&self) -> CompactValues<ir::Value> {
    match self {
      RValue::Nil => panic!("cannot convert nil to compact value"),
      RValue::Bool(v) => CompactValues::One(*v),
      RValue::Int(v) => CompactValues::One(*v),
      RValue::Function(v) => CompactValues::One(*v),
      RValue::Dynamic(_, _) => panic!("dynamic values cannot be compact"),

      RValue::UserFunction(_) => todo!(),
    }
  }

  /// Returns the dynamic IR values for this RValue. This should be used
  /// whenever the length of arguments can change (for example in a function
  /// call). For block arguments, which must have a consistent size, use
  /// `to_sized_ir`.
  pub fn to_ir(&self, kind: ParamKind, builder: &mut FunctionBuilder) -> CompactValues<ir::Value> {
    match kind {
      ParamKind::Zero => CompactValues::None,
      ParamKind::Compact => self.to_compact_ir(),
      ParamKind::Extended => self.to_extended_ir(builder),
    }
  }

  // TODO: Need to actually use this with a function return.
  pub fn from_ir(ir: &[ir::Value], ty: &Type) -> RValue {
    match ParamKind::for_type(ty) {
      ParamKind::Zero => {
        assert_eq!(ir.len(), 0);
        RValue::Nil
      }
      ParamKind::Compact => {
        assert_eq!(ir.len(), 1);
        let v = ir[0];

        match ty {
          Type::Literal(Literal::Unit) => panic!("zero sized type shouldn't take up space"),
          Type::Literal(Literal::Bool) => RValue::Bool(v),
          Type::Literal(Literal::Int) => RValue::Int(v),
          Type::Function(_, _) => RValue::Function(v),
          _ => panic!("invalid type"),
        }
      }
      ParamKind::Extended => {
        assert_eq!(ir.len(), 2);

        RValue::Dynamic(ir[0], ir[1])
      }
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
