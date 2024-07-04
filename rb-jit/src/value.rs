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

#[derive(Clone, Copy)]
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
  /// into a union slot, or back to native code. The number of values may change
  /// depending on the type (so this works for function calls, but not for
  /// block arguments).
  fn to_extended_ir(&self, builder: &mut FunctionBuilder) -> CompactValues<ir::Value> {
    let ty = match self {
      RValue::Nil => builder.ins().iconst(ir::types::I64, 0),
      RValue::Bool(_) => builder.ins().iconst(ir::types::I64, 1),
      RValue::Int(_) => builder.ins().iconst(ir::types::I64, 2),
      RValue::Function(_) => builder.ins().iconst(ir::types::I64, 3),
      RValue::Dynamic(ty, _) => *ty,

      RValue::UserFunction(_) => todo!(),
    };

    let value = match self {
      RValue::Nil => None,
      RValue::Bool(v) => Some(*v),
      RValue::Int(v) => Some(*v),
      RValue::Function(v) => Some(*v),
      RValue::Dynamic(_, v) => Some(*v),

      RValue::UserFunction(_) => todo!(),
    };

    match value {
      None => CompactValues::One(ty),
      Some(v) => CompactValues::Two(ty, v),
    }
  }

  /// Returns the compact for of this value. This is used wherever the static
  /// type of the value is simple (ie, not a union), and when the number of
  /// values can change depending on the type (so this works for function
  /// arguments, but not for block arguments).
  fn to_compact_ir(&self) -> CompactValues<ir::Value> {
    match self {
      RValue::Nil => CompactValues::None,
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
      ParamKind::Compact => self.to_compact_ir(),
      ParamKind::Extended => self.to_extended_ir(builder),
    }
  }

  // TODO: Need to actually use this with a function return.
  pub fn from_ir(ir: &[ir::Value], ty: &Type) -> RValue {
    match /*ParamKind::for_type(ty)*/ ParamKind::Extended {
      ParamKind::Compact => match ty {
        Type::Literal(Literal::Unit) => {
          assert_eq!(ir.len(), 0);
          RValue::Nil
        }
        _ => {
          assert_eq!(ir.len(), 1);
          let v = ir[0];

          match ty {
            Type::Literal(Literal::Bool) => RValue::Bool(v),
            Type::Literal(Literal::Int) => RValue::Int(v),
            Type::Function(_, _) => RValue::Function(v),
            _ => panic!("invalid type"),
          }
        }
      },
      ParamKind::Extended => {
        assert_eq!(ir.len(), 2);
        RValue::Dynamic(ir[0], ir[1])
      }
    }
  }

  /// Returns an IR value that has a consistent number of values. This means
  /// passing in `ParamKind::Extended` will always return two values. This
  /// should only be used in places where consistent sizes are required, ie
  /// the block arguments for a conditional. Prefer `to_ir` when possible.
  pub fn to_sized_ir(
    &self,
    kind: ParamKind,
    builder: &mut FunctionBuilder,
  ) -> CompactValues<ir::Value> {
    match kind {
      ParamKind::Compact => self.to_compact_ir(),
      ParamKind::Extended => match self.to_extended_ir(builder) {
        CompactValues::None => unreachable!(),
        CompactValues::One(ty) => CompactValues::Two(ty, builder.ins().iconst(ir::types::I64, 0)),
        CompactValues::Two(ty, v) => CompactValues::Two(ty, v),
      },
    }
  }

  /// Creates an RValue from a fixed sized list of IR values. This should be
  /// used for returns from blocks, where the size is fixed.
  pub fn from_sized_ir(ir: &[ir::Value], ty: &Type) -> RValue {
    let kind = ParamKind::for_type(ty);
    match kind {
      ParamKind::Compact => match ty {
        Type::Literal(Literal::Unit) => assert_eq!(ir.len(), 0),
        _ => assert_eq!(ir.len(), 1),
      },
      ParamKind::Extended => assert!(ir.len() == 2),
    }

    match kind {
      ParamKind::Compact => match ty {
        Type::Literal(Literal::Unit) => RValue::Nil,
        Type::Literal(Literal::Bool) => RValue::Bool(ir[0]),
        Type::Literal(Literal::Int) => RValue::Int(ir[0]),
        Type::Function(_, _) => RValue::Function(ir[0]),
        _ => panic!("invalid type"),
      },
      ParamKind::Extended => RValue::Dynamic(ir[0], ir[1]),
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
  pub fn block_params(builder: &mut FunctionBuilder, ty: &Type, block: Block) -> Self {
    let kind = ParamKind::for_type(ty);

    match kind {
      ParamKind::Compact => match ty {
        Type::Literal(Literal::Unit) => {}
        _ => {
          builder.append_block_param(block, ir::types::I64);
        }
      },
      ParamKind::Extended => {
        builder.append_block_param(block, ir::types::I64);
        builder.append_block_param(block, ir::types::I64);
      }
    }

    kind
  }

  pub fn for_type(ty: &Type) -> Self {
    match ty {
      Type::Union(_) => ParamKind::Extended,
      _ => ParamKind::Compact,
    }
  }
}
