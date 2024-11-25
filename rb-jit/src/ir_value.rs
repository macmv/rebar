use cranelift::{
  codegen::ir,
  prelude::{FunctionBuilder, InstBuilder},
};

use rb_value::ValueType;

#[derive(Debug, Clone, Copy)]
pub enum IRValue<T: AsIR> {
  Const(T),
  Dyn(ir::Value),
}

pub trait AsIR {
  fn ty(&self) -> ir::Type;
  fn as_i64(&self) -> i64;
}

impl<T: AsIR> From<T> for IRValue<T> {
  fn from(t: T) -> Self { IRValue::Const(t) }
}
impl<T: AsIR> From<ir::Value> for IRValue<T> {
  fn from(t: ir::Value) -> Self { IRValue::Dyn(t) }
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

impl<T: AsIR> IRValue<T> {
  pub fn to_ir(&self, builder: &mut FunctionBuilder) -> ir::Value {
    match self {
      IRValue::Const(t) => builder.ins().iconst(t.ty(), t.as_i64()),
      IRValue::Dyn(v) => *v,
    }
  }
}

impl<T: AsIR + Copy> IRValue<T> {
  pub fn as_const(&self) -> Option<T> {
    match self {
      IRValue::Const(t) => Some(*t),
      IRValue::Dyn(_) => None,
    }
  }
}
