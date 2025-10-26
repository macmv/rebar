use rb_hir::ast as hir;
use rb_mir::MirContext;
use rb_typer::Type;
use std::collections::HashMap;

use crate::{OwnedValue, Value};

pub struct Environment {
  pub static_functions: HashMap<String, Function>,
  pub ids:              Vec<String>,
  pub mir_ctx:          MirContext,
}

pub struct Function {
  pub args: Vec<Type>,
  pub ret:  Type,

  pub imp: Box<dyn Fn(Vec<Value>) -> OwnedValue>,
}

impl Environment {
  pub fn empty() -> Self {
    Environment {
      static_functions: HashMap::new(),
      ids:              vec![],
      mir_ctx:          MirContext::default(),
    }
  }

  pub fn add_fn<T>(&mut self, name: impl Into<String>, function: impl DynFunction<T>) {
    let name = name.into();
    self.static_functions.insert(name.clone(), function.into_function());
    self.ids.push(name);
  }
}

pub trait DynFunction<T> {
  fn into_function(self) -> Function;
}

trait FunctionArg {
  fn static_type() -> Type;
  fn from_value(v: Value) -> Self;
}

trait FunctionRet {
  fn static_type() -> Type;
  fn into_value(self) -> OwnedValue;
}

// Write a macro to generate the following From for Function impls:
macro_rules! impl_from_function {
  ($($arg:ident),*) => {
    impl<F, R, $($arg: FunctionArg + 'static),*> DynFunction<($($arg,)*)> for F
    where
      F: (Fn($($arg),*) -> R) + 'static,
      R: FunctionRet + 'static,
    {
      fn into_function(self) -> Function {
        Function {
          args: vec![$($arg::static_type()),*],
          ret:  R::static_type(),
          imp:  Box::new(move |args: Vec<Value>| {
            #[allow(unused_mut, unused_variables)]
            let mut iter = args.into_iter();
            self($($arg::from_value(iter.next().unwrap())),*).into_value()
          }),
        }
      }
    }
  };
}

impl_from_function!();
impl_from_function!(A);
impl_from_function!(A, B);
impl_from_function!(A, B, C);
impl_from_function!(A, B, C, D);

impl FunctionArg for i64 {
  fn static_type() -> Type { hir::PrimitiveType::I64.into() }
  fn from_value(v: Value) -> Self {
    match v {
      Value::Int(i) => i,
      _ => panic!("expected int"),
    }
  }
}
impl FunctionRet for i64 {
  fn static_type() -> Type { hir::PrimitiveType::I64.into() }
  fn into_value(self) -> OwnedValue { OwnedValue::Int(self) }
}

impl FunctionArg for bool {
  fn static_type() -> Type { hir::PrimitiveType::Bool.into() }
  fn from_value(v: Value) -> Self {
    match v {
      Value::Bool(i) => i,
      _ => panic!("expected bool"),
    }
  }
}
impl FunctionRet for bool {
  fn static_type() -> Type { hir::PrimitiveType::Bool.into() }
  fn into_value(self) -> OwnedValue { OwnedValue::Bool(self) }
}

impl FunctionArg for String {
  fn static_type() -> Type { hir::PrimitiveType::Str.into() }
  fn from_value(v: Value) -> Self {
    match v {
      Value::String(s) => s.into(),
      _ => panic!("expected string"),
    }
  }
}

impl FunctionRet for String {
  fn static_type() -> Type { hir::PrimitiveType::Str.into() }
  fn into_value(self) -> OwnedValue { OwnedValue::String(self) }
}

impl FunctionRet for () {
  fn static_type() -> Type { Type::unit() }
  fn into_value(self) -> OwnedValue { OwnedValue::Nil }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn constructs_signatures() {
    let mut env = Environment::empty();

    env.add_fn("foo", (|a: i64, b: i64| -> i64 { a + b }) as fn(i64, i64) -> i64);
  }
}
