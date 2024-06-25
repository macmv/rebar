use ::std::collections::HashMap;

mod core;
mod std;

use rb_typer::{Literal, Type};

pub struct Environment {
  pub names: HashMap<String, Function>,
}

pub struct Function {
  args: Vec<Type>,
  ret:  Type,

  imp: Box<dyn Fn(Vec<Value>) -> Value>,
}

impl Environment {
  fn empty() -> Self { Environment { names: HashMap::new() } }

  pub fn static_env(&self) -> rb_typer::Environment {
    rb_typer::Environment {
      names: self
        .names
        .iter()
        .map(|(k, v)| (k.clone(), Type::Function(v.args.clone(), Box::new(v.ret.clone()))))
        .collect(),
    }
  }
}

trait DynFunction {
  fn into_function(self) -> Function;
}

enum Value {
  Int(i64),
  Bool(bool),
  Unit,
}

impl Environment {
  pub fn add_fn(&mut self, name: impl Into<String>, function: impl DynFunction) {
    self.names.insert(name.into(), function.into_function());
  }
}

trait FunctionArg {
  fn static_type() -> Type;
  fn from_value(v: Value) -> Self;
}

trait FunctionRet {
  fn static_type() -> Type;
  fn into_value(self) -> Value;
}

// Write a macro to generate the following From for Function impls:
macro_rules! impl_from_function {
  ($($arg:ident),*) => {
    impl<R: FunctionRet + 'static, $($arg: FunctionArg + 'static),*> DynFunction for fn($($arg),*) -> R {
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
  fn static_type() -> Type { Type::Literal(Literal::Int) }
  fn from_value(v: Value) -> Self {
    match v {
      Value::Int(i) => i,
      _ => panic!("expected int"),
    }
  }
}
impl FunctionRet for i64 {
  fn static_type() -> Type { Type::Literal(Literal::Int) }
  fn into_value(self) -> Value { Value::Int(self) }
}

impl FunctionArg for bool {
  fn static_type() -> Type { Type::Literal(Literal::Bool) }
  fn from_value(v: Value) -> Self {
    match v {
      Value::Bool(i) => i,
      _ => panic!("expected bool"),
    }
  }
}
impl FunctionRet for bool {
  fn static_type() -> Type { Type::Literal(Literal::Bool) }
  fn into_value(self) -> Value { Value::Bool(self) }
}

impl FunctionRet for () {
  fn static_type() -> Type { Type::Literal(Literal::Unit) }
  fn into_value(self) -> Value { Value::Unit }
}

fn foo(a: i64, b: i64) -> i64 { a + b }

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn constructs_signatures() {
    let mut env = Environment::empty();

    env.add_fn("foo", (|a: i64, b: i64| -> i64 { a + b }) as fn(i64, i64) -> i64);
  }
}
