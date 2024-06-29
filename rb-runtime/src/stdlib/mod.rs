use ::std::{cell::RefCell, collections::HashMap};

mod core;
mod std;

use rb_jit::jit::RebarSlice;
use rb_mir::ast as mir;
use rb_typer::{Literal, Type};

pub struct Environment {
  pub names: HashMap<String, Function>,
  ids:       Vec<String>,
}

pub struct Function {
  args: Vec<Type>,
  ret:  Type,

  imp: Box<dyn Fn(Vec<Value>) -> Value>,
}

impl Environment {
  fn empty() -> Self { Environment { names: HashMap::new(), ids: vec![] } }

  pub(crate) fn dyn_call_ptr(self) -> fn(i64, *const RebarSlice) -> i64 {
    // This works pretty well, but it would be nice to support multithreading, and
    // multiple environments on one thread. Probably something for later though.
    thread_local! {
      static ENV: RefCell<Option<Environment>> = RefCell::new(None);
    }

    ENV.with(|env| {
      *env.borrow_mut() = Some(self);
    });

    |func, arg| {
      ENV.with(|env| {
        let env = env.borrow();
        let env = env.as_ref().unwrap();

        let f = &env.names[&env.ids[func as usize]].imp;

        let args = unsafe {
          let arg_value = &*arg;

          let mut args = vec![];
          for i in 0..arg_value.len() {
            let rb_value = arg_value.arg(i);
            let value = match rb_value.kind {
              0 => Value::Nil,
              1 => Value::Bool(rb_value.value != 0),
              2 => Value::Int(rb_value.value),
              v => panic!("unknown value kind {v}"),
            };

            args.push(value);
          }
          args
        };

        // TODO: And we need opposite shenanigans here to convert the return value.
        match f(args) {
          Value::Int(v) => v,
          Value::Bool(_) => 0,
          Value::Nil => 0,
        }
      })
    }
  }

  pub fn static_env(&self) -> rb_typer::Environment {
    rb_typer::Environment {
      names: self
        .names
        .iter()
        .map(|(k, v)| (k.clone(), Type::Function(v.args.clone(), Box::new(v.ret.clone()))))
        .collect(),
    }
  }

  pub fn mir_env(&self) -> rb_mir_lower::Env {
    rb_mir_lower::Env {
      functions: self
        .ids
        .iter()
        .enumerate()
        .map(|(k, v)| (v.clone(), mir::NativeFunctionId(k as u64)))
        .collect(),
    }
  }
}

pub trait DynFunction<T> {
  fn into_function(self) -> Function;
}

enum Value {
  Int(i64),
  Bool(bool),
  Nil,
}

impl Environment {
  pub fn add_fn<T>(&mut self, name: impl Into<String>, function: impl DynFunction<T>) {
    let name = name.into();
    self.names.insert(name.clone(), function.into_function());
    self.ids.push(name);
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
  fn into_value(self) -> Value { Value::Nil }
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
