use ::std::{cell::RefCell, collections::HashMap};

mod core;
mod std;

use rb_jit::{jit::RebarArgs, value::ParamKind};
use rb_mir::ast::{self as mir};
use rb_typer::{Literal, Type};

pub struct Environment {
  pub static_functions: HashMap<String, Function>,
  ids:                  Vec<String>,
}

pub struct Function {
  args: Vec<Type>,
  ret:  Type,

  imp: Box<dyn Fn(Vec<Value>) -> Value>,
}

impl Environment {
  fn empty() -> Self { Environment { static_functions: HashMap::new(), ids: vec![] } }

  pub(crate) fn dyn_call_ptr(self) -> fn(i64, *const RebarArgs) -> i64 {
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

        let f = &env.static_functions[&env.ids[func as usize]];

        let args = unsafe {
          let arg_value = &*arg;

          let mut args = vec![];
          let mut offset = 0;
          for ty in f.args.iter() {
            let param_kind = ParamKind::for_type(ty);

            let value = match param_kind {
              ParamKind::Compact => {
                // A nil won't take up any slots, so we must check for that to avoid reading out
                // of bounds.
                match ty {
                  Type::Literal(Literal::Unit) => Value::Nil,
                  _ => {
                    // Now that we know its not a unit, we can safely read the value. The value
                    // will always take up 8 bytes, even if less bytes are used.
                    let value = *arg_value.arg(offset);
                    offset += 1;

                    match ty {
                      // Booleans only use 8 bits, so cast the value to a u8 and just compare that.
                      Type::Literal(Literal::Bool) => Value::Bool(value as u8 != 0),
                      Type::Literal(Literal::Int) => Value::Int(value),
                      v => unimplemented!("{v:?}"),
                    }
                  }
                }
              }
              ParamKind::Extended => {
                // A nil will only take up one slot, so we must check for that to avoid reading
                // out of bounds.
                let dyn_ty = *arg_value.arg(offset);
                offset += 1;

                match dyn_ty {
                  0 => Value::Nil,
                  _ => {
                    // `offset` was just incremented, so read the next slot to get the actual
                    // value.
                    let value = *arg_value.arg(offset);
                    offset += 1;

                    match dyn_ty {
                      // Booleans only use 8 bits, so cast the value to a u8 and just compare that.
                      1 => Value::Bool(value as u8 != 0),
                      2 => Value::Int(value),
                      v => panic!("unknown value kind {v}"),
                    }
                  }
                }
              }
            };

            args.push(value);
          }
          args
        };

        let ret = (f.imp)(args);

        // TODO: Native functions must always return a value, but the runtime isn't
        // going to assume that. Need to figure out a way to return something
        // sane here.
        match f.ret {
          Type::Literal(Literal::Unit) => 0,
          Type::Literal(Literal::Bool) => ret.as_bool() as i64,
          Type::Literal(Literal::Int) => ret.as_int(),
          ref v => unimplemented!("{v:?}"),
        }
      })
    }
  }

  pub fn static_env(&self) -> rb_typer::Environment {
    rb_typer::Environment {
      names: self
        .static_functions
        .iter()
        .map(|(k, v)| (k.clone(), Type::Function(v.args.clone(), Box::new(v.ret.clone()))))
        .collect(),
    }
  }

  pub fn mir_env(&self) -> rb_mir_lower::Env {
    rb_mir_lower::Env {
      items: self
        .ids
        .iter()
        .enumerate()
        .map(|(k, v)| {
          (v.clone(), rb_mir_lower::Item::NativeFunction(mir::NativeFunctionId(k as u64)))
        })
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

impl Value {
  pub fn as_int(&self) -> i64 {
    match self {
      Value::Int(i) => *i,
      _ => panic!("expected int"),
    }
  }

  pub fn as_bool(&self) -> bool {
    match self {
      Value::Bool(b) => *b,
      _ => panic!("expected bool"),
    }
  }
}

impl Environment {
  pub fn add_fn<T>(&mut self, name: impl Into<String>, function: impl DynFunction<T>) {
    let name = name.into();
    self.static_functions.insert(name.clone(), function.into_function());
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
