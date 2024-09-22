use ::std::{cell::RefCell, collections::HashMap, fmt::Write, mem::ManuallyDrop, slice};

mod core;
mod std;

use gc_arena::{lock::RefLock, Collect, Gc};
use rb_jit::{
  jit::{RebarArgs, RuntimeHelpers},
  value::{DynamicValueType, ValueType},
};
use rb_mir::ast::{self as mir};
use rb_typer::{Literal, Type};

use crate::gc::{GcArena, GcId, GcRoot};

pub struct Environment {
  pub static_functions: HashMap<String, Function>,
  ids:                  Vec<String>,

  gc: GcArena,
}

pub struct Function {
  args: Vec<Type>,
  ret:  Type,

  imp: Box<dyn Fn(Vec<Value>) -> Value>,
}

// This works pretty well, but it would be nice to support multithreading, and
// multiple environments on one thread. Probably something for later though.
thread_local! {
  static ENV: RefCell<Option<Environment>> = RefCell::new(None);
}

impl Environment {
  fn empty() -> Self {
    Environment {
      static_functions: HashMap::new(),
      ids:              vec![],
      gc:               GcArena::new(|_| GcRoot { threads: HashMap::new() }),
    }
  }

  pub(crate) fn helpers(self) -> RuntimeHelpers {
    ENV.with(|env| {
      *env.borrow_mut() = Some(self);
    });

    RuntimeHelpers {
      call:                Self::dyn_call_ptr(),
      push_frame:          Self::push_frame(),
      pop_frame:           Self::pop_frame(),
      track:               Self::track,
      string_append_value: Self::string_append_value,
      array_push:          Self::array_push,
      value_equals:        Self::value_equals,
    }
  }

  fn track_value(&self, value: Value) {
    self.gc.mutate(|m, root| {
      let tid = 3; // FIXME: Use ThreadId.

      let thread = root.threads.get(&tid).unwrap();
      let frame = thread.frames.last().unwrap();

      let id = value.gc_id();
      frame.borrow_mut(m).values.insert(id, Gc::new(&m, value));
    });
  }

  fn dyn_call_ptr() -> fn(i64, *const RebarArgs, *mut RebarArgs) {
    |func, arg, ret| {
      ENV.with(|env| {
        let env = env.borrow();
        let env = env.as_ref().unwrap();

        let f = &env.static_functions[&env.ids[func as usize]];

        let ret = unsafe { &mut *ret };

        let args = unsafe {
          let mut parser = RebarArgsParser::new(arg);

          let mut args = vec![];
          for ty in f.args.iter() {
            args.push(parser.value(ty));
          }
          args
        };

        let ret_value = (f.imp)(args);

        unsafe {
          // TODO: Native functions must always return a value, but the runtime isn't
          // going to assume that. Need to figure out a way to return something
          // sane here.
          match f.ret {
            Type::Literal(Literal::Unit) => {}
            Type::Literal(Literal::Bool) => ret.ret(0, ret_value.as_bool() as i64),
            Type::Literal(Literal::Int) => ret.ret(0, ret_value.as_int() as i64),
            Type::Literal(Literal::String) => {
              let mut str = String::from(ret_value.as_str());
              str.shrink_to_fit();
              let ptr = str.as_ptr() as i64;

              ret.ret(0, str.len() as i64);
              ret.ret(1, ptr);

              env.track_value(Value::String(str));
            }
            ref v => unimplemented!("{v:?}"),
          }
        }
      })
    }
  }

  fn push_frame() -> fn() {
    || {
      ENV.with(|env| {
        let mut env = env.borrow_mut();
        env.as_mut().unwrap().gc.mutate_root(|m, root| {
          let tid = 3; // FIXME: Use ThreadId.

          let thread = root.threads.entry(tid).or_insert_with(|| crate::gc::Stack::default());

          thread.frames.push(Gc::new(m, RefLock::new(crate::gc::Frame::default())));
        });
      });
    }
  }

  fn pop_frame() -> fn() {
    || {
      ENV.with(|env| {
        let mut env = env.borrow_mut();
        env.as_mut().unwrap().gc.mutate_root(|_, root| {
          let tid = 3; // FIXME: Use ThreadId.

          let thread = root.threads.entry(tid).or_insert_with(|| crate::gc::Stack::default());

          thread.frames.pop().unwrap();
        });
      });
    }
  }

  fn track(args: *const RebarArgs) {
    ENV.with(|env| {
      let value = unsafe {
        let mut parser = RebarArgsParser::new(args);
        parser.value_owned_unsized()
      };

      let mut env = env.borrow_mut();
      env.as_mut().unwrap().gc.mutate_root(|m, root| {
        let tid = 3; // FIXME: Use ThreadId.

        let thread = root.threads.entry(tid).or_insert_with(|| crate::gc::Stack::default());
        let mut frame = thread.frames.last_mut().unwrap().borrow_mut(m);

        let id = value.gc_id();
        match frame.values.get(&id) {
          Some(_) => {
            // NB: Now we've gotten into chaotic territory. Because this
            // value is already tracked, it means we have just
            // created an owned value `parser.value_owned_unsized`. However,
            // that value is wrapped in a `ManuallyDrop`, so we
            // don't need to do anything here, we can just
            // forget about this value, as it's already in the GC.
          }
          None => {
            frame.values.insert(id, Gc::new(&m, ManuallyDrop::into_inner(value)));
          }
        }
      });
    });
  }

  fn string_append_value(str: *const RebarArgs, args: *const RebarArgs) {
    ENV.with(|_env| {
      let str = unsafe { &mut *(str as *mut RebarArgs) };
      let mut str_value = unsafe {
        let mut parser = RebarArgsParser::new(str);

        let len = parser.next();
        let cap = parser.next();
        let ptr = parser.next();
        ManuallyDrop::new(String::from_utf8_unchecked(Vec::from_raw_parts(
          ptr as *mut u8,
          len as usize,
          cap as usize,
        )))
      };

      let arg_value = unsafe {
        let mut parser = RebarArgsParser::new(args);
        parser.value_unsized()
      };

      match arg_value {
        Value::Int(i) => write!(str_value, "{}", i).unwrap(),
        Value::String(s) => str_value.push_str(s.as_str()),
        Value::Array(v) => write!(str_value, "{v:?}").unwrap(),
        _ => panic!("expected string"),
      }

      unsafe {
        str.ret(0, str_value.len() as i64);
        str.ret(1, str_value.capacity() as i64);
        str.ret(2, str_value.as_ptr() as i64);
      }
    });
  }

  fn array_push(array: *mut Vec<i64>, slot_size: i64, arg: *const RebarArgs) {
    ENV.with(|_env| {
      let mut array = unsafe { ManuallyDrop::new(Box::from_raw(array)) };

      let slice = unsafe {
        let mut parser = RebarArgsParser::new(arg);
        // Parse the value.
        parser.value_unsized();

        // Then, the resulting offset is the length of the item.
        let len = parser.offset;

        ::std::slice::from_raw_parts(arg as *const i64, len)
      };

      assert!(slice.len() <= slot_size as usize);
      array.extend(slice);
      for _ in slice.len()..slot_size as usize {
        array.push(0);
      }
    });
  }

  fn value_equals(a: *const RebarArgs, b: *const RebarArgs) -> i8 {
    ENV.with(|_env| {
      let a_value = unsafe {
        let mut parser = RebarArgsParser::new(a);
        parser.value_unsized()
      };

      let b_value = unsafe {
        let mut parser = RebarArgsParser::new(b);
        parser.value_unsized()
      };

      (a_value == b_value) as i8
    })
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

#[derive(Debug, Collect, PartialEq)]
#[collect(no_drop)]
pub enum Value {
  Nil,
  Int(i64),
  Bool(bool),
  String(String),
  Array(Vec<i64>),
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

  pub fn as_str(&self) -> &String {
    match self {
      Value::String(s) => s,
      _ => panic!("expected str"),
    }
  }

  pub fn gc_id(&self) -> GcId {
    match self {
      Value::String(s) => GcId(s.as_ptr() as u64),
      _ => panic!("cannot gc {self:?}"),
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

impl FunctionArg for String {
  fn static_type() -> Type { Type::Literal(Literal::String) }
  fn from_value(v: Value) -> Self {
    match v {
      Value::String(s) => s,
      _ => panic!("expected string"),
    }
  }
}

impl FunctionRet for String {
  fn static_type() -> Type { Type::Literal(Literal::String) }
  fn into_value(self) -> Value { Value::String(self) }
}

impl FunctionRet for () {
  fn static_type() -> Type { Type::Literal(Literal::Unit) }
  fn into_value(self) -> Value { Value::Nil }
}

pub struct RebarArgsParser {
  args:   *const RebarArgs,
  offset: usize,
}

impl RebarArgsParser {
  pub fn new(args: *const RebarArgs) -> Self { RebarArgsParser { args, offset: 0 } }

  unsafe fn next(&mut self) -> i64 {
    let v = *(&*self.args).arg(self.offset) as i64;
    self.offset += 1;
    v
  }

  unsafe fn value_const(&mut self, vt: ValueType) -> Value {
    match vt {
      ValueType::Nil => Value::Nil,
      // Booleans only use 8 bits, so cast the value to a u8 and just compare that.
      ValueType::Bool => {
        // The value will always take up 8 bytes, even if less bytes are used.
        Value::Bool(self.next() as u8 != 0)
      }
      ValueType::Int => Value::Int(self.next()),
      ValueType::String => {
        // SAFETY: `value` came from rebar, so we assume its a valid pointer.
        // The value will always take up 8 bytes, even if less bytes are used.
        let len = self.next();
        let ptr = self.next();
        let str =
          ::std::str::from_utf8_unchecked(slice::from_raw_parts(ptr as *const u8, len as usize));

        Value::String(str.into())
      }
      ValueType::Array => {
        let ptr = self.next();

        let array_ptr = ptr as *mut Vec<i64>;
        let arr = ManuallyDrop::new(Box::from_raw(array_ptr));

        let slice = arr.as_slice();

        Value::Array(slice.into())
      }
      v => unimplemented!("{v:?}"),
    }
  }

  unsafe fn value_owned(&mut self, vt: ValueType) -> ManuallyDrop<Value> {
    match vt {
      ValueType::String => {
        // Rebar always shrinks strings before throwing them on the stack, so the len
        // and cap will be the same.
        let len = self.next();
        let ptr = self.next();
        let str = String::from_utf8_unchecked(Vec::from_raw_parts(
          ptr as *mut u8,
          len as usize,
          len as usize,
        ));

        ManuallyDrop::new(Value::String(str.into()))
      }
      _ => unreachable!("not an owned value: {vt:?}"),
    }
  }

  pub unsafe fn value(&mut self, ty: &Type) -> Value {
    let dvt = DynamicValueType::for_type(ty);

    let start = self.offset;
    let v = match dvt {
      DynamicValueType::Const(vt) => self.value_const(vt),
      DynamicValueType::Union(_) => {
        // A nil will only take up one slot, so we must check for that to avoid reading
        // out of bounds.
        let dyn_ty = self.next();

        let vt = ValueType::try_from(dyn_ty).unwrap();

        self.value_const(vt)
      }
    };

    let expected_end = start + dvt.len() as usize;
    if self.offset < expected_end {
      self.offset = expected_end;
    } else if self.offset > expected_end {
      panic!("read too many slots while parsing argument of type {ty:?}");
    }

    v
  }

  /// Parses a single value, and renders the current parser unusable. If the
  /// value passed in changes type, the amount of slots parsed could change,
  /// which makes this inconsistent. So, after calling this, a subsequent
  /// value cannot be parsed.
  pub unsafe fn value_unsized(&mut self) -> Value {
    let ty = self.next();
    let vt = ValueType::try_from(ty).unwrap();
    self.value_const(vt)
  }

  /// Parses a value to get tracked by the GC.
  pub unsafe fn value_owned_unsized(&mut self) -> ManuallyDrop<Value> {
    let ty = self.next();
    let vt = ValueType::try_from(ty).unwrap();
    self.value_owned(vt)
  }
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
