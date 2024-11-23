use ::std::{
  cell::RefCell, collections::HashMap, fmt::Write, marker::PhantomData, mem::ManuallyDrop,
};

mod core;
mod std;

use gc_arena::{lock::RefLock, Collect, Gc};
use rb_jit::{
  jit::{IntrinsicImpls, RbArray, RebarArgs},
  value::{DynamicValueType, ValueType},
};
use rb_mir::ast::{self as mir};
use rb_typer::{Literal, Type};

use crate::gc::{GcArena, GcId, GcRoot};

mod slice;
use slice::RbSlice;

pub struct Environment {
  pub static_functions: HashMap<String, Function>,
  ids:                  Vec<String>,

  gc: GcArena,
}

pub struct Function {
  args: Vec<Type>,
  ret:  Type,

  imp: Box<dyn Fn(Vec<Value>) -> OwnedValue>,
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

  pub(crate) fn intrinsics(self) -> IntrinsicImpls {
    ENV.with(|env| {
      *env.borrow_mut() = Some(self);
    });

    IntrinsicImpls {
      call:                Self::dyn_call_ptr(),
      push_frame:          Self::push_frame(),
      pop_frame:           Self::pop_frame(),
      track:               Self::track,
      string_append_value: Self::string_append_value,
      value_equals:        Self::value_equals,
    }
  }

  fn track_value(&self, value: GcValue) {
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
            let dvt = DynamicValueType::for_type(ty);
            args.push(parser.value(dvt));
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

              env.track_value(GcValue::String(str));
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
        Value::String(s) => str_value.push_str(s),
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

/// An owned, garbage collected value. This is created from the rebar values, so
/// it almost always shows up as a `ManuallyDrop<GcValue>`, as we need to
/// control dropping behavior.
///
/// Using `GcValue::gc_id`, we can check if we've already tracked a value. If we
/// haven't then the owned value is added to the garbage collector.
#[derive(Debug, Collect, PartialEq)]
#[collect(no_drop)]
pub enum GcValue {
  String(String),
  Array(RbArrayCollect),
}

#[derive(Debug, PartialEq)]
pub struct RbArrayCollect {
  arr: Box<RbArray>,
  vt:  DynamicValueType,
}

// FIXME: This is horribly incorrect. I basically need to pass a `RuntimeEnv`
// through `cc` somehow, so that I can parse the nested values out of this
// `Vec<i64>`.
//
// TODO: Write new gc :)
unsafe impl Collect for RbArrayCollect {
  fn trace(&self, cc: &gc_arena::Collection) {
    for elem in self.arr.iter() {
      elem.trace(cc);
    }
  }
}

/// A value with references to rebar values. This typically has the lifetime of
/// the native rust function that is being passed this value.
#[derive(Debug, PartialEq)]
pub enum Value<'a> {
  Nil,
  Int(i64),
  Bool(bool),
  String(&'a str),
  Array(RbSlice<'a>),
}

/// An owned value, created from rust, that will be passed back to rebar.
#[derive(Debug, PartialEq)]
pub enum OwnedValue {
  Nil,
  Int(i64),
  Bool(bool),
  String(String),
  Array(Vec<i64>),
}

impl Value<'_> {
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

  pub fn as_str(&self) -> &str {
    match self {
      Value::String(s) => s,
      _ => panic!("expected str"),
    }
  }
}

impl OwnedValue {
  pub fn as_int(&self) -> i64 {
    match self {
      OwnedValue::Int(i) => *i,
      _ => panic!("expected int"),
    }
  }

  pub fn as_bool(&self) -> bool {
    match self {
      OwnedValue::Bool(b) => *b,
      _ => panic!("expected bool"),
    }
  }

  pub fn as_str(&self) -> &str {
    match self {
      OwnedValue::String(s) => s,
      _ => panic!("expected str"),
    }
  }
}

impl GcValue {
  pub fn gc_id(&self) -> GcId {
    match self {
      GcValue::String(s) => GcId(s.as_ptr() as u64),
      GcValue::Array(RbArrayCollect { arr, .. }) => {
        let ptr = &**arr as *const RbArray;
        GcId(ptr as u64)
      }
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
  fn into_value(self) -> OwnedValue { OwnedValue::Int(self) }
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
  fn into_value(self) -> OwnedValue { OwnedValue::Bool(self) }
}

impl FunctionArg for String {
  fn static_type() -> Type { Type::Literal(Literal::String) }
  fn from_value(v: Value) -> Self {
    match v {
      Value::String(s) => s.into(),
      _ => panic!("expected string"),
    }
  }
}

impl FunctionRet for String {
  fn static_type() -> Type { Type::Literal(Literal::String) }
  fn into_value(self) -> OwnedValue { OwnedValue::String(self) }
}

impl FunctionRet for () {
  fn static_type() -> Type { Type::Literal(Literal::Unit) }
  fn into_value(self) -> OwnedValue { OwnedValue::Nil }
}

pub struct RebarArgsParser<'a> {
  args:   *const RebarArgs,
  offset: usize,

  _phantom: PhantomData<&'a ()>,
}

impl<'a> RebarArgsParser<'a> {
  pub fn new(args: *const RebarArgs) -> Self {
    RebarArgsParser { args, offset: 0, _phantom: PhantomData }
  }

  unsafe fn next(&mut self) -> i64 {
    let v = *(&*self.args).arg(self.offset) as i64;
    self.offset += 1;
    v
  }

  unsafe fn value_const(&mut self, vt: ValueType) -> Value<'a> {
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
        let str = ::std::str::from_utf8_unchecked(::std::slice::from_raw_parts(
          ptr as *const u8,
          len as usize,
        ));

        Value::String(str)
      }
      ValueType::Array => {
        let ptr = self.next();
        let vt = self.next();

        let arr = &*(ptr as *const RbArray) as &RbArray;
        let vt = DynamicValueType::decode(vt);

        Value::Array(RbSlice::new(arr, vt))
      }
      v => unimplemented!("{v:?}"),
    }
  }

  unsafe fn value_owned(&mut self, vt: ValueType) -> ManuallyDrop<GcValue> {
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

        ManuallyDrop::new(GcValue::String(str))
      }
      ValueType::Array => {
        let ptr = self.next();
        let vt = self.next();

        let vt = DynamicValueType::decode(vt);

        ManuallyDrop::new(GcValue::Array(RbArrayCollect {
          arr: Box::from_raw(ptr as *mut RbArray),
          vt,
        }))
      }
      _ => unreachable!("not an owned value: {vt:?}"),
    }
  }

  pub unsafe fn value(&mut self, dvt: DynamicValueType) -> Value<'a> {
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
      panic!("read too many slots while parsing argument of type {dvt:?}");
    }

    v
  }

  /// Parses a single value, and renders the current parser unusable. If the
  /// value passed in changes type, the amount of slots parsed could change,
  /// which makes this inconsistent. So, after calling this, a subsequent
  /// value cannot be parsed.
  pub unsafe fn value_unsized(&mut self) -> Value<'a> {
    let ty = self.next();
    let vt = ValueType::try_from(ty).unwrap();
    self.value_const(vt)
  }

  /// Parses a value to get tracked by the GC.
  pub unsafe fn value_owned_unsized(&mut self) -> ManuallyDrop<GcValue> {
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
