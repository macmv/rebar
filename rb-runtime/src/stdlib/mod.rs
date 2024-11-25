use ::std::{
  cell::{RefCell, UnsafeCell},
  collections::HashMap,
  fmt::Write,
  marker::PhantomData,
  mem::ManuallyDrop,
};

mod core;
mod std;

use rb_gc::{lock::RefLock, Collect, Gc};
use rb_jit::jit::IntrinsicImpls;
use rb_mir::ast::{self as mir};
use rb_typer::{Literal, Type};
use rb_value::{DynamicValueType, RbArray, RebarArgs, ValueType};

use crate::gc::{GcArena, GcRoot};

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
      call:                Self::dyn_call_ptr,
      push_frame:          Self::push_frame,
      pop_frame:           Self::pop_frame,
      gc_collect:          Self::gc_collect,
      track:               Self::track,
      string_append_value: Self::string_append_value,
      string_append_str:   Self::string_append_str,
      string_new:          Self::string_new,
      array_new:           Self::array_new,
      value_equals:        Self::value_equals,
    }
  }

  fn track_value(&self, value: GcValue) {
    let m = self.gc.mutate();
    let root = self.gc.root();

    let tid = 3; // FIXME: Use ThreadId.

    let thread = root.threads.get(&tid).unwrap();
    let frame = thread.frames.last().unwrap();

    frame.borrow_mut(m).values.push(Gc::new(&m, value));
  }

  fn dyn_call_ptr(func: i64, arg: *const RebarArgs, ret: *mut RebarArgs) {
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
            let gc: Gc<String> = Gc::new(env.gc.mutate(), str);

            ret.ret(0, Gc::as_ptr(gc) as i64);

            env.track_value(GcValue::String(gc));
          }
          ref v => unimplemented!("{v:?}"),
        }
      }
    })
  }

  fn push_frame() {
    ENV.with(|env| {
      let mut env = env.borrow_mut();
      let env = env.as_mut().unwrap();

      let (m, root) = env.gc.mutate_root();
      let tid = 3; // FIXME: Use ThreadId.

      let thread = root.threads.entry(tid).or_insert_with(|| crate::gc::Stack::default());

      thread.frames.push(Gc::new(m, RefLock::new(crate::gc::Frame::default())));
    });
  }

  fn pop_frame() {
    ENV.with(|env| {
      let mut env = env.borrow_mut();

      let (_, root) = env.as_mut().unwrap().gc.mutate_root();
      let tid = 3; // FIXME: Use ThreadId.

      let thread = root.threads.entry(tid).or_insert_with(|| crate::gc::Stack::default());

      thread.frames.pop().unwrap();
    });
  }

  fn gc_collect() {
    ENV.with(|env| {
      let mut env = env.borrow_mut();

      // TODO: Use `collect_debt` instead, but while testing this is more effective.
      env.as_mut().unwrap().gc.collect_all();
    });
  }

  fn track(args: *const RebarArgs) {
    ENV.with(|env| {
      let value = unsafe {
        let mut parser = RebarArgsParser::new(args);
        parser.value_owned_unsized()
      };

      let mut env = env.borrow_mut();

      let (m, root) = env.as_mut().unwrap().gc.mutate_root();
      let tid = 3; // FIXME: Use ThreadId.

      let thread = root.threads.entry(tid).or_insert_with(|| crate::gc::Stack::default());
      let mut frame = thread.frames.last_mut().unwrap().borrow_mut(m);

      frame.values.push(Gc::new(&m, value));
    });
  }

  fn string_append_value(str: *const String, args: *const RebarArgs) {
    ENV.with(|_env| {
      let str_value = unsafe { Gc::from_ptr(str as *const UnsafeCell<String>) };

      let arg_value = unsafe {
        let mut parser = RebarArgsParser::new(args);
        parser.value_unsized()
      };

      let str = unsafe { &mut *str_value.get() };

      match arg_value {
        Value::Int(i) => write!(str, "{}", i).unwrap(),
        Value::String(s) => str.push_str(s),
        Value::Array(v) => write!(str, "{v:?}").unwrap(),
        _ => panic!("expected string"),
      }
    });
  }

  fn string_append_str(str: *const String, s: *const u8, len: i64) {
    ENV.with(|_env| {
      let str_value = unsafe { Gc::from_ptr(str as *const UnsafeCell<String>) };

      let s = unsafe { ::std::slice::from_raw_parts(s, len as usize) };

      unsafe {
        (&mut *str_value.get()).push_str(::std::str::from_utf8(s).unwrap());
      }
    });
  }

  fn string_new() -> *const String {
    ENV.with(|env| {
      let env = env.borrow();

      let m = env.as_ref().unwrap().gc.mutate();
      Gc::as_ptr(Gc::new(m, String::new()))
    })
  }

  fn array_new(len: i64, vt: i64) -> *const u8 {
    ENV.with(|env| {
      let env = env.borrow();
      let env = env.as_ref().unwrap();

      let vt = DynamicValueType::decode(vt);

      let m = env.gc.mutate();
      Gc::as_ptr(Gc::new(
        m,
        GcArray {
          arr: UnsafeCell::new(RbArray::new_with_len(len as usize * vt.len() as usize)),
          vt,
        },
      )) as *const u8
    })
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
#[derive(Debug, PartialEq)]
pub enum GcValue {
  String(Gc<String>),
  Array(Gc<GcArray>),
}

unsafe impl Collect for GcValue {
  fn trace(&self, cc: &rb_gc::Collection) {
    match self {
      GcValue::String(s) => s.trace(cc),
      GcValue::Array(arr) => arr.trace(cc),
    }
  }
}

// SAFETY: Must be `#[repr(C)]`, so that rebar can access fields in it. Rebar
// will never access the `vt` field (as that's captured in the static type
// information), but it needs the `arr` field to be at the start of the struct.
#[derive(Debug)]
#[repr(C)]
pub struct GcArray {
  arr: UnsafeCell<RbArray>,
  vt:  DynamicValueType,
}

impl GcValue {
  // NB: This `GcValue` cannot be dropped, as that will cause a double free.
  pub(crate) fn from_value(value: &Value) -> Option<ManuallyDrop<GcValue>> {
    let gc = match value {
      Value::String(s) => unsafe { GcValue::String(Gc::from_ptr(s.as_ptr() as *const String)) },
      Value::Array(arr) => unsafe {
        // This is horrible.
        GcValue::Array(Gc::from_ptr(arr.elems as *const RbArray as *const GcArray))
      },
      _ => return None,
    };
    Some(ManuallyDrop::new(gc))
  }
}

impl PartialEq for GcArray {
  fn eq(&self, other: &Self) -> bool { self.as_slice() == other.as_slice() }
}

impl GcArray {
  pub fn as_slice(&self) -> RbSlice { unsafe { RbSlice::new(&*self.arr.get(), self.vt) } }
}

unsafe impl Collect for GcArray {
  fn trace(&self, cc: &rb_gc::Collection) {
    for value in self.as_slice().iter() {
      if let Some(v) = GcValue::from_value(&value) {
        v.trace(cc);
      }
    }
  }
}

impl Drop for GcArray {
  fn drop(&mut self) {
    for value in self.as_slice().iter() {
      if let Some(mut v) = GcValue::from_value(&value) {
        unsafe {
          ManuallyDrop::drop(&mut v);
        }
      }
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
        let ptr = self.next();

        let gc = Gc::from_ptr(ptr as *const String);

        Value::String(::std::mem::transmute(gc.as_str()))
      }
      ValueType::Array => {
        let ptr = self.next();
        let arr = Gc::from_ptr(ptr as *const GcArray);

        Value::Array(RbSlice::new(&*arr.arr.get(), arr.vt))
      }
      v => unimplemented!("{v:?}"),
    }
  }

  unsafe fn value_owned(&mut self, vt: ValueType) -> GcValue {
    match vt {
      ValueType::String => {
        let ptr = self.next();

        let gc = Gc::from_ptr(ptr as *const String);

        GcValue::String(gc)
      }
      ValueType::Array => {
        let ptr = self.next();

        GcValue::Array(Gc::from_ptr(ptr as *const GcArray))
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

  /// Parses a value to get tracked by the GC. This value should not be dropped!
  pub unsafe fn value_owned_unsized(&mut self) -> GcValue {
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
