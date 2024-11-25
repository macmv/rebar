use ::std::{
  cell::{RefCell, UnsafeCell},
  fmt::Write,
  mem::ManuallyDrop,
};
use std::collections::HashMap;

use rb_gc::{lock::RefLock, Collect, Gc};
use rb_mir::ast::{self as mir};
use rb_std::{Environment, RbSlice, RebarArgsParser, Value};
use rb_typer::{Literal, Type};
use rb_value::{DynamicValueType, IntrinsicImpls, RbArray, RebarArgs};

use crate::gc::{GcArena, GcRoot};

mod arg_parser;

use arg_parser::OwnedRebarArgsParser;

pub struct RuntimeEnvironment {
  pub env: Environment,

  gc: GcArena,
}

// This works pretty well, but it would be nice to support multithreading, and
// multiple environments on one thread. Probably something for later though.
thread_local! {
  static ENV: RefCell<Option<RuntimeEnvironment>> = RefCell::new(None);
}

impl RuntimeEnvironment {
  pub fn core() -> Self {
    RuntimeEnvironment {
      env: Environment::core(),
      gc:  GcArena::new(|_| GcRoot { threads: HashMap::new() }),
    }
  }
  pub fn std() -> Self {
    RuntimeEnvironment {
      env: Environment::std(),
      gc:  GcArena::new(|_| GcRoot { threads: HashMap::new() }),
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

      let f = &env.env.static_functions[&env.env.ids[func as usize]];

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
        let mut parser = OwnedRebarArgsParser::new(args);
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
      let arg_value = unsafe { RebarArgsParser::new(args).value_unsized() };

      let str = unsafe { &mut *str_value.get() };
      write!(str, "{}", arg_value).unwrap();
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
      let a_value = unsafe { RebarArgsParser::new(a).value_unsized() };
      let b_value = unsafe { RebarArgsParser::new(b).value_unsized() };

      (a_value == b_value) as i8
    })
  }

  pub fn static_env(&self) -> rb_typer::Environment {
    rb_typer::Environment {
      names: self
        .env
        .static_functions
        .iter()
        .map(|(k, v)| (k.clone(), Type::Function(v.args.clone(), Box::new(v.ret.clone()))))
        .collect(),
    }
  }

  pub fn mir_env(&self) -> rb_mir_lower::Env {
    rb_mir_lower::Env {
      items: self
        .env
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn constructs_signatures() {
    let mut env = Environment::empty();

    env.add_fn("foo", (|a: i64, b: i64| -> i64 { a + b }) as fn(i64, i64) -> i64);
  }
}
