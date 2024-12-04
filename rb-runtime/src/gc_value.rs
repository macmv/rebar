use std::{cell::UnsafeCell, fmt, mem::ManuallyDrop};

use rb_gc::{Collect, Gc};
use rb_mir::MirContext;
use rb_std::{RbSlice, Value};
use rb_value::{DynamicValueType, RbArray, RebarArgs, ValueType};

use crate::owned_arg_parser::OwnedRebarArgsParser;

/// An owned, garbage collected value. This is created from the rebar values, so
/// it almost always shows up as a `ManuallyDrop<GcValue>`, as we need to
/// control dropping behavior.
///
/// Using `GcValue::gc_id`, we can check if we've already tracked a value. If we
/// haven't then the owned value is added to the garbage collector.
#[derive(Debug, PartialEq)]
pub enum GcValue<'ctx> {
  String(Gc<String>),
  Array(Gc<GcArray<'ctx>>),
  Struct(GcStruct<'ctx>),
}

// SAFETY: Must be `#[repr(C)]`, so that rebar can access fields in it. Rebar
// will never access the `vt` field (as that's captured in the static type
// information), but it needs the `arr` field to be at the start of the struct.
#[repr(C)]
pub struct GcArray<'ctx> {
  pub(crate) arr: UnsafeCell<RbArray>,
  pub(crate) ctx: &'ctx MirContext,
  pub(crate) vt:  DynamicValueType,
}

// This type is never created by rebar. Instead, `ptr` is a pointer to the
// location on the stack where this struct lives. Once the rebar function
// returns, `ptr` will be invalid. Returning from a function will pop the
// GcStruct off the stack, and destroy the invalid pointer.
pub struct GcStruct<'ctx> {
  pub(crate) ctx:   &'ctx MirContext,
  pub(crate) strct: rb_mir::Struct,
  pub(crate) ptr:   *const RebarArgs,
}

impl GcValue<'_> {
  // NB: This `GcValue` cannot be dropped, as that will cause a double free.
  pub(crate) fn from_value(value: &Value) -> Option<ManuallyDrop<GcValue<'static>>> {
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

impl PartialEq for GcArray<'_> {
  fn eq(&self, other: &Self) -> bool { self.as_slice() == other.as_slice() }
}

impl GcArray<'_> {
  pub fn as_slice<'a>(&'a self) -> RbSlice<'a> {
    unsafe { RbSlice::new(self.ctx, &*self.arr.get(), self.vt) }
  }
}

impl fmt::Debug for GcArray<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("GcArray").field("arr", &self.arr).finish()
  }
}

impl fmt::Debug for GcStruct<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("GcStruct").field("ptr", &self.ptr).finish()
  }
}

impl PartialEq for GcStruct<'_> {
  fn eq(&self, other: &Self) -> bool { self.ptr == other.ptr }
}

unsafe impl Collect for GcValue<'_> {
  fn trace(&self, cc: &rb_gc::Collection) {
    match self {
      GcValue::String(s) => s.trace(cc),
      GcValue::Array(arr) => arr.trace(cc),
      GcValue::Struct(s) => s.trace(cc),
    }
  }
}

unsafe impl Collect for GcArray<'_> {
  fn trace(&self, cc: &rb_gc::Collection) {
    for value in self.as_slice().iter() {
      if let Some(v) = GcValue::from_value(&value) {
        v.trace(cc);
      }
    }
  }
}

impl Drop for GcArray<'_> {
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

unsafe impl Collect for GcStruct<'_> {
  fn trace(&self, cc: &rb_gc::Collection) {
    let mut parser = OwnedRebarArgsParser::new(self.ctx, self.ptr);

    for (_, ty) in self.strct.fields.iter() {
      match DynamicValueType::for_type(self.ctx, ty) {
        DynamicValueType::Const(vt) => match vt {
          ValueType::Int => parser.offset += 1,

          ValueType::String | ValueType::Array => unsafe {
            parser.value_owned(vt).trace(cc);
          },

          _ => todo!("skip const value: {vt:?}"),
        },
        // FIXME: Consume the rest of `len` bytes.
        DynamicValueType::Union(_len) => unsafe {
          parser.value_owned_unsized().trace(cc);
        },
      }
    }
  }
}
