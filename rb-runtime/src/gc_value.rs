use std::{cell::UnsafeCell, mem::ManuallyDrop};

use rb_gc::{Collect, Gc};
use rb_std::{RbSlice, Value};
use rb_value::{DynamicValueType, RbArray};

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

// SAFETY: Must be `#[repr(C)]`, so that rebar can access fields in it. Rebar
// will never access the `vt` field (as that's captured in the static type
// information), but it needs the `arr` field to be at the start of the struct.
#[derive(Debug)]
#[repr(C)]
pub struct GcArray {
  pub(crate) arr: UnsafeCell<RbArray>,
  pub(crate) vt:  DynamicValueType,
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

unsafe impl Collect for GcValue {
  fn trace(&self, cc: &rb_gc::Collection) {
    match self {
      GcValue::String(s) => s.trace(cc),
      GcValue::Array(arr) => arr.trace(cc),
    }
  }
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
