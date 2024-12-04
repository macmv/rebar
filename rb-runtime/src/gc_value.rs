use std::mem::ManuallyDrop;

use rb_gc::{Collect, Gc};
use rb_mir::MirContext;
use rb_std::{RbArray, RbStruct, Value};

/// An owned, garbage collected value. This is created from the rebar values, so
/// it almost always shows up as a `ManuallyDrop<GcValue>`, as we need to
/// control dropping behavior.
///
/// Using `GcValue::gc_id`, we can check if we've already tracked a value. If we
/// haven't then the owned value is added to the garbage collector.
#[derive(Debug)]
pub enum GcValue<'ctx> {
  String(Gc<String>),
  Array(Gc<GcArray>),
  Struct(GcStruct<'ctx>),
}

#[derive(Debug)]
pub struct GcArray(pub RbArray);

// This type is never created by rebar. Instead, `ptr` is a pointer to the
// location on the stack where this struct lives. Once the rebar function
// returns, `ptr` will be invalid. Returning from a function will pop the
// GcStruct off the stack, and destroy the invalid pointer.
#[derive(Debug, PartialEq)]
pub struct GcStruct<'ctx>(pub RbStruct<'ctx>);

impl GcValue<'_> {
  // NB: This `GcValue` cannot be dropped, as that will cause a double free.
  pub(crate) fn from_value<'ctx>(value: &Value<'ctx>) -> Option<ManuallyDrop<GcValue<'ctx>>> {
    let gc = match value {
      Value::String(s) => unsafe { GcValue::String(Gc::from_ptr(*s)) },
      Value::Array(arr) => unsafe {
        // This is horrible.
        GcValue::Array(Gc::from_ptr(arr.elems as *const _ as *const GcArray))
      },
      Value::Struct(s) => GcValue::Struct(GcStruct(*s)),
      _ => return None,
    };
    Some(ManuallyDrop::new(gc))
  }
}

unsafe impl Collect<MirContext> for GcValue<'_> {
  fn trace(&self, ctx: &MirContext, cc: &rb_gc::Collection) {
    match self {
      GcValue::String(s) => s.trace(ctx, cc),
      GcValue::Array(arr) => arr.trace(ctx, cc),
      GcValue::Struct(s) => s.trace(ctx, cc),
    }
  }
}

unsafe impl Collect<MirContext> for GcArray {
  fn trace(&self, ctx: &MirContext, cc: &rb_gc::Collection) {
    for value in self.0.as_slice(ctx).iter() {
      if let Some(v) = GcValue::from_value(&value) {
        v.trace(ctx, cc);
      }
    }
  }
}

unsafe impl Collect<MirContext> for GcStruct<'_> {
  fn trace(&self, ctx: &MirContext, cc: &rb_gc::Collection) {
    for value in self.0.fields() {
      if let Some(v) = GcValue::from_value(&value) {
        v.trace(ctx, cc);
      }
    }
  }
}
