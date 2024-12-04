use std::{cell::UnsafeCell, fmt};

use rb_mir::MirContext;
use rb_value::{DynamicValueType, RbVec};

use crate::RbSlice;

// SAFETY: Must be `#[repr(C)]`, so that rebar can access fields in it. Rebar
// will never access the `vt` field (as that's captured in the static type
// information), but it needs the `arr` field to be at the start of the struct.
#[repr(C)]
pub struct RbArray {
  pub arr: UnsafeCell<RbVec>,
  pub vt:  DynamicValueType,
}

impl PartialEq for RbArray {
  // FIXME
  fn eq(&self, _other: &Self) -> bool {
    // self.as_slice() == other.as_slice()
    false
  }
}

impl RbArray {
  pub fn as_slice<'a>(&'a self, ctx: &'a MirContext) -> RbSlice<'a> {
    unsafe { RbSlice::new(ctx, &*self.arr.get(), self.vt) }
  }
}

impl fmt::Debug for RbArray {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RbArray").field("arr", &self.arr).finish()
  }
}
