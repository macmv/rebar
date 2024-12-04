use std::{cell::UnsafeCell, fmt};

use rb_mir::MirContext;
use rb_value::{DynamicValueType, RbVec};

use crate::RbSlice;

// SAFETY: Must be `#[repr(C)]`, so that rebar can access fields in it. Rebar
// will never access the `vt` field (as that's captured in the static type
// information), but it needs the `arr` field to be at the start of the struct.
#[repr(C)]
pub struct RbArray<'ctx> {
  pub arr: UnsafeCell<RbVec>,
  pub ctx: &'ctx MirContext,
  pub vt:  DynamicValueType,
}

impl PartialEq for RbArray<'_> {
  fn eq(&self, other: &Self) -> bool { self.as_slice() == other.as_slice() }
}

impl RbArray<'_> {
  pub fn as_slice<'a>(&'a self) -> RbSlice<'a> {
    unsafe { RbSlice::new(self.ctx, &*self.arr.get(), self.vt) }
  }
}

impl fmt::Debug for RbArray<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RbArray").field("arr", &self.arr).finish()
  }
}
