use std::{
  fmt,
  mem::ManuallyDrop,
  ops::{Deref, DerefMut},
  ptr::NonNull,
};

/// Same thing as `Vec<i64>`, but #[repr(C)] so that we can access fields
/// directly from rebar.
#[repr(C)]
pub struct RbArray {
  ptr: NonNull<i64>,
  len: usize,
  cap: usize,
}

impl RbArray {
  pub fn new() -> Self { Self { ptr: NonNull::dangling(), len: 0, cap: 0 } }
  pub fn new_with_len(len: usize) -> Self { vec![0; len].into() }

  pub fn as_ptr(&self) -> *const i64 { self.ptr.as_ptr() }
  pub fn len(&self) -> usize { self.len }
}

impl Deref for RbArray {
  type Target = [i64];

  fn deref(&self) -> &Self::Target {
    unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
  }
}

impl DerefMut for RbArray {
  fn deref_mut(&mut self) -> &mut Self::Target {
    unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
  }
}

impl fmt::Debug for RbArray {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.deref().fmt(f) }
}
impl PartialEq for RbArray {
  fn eq(&self, other: &Self) -> bool { self.deref().eq(other.deref()) }
}

impl From<Vec<i64>> for RbArray {
  fn from(vec: Vec<i64>) -> Self {
    let vec = ManuallyDrop::new(vec);
    unsafe {
      RbArray {
        ptr: NonNull::new_unchecked(vec.as_ptr() as *mut i64),
        len: vec.len(),
        cap: vec.capacity(),
      }
    }
  }
}

impl From<RbArray> for Vec<i64> {
  fn from(rb: RbArray) -> Self {
    let rb = ManuallyDrop::new(rb);
    unsafe { Vec::from_raw_parts(rb.ptr.as_ptr(), rb.len, rb.cap) }
  }
}

impl Drop for RbArray {
  fn drop(&mut self) {
    unsafe {
      let _ = Vec::from_raw_parts(self.ptr.as_ptr(), self.len, self.cap);
    }
  }
}
