use std::ptr::NonNull;

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
}

impl From<Vec<i64>> for RbArray {
  fn from(vec: Vec<i64>) -> Self {
    unsafe {
      RbArray {
        ptr: NonNull::new_unchecked(vec.as_ptr() as *mut i64),
        len: vec.len(),
        cap: vec.capacity(),
      }
    }
  }
}

impl Drop for RbArray {
  fn drop(&mut self) {
    unsafe {
      let _ = Vec::from_raw_parts(self.ptr.as_ptr(), self.len, self.cap);
    }
  }
}
