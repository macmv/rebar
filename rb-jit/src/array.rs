use std::{mem::ManuallyDrop, ptr};

pub struct RbArray {
  /// The size of each element in the array, in slots. Note that this only lives
  /// on the stack in rust! It is static in rebar, and so it is hardcoded in
  /// the JIT's code, and passed along through native calls to the runtime.
  slot_size: u32,

  /// A pointer to the actual array data. It always has 64-bit alignment, and
  /// this is a thin pointer, so the layout is as follows:
  /// - The first slot is the length of the array (in elements).
  /// - The second slot is the capacity of the array (in elements).
  /// - The remaining slots are the array contents.
  ///
  /// If the array is empty, this will be a null pointer.
  ptr: *mut i64,
}

impl RbArray {
  pub fn new(slot_size: u32) -> Self { Self { slot_size, ptr: ptr::null_mut() } }

  pub fn len(&self) -> usize {
    if self.ptr.is_null() {
      0
    } else {
      unsafe { *self.ptr as usize }
    }
  }

  pub fn cap(&self) -> usize {
    if self.ptr.is_null() {
      0
    } else {
      unsafe { *self.ptr.offset(1) as usize }
    }
  }

  pub fn as_ptr(&self) -> *const i64 { self.ptr }

  pub fn push(&mut self, element: &[i64]) {
    let len = self.len();
    let cap = self.cap();

    assert_eq!(element.len(), self.slot_size as usize);

    if len == cap {
      self.grow();
    }

    unsafe {
      let ptr = self.ptr.offset(2 + len as isize * self.slot_size as isize);
      for (i, &e) in element.iter().enumerate() {
        *ptr.offset(i as isize) = e;
      }
      // Increment length.
      *self.ptr += 1;
    }
  }

  pub fn get(&self, index: usize) -> &[i64] {
    assert!(index < self.len());

    let ptr = unsafe { self.ptr.offset(2 + index as isize * self.slot_size as isize) };
    unsafe { std::slice::from_raw_parts(ptr, self.slot_size as usize) }
  }

  fn grow(&mut self) {
    let len = self.len();
    let cap = self.cap();

    let new_cap = if cap == 0 { 1 } else { cap * 2 };
    let new_size = 2 + new_cap * self.slot_size as usize;

    if new_cap > isize::MAX as usize {
      panic!("array too large");
    }

    // Use Vec to allocate for us.
    let mut vec = ManuallyDrop::new(Vec::<i64>::with_capacity(new_size));

    let new_ptr = vec.as_mut_ptr();

    unsafe {
      if self.ptr.is_null() {
        (*new_ptr) = len as i64;
      } else {
        ptr::copy_nonoverlapping(self.ptr, new_ptr, 2 + len * self.slot_size as usize);

        // Drop the old Vec.
        let _ = Vec::from_raw_parts(self.ptr, 0, 2 + cap * self.slot_size as usize);
      }
    }

    self.ptr = new_ptr;
    unsafe {
      (*self.ptr.offset(1)) = new_cap as i64;
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn rb_array_works() {
    let mut arr = RbArray::new(2);

    assert_eq!(arr.len(), 0);
    assert_eq!(arr.cap(), 0);

    arr.push(&[1, 2]);
    assert_eq!(arr.get(0), &[1, 2]);

    assert_eq!(arr.len(), 1);
    assert_eq!(arr.cap(), 1);

    arr.push(&[3, 4]);
    assert_eq!(arr.get(0), &[1, 2]);
    assert_eq!(arr.get(1), &[3, 4]);

    assert_eq!(arr.len(), 2);
    assert_eq!(arr.cap(), 2);

    arr.push(&[5, 6]);
    assert_eq!(arr.get(0), &[1, 2]);
    assert_eq!(arr.get(1), &[3, 4]);
    assert_eq!(arr.get(2), &[5, 6]);

    assert_eq!(arr.len(), 3);
    assert_eq!(arr.cap(), 4);
  }
}
