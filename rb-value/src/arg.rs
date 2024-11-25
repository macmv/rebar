use std::marker::PhantomPinned;

/// This struct is horribly dangerous to use. It is a struct storing the
/// arguments passed from the Rebar runtime up to rust code. Because calls know
/// the signature of the called function statically, this struct's layout
/// depends on the function signature. Its essentially a wrapper for a pointer
/// and should only be used as such.
///
/// So, don't move this thing around. I would wrap it in a `Pin`, but `Pin` is
/// annoying to use, so all the functions are just unsafe instead.
#[repr(C)]
pub struct RebarArgs {
  _phantom: PhantomPinned,
}

impl RebarArgs {
  pub unsafe fn arg(&self, offset: usize) -> *const i64 {
    unsafe {
      let ptr = self as *const _;
      (ptr as *const i64).offset(offset as isize)
    }
  }

  pub unsafe fn ret(&mut self, offset: usize, value: i64) {
    unsafe {
      let ptr = self as *mut _;
      *(ptr as *mut i64).offset(offset as isize) = value
    }
  }
}
