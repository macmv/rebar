use core::ptr::NonNull;

use crate::{types::GcBoxInner, Gc, GcWeak};

/// Unsizes a [`Gc`] or [`GcWeak`] pointer.
///
/// This macro is a `rb_gc`-specific replacement for the nightly-only
/// `CoerceUnsized` trait.
///
/// ## Usage
///
/// ```rust
/// # use std::fmt::Display;
/// # use rb_gc::{Gc, unsize};
/// # fn main() {
/// # rb_gc::arena::rootless_mutate(|mc| {
/// // Unsizing arrays to slices.
/// let mut slice;
/// slice = unsize!(Gc::new(mc, [1, 2]) => [u8]);
/// assert_eq!(slice.len(), 2);
/// slice = unsize!(Gc::new(mc, [42; 4]) => [u8]);
/// assert_eq!(slice.len(), 4);
///
/// // Unsizing values to trait objects.
/// let mut display;
/// display = unsize!(Gc::new(mc, "Hello world!".to_owned()) => dyn Display);
/// assert_eq!(display.to_string(), "Hello world!");
/// display = unsize!(Gc::new(mc, 123456) => dyn Display);
/// assert_eq!(display.to_string(), "123456");
/// # })
/// # }
/// ```
///
/// The `unsize` macro is safe, and will fail to compile when trying to coerce
/// between incompatible types.
/// ```rust,compile_fail
/// # use std::error::Error;
/// # use rb_gc::{Gc, unsize};
/// # fn main() {
/// # rb_gc::arena::rootless_mutate(|mc| {
/// // Error: `Option<char>` doesn't implement `Error`.
/// let _ = unsize!(Gc::new(mc, Some('💥')) => dyn Error);
/// # })
/// # }
/// ```
#[macro_export]
macro_rules! unsize {
  ($gc:expr => $ty:ty) => {{
    let gc = $gc;
    // SAFETY: the closure has a trivial body and must be a valid pointer
    // coercion, if it compiles. Additionally, the `__CoercePtrInternal` trait
    // ensures that the resulting GC pointer has the correct `'gc` lifetime.
    unsafe { $crate::__CoercePtrInternal::__coerce_unchecked(gc, |p: *mut _| -> *mut $ty { p }) }
  }};
}

// Not public API; implementation detail of the `unsize` macro.
//
// Maps a raw pointer coercion (`*mut FromPtr -> *mut ToPtr`) to
// a smart pointer coercion (`Self -> Dst`).
#[doc(hidden)]
pub unsafe trait __CoercePtrInternal<Dst> {
  type FromPtr;
  type ToPtr: ?Sized;
  // SAFETY: `coerce` must be a valid pointer coercion; in particular, the coerced
  // pointer must have the same address and provenance as the original.
  unsafe fn __coerce_unchecked<F>(self, coerce: F) -> Dst
  where
    F: FnOnce(*mut Self::FromPtr) -> *mut Self::ToPtr;
}

unsafe impl<'gc, T, U: ?Sized> __CoercePtrInternal<Gc<U>> for Gc<T> {
  type FromPtr = T;
  type ToPtr = U;

  #[inline(always)]
  unsafe fn __coerce_unchecked<F>(self, coerce: F) -> Gc<U>
  where
    F: FnOnce(*mut T) -> *mut U,
  {
    let ptr = self.ptr.as_ptr() as *mut T;
    let ptr = NonNull::new_unchecked(coerce(ptr) as *mut GcBoxInner<U>);
    Gc { ptr }
  }
}

unsafe impl<'gc, T, U: ?Sized> __CoercePtrInternal<GcWeak<U>> for GcWeak<T> {
  type FromPtr = T;
  type ToPtr = U;

  #[inline(always)]
  unsafe fn __coerce_unchecked<F>(self, coerce: F) -> GcWeak<U>
  where
    F: FnOnce(*mut T) -> *mut U,
  {
    let inner = self.inner.__coerce_unchecked(coerce);
    GcWeak { inner }
  }
}
