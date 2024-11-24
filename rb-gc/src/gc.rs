use core::{
  alloc::Layout,
  borrow::Borrow,
  fmt::{self, Debug, Display, Pointer},
  hash::{Hash, Hasher},
  ops::Deref,
  ptr::NonNull,
};

use crate::{
  barrier::{Unlock, Write},
  collect::Collect,
  context::{Collection, Mutation},
  gc_weak::GcWeak,
  static_collect::Static,
  types::{GcBox, GcBoxHeader, GcBoxInner, GcColor},
  Finalization,
};

/// A garbage collected pointer to a type T. Implements Copy, and is implemented
/// as a plain machine pointer. You can only allocate `Gc` pointers through a
/// `&Mutation<'gc>` inside an arena type, and through "generativity" such `Gc`
/// pointers may not escape the arena they were born in or be stored inside TLS.
/// This, combined with correct `Collect` implementations, means that `Gc`
/// pointers will never be dangling and are always safe to access.
pub struct Gc<T: ?Sized> {
  pub(crate) ptr: NonNull<GcBoxInner<T>>,
}

impl<T: Debug + ?Sized> Debug for Gc<T> {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result { fmt::Debug::fmt(&**self, fmt) }
}

impl<T: ?Sized> Pointer for Gc<T> {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
    fmt::Pointer::fmt(&Gc::as_ptr(*self), fmt)
  }
}

impl<T: Display + ?Sized> Display for Gc<T> {
  fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result { fmt::Display::fmt(&**self, fmt) }
}

impl<T: ?Sized> Copy for Gc<T> {}

impl<T: ?Sized> Clone for Gc<T> {
  #[inline]
  fn clone(&self) -> Gc<T> { *self }
}

unsafe impl<T: ?Sized> Collect for Gc<T> {
  #[inline]
  fn trace(&self, cc: &Collection) {
    unsafe {
      cc.trace(GcBox::erase(self.ptr));
    }
  }
}

impl<T: ?Sized> Deref for Gc<T> {
  type Target = T;

  #[inline]
  fn deref(&self) -> &T { unsafe { &self.ptr.as_ref().value } }
}

impl<T: ?Sized> AsRef<T> for Gc<T> {
  #[inline]
  fn as_ref(&self) -> &T { unsafe { &self.ptr.as_ref().value } }
}

impl<T: ?Sized> Borrow<T> for Gc<T> {
  #[inline]
  fn borrow(&self) -> &T { unsafe { &self.ptr.as_ref().value } }
}

impl<'gc, T: Collect + 'gc> Gc<T> {
  #[inline]
  pub fn new(mc: &Mutation<'gc>, t: T) -> Gc<T> { Gc { ptr: mc.allocate(t) } }
}

impl<T: 'static> Gc<T> {
  /// Create a new `Gc` pointer from a static value.
  ///
  /// This method does not require that the type `T` implement `Collect`. This
  /// uses [`Static`] internally to automatically provide a trivial `Collect`
  /// impl and is equivalent to the following code:
  ///
  /// ```rust
  /// # use rb_gc::{Gc, Static};
  /// # fn main() {
  /// # rb_gc::arena::rootless_mutate(|mc| {
  /// struct MyStaticStruct;
  /// let p = Gc::new(mc, Static(MyStaticStruct));
  /// // This is allowed because `Static` is `#[repr(transparent)]`
  /// let p: Gc<MyStaticStruct> = unsafe { Gc::cast(p) };
  /// # });
  /// # }
  /// ```
  #[inline]
  pub fn new_static(mc: &Mutation, t: T) -> Gc<T> {
    let p = Gc::new(mc, Static(t));
    // SAFETY: `Static` is `#[repr(transparent)]`.
    unsafe { Gc::cast::<T>(p) }
  }
}

impl<'gc, T: ?Sized + 'gc> Gc<T> {
  /// Cast a `Gc` pointer to a different type.
  ///
  /// SAFETY:
  /// It must be valid to dereference a `*mut U` that has come from casting a
  /// `*mut T`.
  #[inline]
  pub unsafe fn cast<U>(this: Gc<T>) -> Gc<U> { Gc { ptr: NonNull::cast(this.ptr) } }

  /// Cast a `Gc` to the unit type.
  ///
  /// This is exactly the same as `unsafe { Gc::cast::<()>(this) }`, but we can
  /// provide this method safely because it is always safe to dereference a
  /// `*mut ()` that has come from casting a `*mut T`.
  #[inline]
  pub fn erase(this: Gc<T>) -> Gc<()> { unsafe { Gc::cast(this) } }

  /// Retrieve a `Gc` from a raw pointer obtained from `Gc::as_ptr`
  ///
  /// SAFETY:
  /// The provided pointer must have been obtained from `Gc::as_ptr`, and the
  /// pointer must not have been collected yet.
  #[inline]
  pub unsafe fn from_ptr(ptr: *const T) -> Gc<T> {
    let layout = Layout::new::<GcBoxHeader>();
    let (_, header_offset) = layout.extend(Layout::for_value(&*ptr)).unwrap();
    let header_offset = -(header_offset as isize);
    let ptr = (ptr as *mut T).byte_offset(header_offset) as *mut GcBoxInner<T>;
    Gc { ptr: NonNull::new_unchecked(ptr) }
  }
}

impl<'gc, T: Unlock + ?Sized + 'gc> Gc<T> {
  /// Shorthand for [`Gc::write`]`(mc, self).`[`unlock()`](Write::unlock).
  #[inline]
  pub fn unlock(self, mc: &Mutation<'gc>) -> &'gc T::Unlocked {
    Gc::write(mc, self);
    // SAFETY: see doc-comment.
    unsafe { self.as_ref().unlock_unchecked() }
  }
}

impl<'gc, T: ?Sized + 'gc> Gc<T> {
  /// Obtains a long-lived reference to the contents of this `Gc`.
  ///
  /// Unlike `AsRef` or `Deref`, the returned reference isn't bound to the `Gc`
  /// itself, and will stay valid for the entirety of the current arena
  /// callback.
  #[inline]
  pub fn as_ref(self: Gc<T>) -> &'gc T {
    // SAFETY: The returned reference cannot escape the current arena callback, as
    // `&'gc T` never implements `Collect` (unless `'gc` is `'static`, which is
    // impossible here), and so cannot be stored inside the GC root.
    unsafe { &self.ptr.as_ref().value }
  }

  #[inline]
  pub fn downgrade(this: Gc<T>) -> GcWeak<T> { GcWeak { inner: this } }

  /// Triggers a write barrier on this `Gc`, allowing for safe mutation.
  ///
  /// This triggers an unrestricted *backwards* write barrier on this pointer,
  /// meaning that it is guaranteed that this pointer can safely adopt *any*
  /// arbitrary child pointers (until the next time that collection is
  /// triggered).
  ///
  /// It returns a reference to the inner `T` wrapped in a `Write` marker to
  /// allow for unrestricted mutation on the held type or any of its directly
  /// held fields.
  #[inline]
  pub fn write(mc: &Mutation<'gc>, gc: Self) -> &'gc Write<T> {
    unsafe {
      mc.backward_barrier(Gc::erase(gc), None);
      // SAFETY: the write barrier stays valid until the end of the current callback.
      Write::assume(gc.as_ref())
    }
  }

  /// Returns true if two `Gc`s point to the same allocation.
  ///
  /// Similarly to `Rc::ptr_eq` and `Arc::ptr_eq`, this function ignores the
  /// metadata of `dyn` pointers.
  #[inline]
  pub fn ptr_eq(this: Gc<T>, other: Gc<T>) -> bool {
    // TODO: Equivalent to `core::ptr::addr_eq`:
    // https://github.com/rust-lang/rust/issues/116324
    Gc::as_ptr(this) as *const () == Gc::as_ptr(other) as *const ()
  }

  #[inline]
  pub fn as_ptr(gc: Gc<T>) -> *const T {
    unsafe {
      let inner = gc.ptr.as_ptr();
      core::ptr::addr_of!((*inner).value) as *const T
    }
  }

  /// Returns true when a pointer is *dead* during finalization. This is
  /// equivalent to `GcWeak::is_dead` for strong pointers.
  ///
  /// Any strong pointer reachable from the root will never be dead, BUT there
  /// can be strong pointers reachable only through other weak pointers that
  /// can be dead.
  #[inline]
  pub fn is_dead(_: &Finalization<'gc>, gc: Gc<T>) -> bool {
    let inner = unsafe { gc.ptr.as_ref() };
    matches!(inner.header.color(), GcColor::White | GcColor::WhiteWeak)
  }

  /// Manually marks a dead `Gc` pointer as reachable and keeps it alive.
  ///
  /// Equivalent to `GcWeak::resurrect` for strong pointers. Manually marks this
  /// pointer and all transitively held pointers as reachable, thus keeping
  /// them from being dropped this collection cycle.
  #[inline]
  pub fn resurrect(fc: &Finalization<'gc>, gc: Gc<T>) {
    unsafe {
      fc.resurrect(GcBox::erase(gc.ptr));
    }
  }
}

impl<T: PartialEq + ?Sized> PartialEq for Gc<T> {
  fn eq(&self, other: &Self) -> bool { (**self).eq(other) }

  fn ne(&self, other: &Self) -> bool { (**self).ne(other) }
}

impl<T: Eq + ?Sized> Eq for Gc<T> {}

impl<T: PartialOrd + ?Sized> PartialOrd for Gc<T> {
  fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> { (**self).partial_cmp(other) }

  fn le(&self, other: &Self) -> bool { (**self).le(other) }

  fn lt(&self, other: &Self) -> bool { (**self).lt(other) }

  fn ge(&self, other: &Self) -> bool { (**self).ge(other) }

  fn gt(&self, other: &Self) -> bool { (**self).gt(other) }
}

impl<T: Ord + ?Sized> Ord for Gc<T> {
  fn cmp(&self, other: &Self) -> core::cmp::Ordering { (**self).cmp(other) }
}

impl<T: Hash + ?Sized> Hash for Gc<T> {
  fn hash<H: Hasher>(&self, state: &mut H) { (**self).hash(state) }
}
