use alloc::{
  boxed::Box,
  collections::{BTreeMap, BTreeSet, LinkedList, VecDeque},
  rc::Rc,
  string::String,
  vec::Vec,
};
use core::{
  cell::{Cell, RefCell},
  marker::PhantomData,
};
#[cfg(feature = "std")]
use std::collections::{HashMap, HashSet};

use crate::{collect::Collect, context::Collection};

/// If a type is static, we know that it can never hold `Gc` pointers, so it is
/// safe to provide a simple empty `Collect` implementation.
#[macro_export]
macro_rules! static_collect {
  ($type:ty) => {
    unsafe impl<C> Collect<C> for $type
    where
      $type: 'static,
    {
      #[allow(dead_code)]
      #[inline]
      fn needs_trace() -> bool { false }
    }
  };
}

static_collect!(bool);
static_collect!(char);
static_collect!(u8);
static_collect!(u16);
static_collect!(u32);
static_collect!(u64);
static_collect!(usize);
static_collect!(i8);
static_collect!(i16);
static_collect!(i32);
static_collect!(i64);
static_collect!(isize);
static_collect!(f32);
static_collect!(f64);
static_collect!(String);
static_collect!(str);
static_collect!(alloc::ffi::CString);
static_collect!(core::ffi::CStr);
static_collect!(core::any::TypeId);
#[cfg(feature = "std")]
static_collect!(std::path::Path);
#[cfg(feature = "std")]
static_collect!(std::path::PathBuf);
#[cfg(feature = "std")]
static_collect!(std::ffi::OsStr);
#[cfg(feature = "std")]
static_collect!(std::ffi::OsString);

/// SAFETY: We know that a `&'static` reference cannot possibly point to `'gc`
/// data, so it is safe to keep in a rooted objet and we do not have to trace
/// through it.
///
/// HOWEVER, There is an extra bound here that seems superfluous. If we have a
/// `&'static T`, why do we require `T: 'static`, shouldn't this be implied,
/// otherwise a `&'static T` would not be well- formed? WELL, there are
/// currently some neat compiler bugs, observe...
///
/// ```rust,compile_fail
/// let arena = Arena::<Rootable![&'static Gc<'gc, i32>]>::new(Default::default(), |mc| {
///     Box::leak(Box::new(Gc::new(mc, 4)))
/// });
/// ```
///
/// At the time of this writing, without the extra `T: static` bound, the above
/// code compiles and produces an arena with a reachable but un-traceable
/// `Gc<'gc, i32>`, and this is unsound. This *is* ofc the stored type of the
/// root, since the Arena is actually constructing a `&'static Gc<'static, i32>`
/// as the root object, but this should still not rightfully compile due to the
/// signature of the constructor callback passed to `Arena::new`. In fact, the
/// 'static lifetime is a red herring, it is possible to change the internals of
/// `Arena` such that the 'gc lifetime given to the callback is *not* 'static,
/// and the problem persists.
///
/// It should not be required to have this extra lifetime bound, and yet! It
/// fixes the above issue perfectly and the given example of unsoundness no
/// longer compiles. So, until this rustc bug is fixed...
///
/// DO NOT REMOVE THIS EXTRA `T: 'static` BOUND
unsafe impl<T: ?Sized + 'static, C> Collect<C> for &'static T {
  #[inline]
  fn needs_trace() -> bool { false }
}

unsafe impl<T: ?Sized + Collect<C>, C> Collect<C> for Box<T> {
  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) { (**self).trace(ctx, cc) }
}

unsafe impl<T: Collect<C>, C> Collect<C> for [T] {
  #[inline]
  #[allow(dead_code)]
  fn needs_trace() -> bool { T::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for t in self.iter() {
      t.trace(ctx, cc)
    }
  }
}

unsafe impl<T: Collect<C>, C> Collect<C> for Option<T> {
  #[inline]
  fn needs_trace() -> bool { T::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    if let Some(t) = self.as_ref() {
      t.trace(ctx, cc)
    }
  }
}

unsafe impl<T: Collect<C>, E: Collect<C>, C> Collect<C> for Result<T, E> {
  #[inline]
  fn needs_trace() -> bool { T::needs_trace() || E::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    match self {
      Ok(r) => r.trace(ctx, cc),
      Err(e) => e.trace(ctx, cc),
    }
  }
}

unsafe impl<T: Collect<C>, C> Collect<C> for Vec<T> {
  #[inline]
  fn needs_trace() -> bool { T::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for t in self {
      t.trace(ctx, cc)
    }
  }
}

unsafe impl<T: Collect<C>, C> Collect<C> for VecDeque<T> {
  #[inline]
  fn needs_trace() -> bool { T::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for t in self {
      t.trace(ctx, cc)
    }
  }
}

unsafe impl<T: Collect<C>, C> Collect<C> for LinkedList<T> {
  #[inline]
  fn needs_trace() -> bool { T::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for t in self {
      t.trace(ctx, cc)
    }
  }
}

#[cfg(feature = "std")]
unsafe impl<K, V, S, C> Collect<C> for HashMap<K, V, S>
where
  K: Collect<C>,
  V: Collect<C>,
  S: 'static,
{
  #[inline]
  fn needs_trace() -> bool { K::needs_trace() || V::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for (k, v) in self {
      k.trace(ctx, cc);
      v.trace(ctx, cc);
    }
  }
}

#[cfg(feature = "std")]
unsafe impl<T, S, C> Collect<C> for HashSet<T, S>
where
  T: Collect<C>,
  S: 'static,
{
  #[inline]
  fn needs_trace() -> bool { T::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for v in self {
      v.trace(ctx, cc);
    }
  }
}

unsafe impl<K, V, C> Collect<C> for BTreeMap<K, V>
where
  K: Collect<C>,
  V: Collect<C>,
{
  #[inline]
  fn needs_trace() -> bool { K::needs_trace() || V::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for (k, v) in self {
      k.trace(ctx, cc);
      v.trace(ctx, cc);
    }
  }
}

unsafe impl<T, C> Collect<C> for BTreeSet<T>
where
  T: Collect<C>,
{
  #[inline]
  fn needs_trace() -> bool { T::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for v in self {
      v.trace(ctx, cc);
    }
  }
}

unsafe impl<T, C> Collect<C> for Rc<T>
where
  T: ?Sized + Collect<C>,
{
  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) { (**self).trace(ctx, cc); }
}

#[cfg(target_has_atomic = "ptr")]
unsafe impl<T, C> Collect<C> for alloc::sync::Arc<T>
where
  T: ?Sized + Collect<C>,
{
  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) { (**self).trace(ctx, cc); }
}

unsafe impl<T, C> Collect<C> for Cell<T>
where
  T: 'static,
{
  #[inline]
  fn needs_trace() -> bool { false }
}

unsafe impl<T, C> Collect<C> for RefCell<T>
where
  T: 'static,
{
  #[inline]
  fn needs_trace() -> bool { false }
}

// SAFETY: `PhantomData` is a ZST, and therefore doesn't store anything
unsafe impl<T, C> Collect<C> for PhantomData<T> {
  #[inline]
  fn needs_trace() -> bool { false }
}

unsafe impl<T: Collect<C>, C, const N: usize> Collect<C> for [T; N] {
  #[inline]
  fn needs_trace() -> bool { T::needs_trace() }

  #[inline]
  fn trace(&self, ctx: &C, cc: &Collection) {
    for t in self {
      t.trace(ctx, cc)
    }
  }
}

macro_rules! impl_tuple {
    () => (
        unsafe impl<C> Collect<C> for () {
            #[inline]
            fn needs_trace() -> bool {
                false
            }
        }
    );

    ($($name:ident)+) => (
        unsafe impl<$($name,)* Ctx> Collect<Ctx> for ($($name,)*)
            where $($name: Collect<Ctx>,)*
        {
            #[inline]
            fn needs_trace() -> bool {
                $($name::needs_trace() ||)* false
            }

            #[allow(non_snake_case)]
            #[inline]
            fn trace(&self, ctx: &Ctx, cc: &Collection) {
                let ($($name,)*) = self;
                $($name.trace(ctx, cc);)*
            }
        }
    );
}

impl_tuple! {}
impl_tuple! {A}
impl_tuple! {A B}
impl_tuple! {A B C}
impl_tuple! {A B C D}
impl_tuple! {A B C D E}
impl_tuple! {A B C D E F}
impl_tuple! {A B C D E F G}
impl_tuple! {A B C D E F G H}
impl_tuple! {A B C D E F G H I}
impl_tuple! {A B C D E F G H I J}
impl_tuple! {A B C D E F G H I J K}
impl_tuple! {A B C D E F G H I J K L}
impl_tuple! {A B C D E F G H I J K L M}
impl_tuple! {A B C D E F G H I J K L M N}
impl_tuple! {A B C D E F G H I J K L M N O}
impl_tuple! {A B C D E F G H I J K L M N O P}
