use alloc::boxed::Box;
use core::{f64, marker::PhantomData};

use crate::{
  context::{Context, EarlyStop, Finalization, Mutation, Phase},
  metrics::Metrics,
  Collect,
};

/// A trait that produces a [`Collect`]-able type for the given lifetime. This
/// is used to produce the root [`Collect`] instance in an [`Arena`].
///
/// In order to use an implementation of this trait in an [`Arena`], it must
/// implement `Rootable<'a>` for *any* possible `'a`. This is necessary so that
/// the `Root` types can be branded by the unique, invariant lifetimes that
/// makes an `Arena` sound.
pub trait Rootable<'a> {
  type Root: ?Sized + 'a;
}

/// A marker type used by the `Rootable!` macro instead of a bare trait object.
///
/// Prevents having to include extra ?Sized bounds on every `for<'a>
/// Rootable<'a>`.
#[doc(hidden)]
pub struct __DynRootable<T: ?Sized>(PhantomData<T>);

impl<'a, T: ?Sized + Rootable<'a>> Rootable<'a> for __DynRootable<T> {
  type Root = <T as Rootable<'a>>::Root;
}

/// A helper type alias for a `Rootable::Root` for a specific lifetime.
pub type Root<'a, R> = <R as Rootable<'a>>::Root;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum CollectionPhase {
  /// The arena is done with a collection cycle and is waiting to be restarted.
  Sleeping,
  /// The arena is currently tracing objects from the root to determine
  /// reachability.
  Marking,
  /// The arena has finished tracing, all reachable objects are marked. This may
  /// transition back to `Marking` if write barriers occur.
  Marked,
  /// The arena has determined a set of unreachable objects and has started
  /// freeing them. At this point, marking is no longer taking place so the
  /// root may have reachable, unmarked pointers.
  Sweeping,
}

/// A generic, garbage collected arena.
///
/// Garbage collected arenas allow for isolated sets of garbage collected
/// objects with zero-overhead garbage collected pointers. It provides
/// incremental mark and sweep garbage collection which must be manually
/// triggered outside the `mutate` method, and works best when units of work
/// inside `mutate` can be kept relatively small. It is designed primarily to be
/// a garbage collector for scripting language runtimes.
///
/// The arena API is able to provide extremely cheap Gc pointers because it is
/// based around "generativity". During construction and access, the root type
/// is branded by a unique, invariant lifetime `'gc` which ensures that `Gc`
/// pointers must be contained inside the root object hierarchy and cannot
/// escape the arena callbacks or be smuggled inside another arena. This way,
/// the arena can be sure that during mutation, all `Gc` pointers come from the
/// arena we expect them to come from, and that they're all either reachable
/// from root or have been allocated during the current `mutate` call. When not
/// inside the `mutate` callback, the arena knows that all `Gc` pointers must be
/// either reachable from root or they are unreachable and safe to collect. In
/// this way, incremental garbage collection can be achieved (assuming
/// "sufficiently small" calls to `mutate`) that is both extremely safe and zero
/// overhead vs what you would write in C with raw pointers and manually
/// ensuring that invariants are held.
pub struct Arena<R>
where
  R: for<'a> Rootable<'a>,
{
  context: Box<Context>,
  root:    Root<'static, R>,
}

impl<R> Arena<R>
where
  R: for<'a> Rootable<'a>,
  for<'a> Root<'a, R>: Sized,
{
  /// Create a new arena with the given garbage collector tuning parameters. You
  /// must provide a closure that accepts a `&Mutation<'gc>` and returns the
  /// appropriate root.
  pub fn new<F>(f: F) -> Arena<R>
  where
    F: for<'gc> FnOnce(&'gc Mutation) -> Root<'gc, R>,
  {
    unsafe {
      let context = Box::new(Context::new());
      // Note - we cast the `&Mutation` to a `'static` lifetime here,
      // instead of transmuting the root type returned by `f`. Transmuting the root
      // type is allowed in nightly versions of rust
      // (see https://github.com/rust-lang/rust/pull/101520#issuecomment-1252016235)
      // but is not yet stable. Casting the `&Mutation` is completely invisible
      // to the callback `f` (since it needs to handle an arbitrary lifetime),
      // and lets us stay compatible with older versions of Rust
      let mc: &'static Mutation = &*(context.mutation_context() as *const _);
      let root: Root<'static, R> = f(mc);
      Arena { context, root }
    }
  }

  /// Similar to `new`, but allows for constructor that can fail.
  pub fn try_new<F, E>(f: F) -> Result<Arena<R>, E>
  where
    F: for<'gc> FnOnce(&'gc Mutation) -> Result<Root<'gc, R>, E>,
  {
    unsafe {
      let context = Box::new(Context::new());
      let mc: &'static Mutation = &*(context.mutation_context() as *const _);
      let root: Root<'static, R> = f(mc)?;
      Ok(Arena { context, root })
    }
  }

  #[inline]
  pub fn map_root<R2>(
    self,
    f: impl for<'gc> FnOnce(&'gc Mutation, Root<'gc, R>) -> Root<'gc, R2>,
  ) -> Arena<R2>
  where
    R2: for<'a> Rootable<'a>,
    for<'a> Root<'a, R2>: Sized,
  {
    self.context.root_barrier();
    let new_root: Root<'static, R2> = unsafe {
      let mc: &'static Mutation = &*(self.context.mutation_context() as *const _);
      f(mc, self.root)
    };
    Arena { context: self.context, root: new_root }
  }

  #[inline]
  pub fn try_map_root<R2, E>(
    self,
    f: impl for<'gc> FnOnce(&'gc Mutation, Root<'gc, R>) -> Result<Root<'gc, R2>, E>,
  ) -> Result<Arena<R2>, E>
  where
    R2: for<'a> Rootable<'a>,
    for<'a> Root<'a, R2>: Sized,
  {
    self.context.root_barrier();
    let new_root: Root<'static, R2> = unsafe {
      let mc: &'static Mutation = &*(self.context.mutation_context() as *const _);
      f(mc, self.root)?
    };
    Ok(Arena { context: self.context, root: new_root })
  }
}

impl<R> Arena<R>
where
  R: for<'a> Rootable<'a>,
{
  /// The primary means of interacting with a garbage collected arena. Returns a
  /// `&Mutation`, which can be used to mutate any part of the object graph.
  /// Garbage collection may not take place until the `&Mutation` is done
  /// being used.
  pub fn mutate(&self) -> &Mutation { unsafe { &*(self.context.mutation_context() as *const _) } }
  pub fn root(&self) -> &Root<'_, R> { unsafe { std::mem::transmute(&*(&self.root as *const _)) } }

  /// An alternative version of [`Arena::mutate`] which allows mutating the root
  /// set, at the cost of an extra write barrier.
  pub fn mutate_root(&mut self) -> (&Mutation, &mut Root<'_, R>) {
    self.context.root_barrier();
    unsafe {
      (
        &*(self.context.mutation_context() as *const _),
        std::mem::transmute(&mut *(&mut self.root as *mut _)),
      )
    }
  }

  #[inline]
  pub fn metrics(&self) -> &Metrics { self.context.metrics() }

  #[inline]
  pub fn collection_phase(&self) -> CollectionPhase {
    match self.context.phase() {
      Phase::Mark => {
        if self.context.gray_remaining() {
          CollectionPhase::Marking
        } else {
          CollectionPhase::Marked
        }
      }
      Phase::Sweep => CollectionPhase::Sweeping,
      Phase::Sleep => CollectionPhase::Sleeping,
      Phase::Drop => unreachable!(),
    }
  }
}

impl<R> Arena<R>
where
  R: for<'a> Rootable<'a>,
{
  /// Run incremental garbage collection until the allocation debt is <= 0.0.
  ///
  /// There is no minimum unit of work enforced here, so it may be faster to
  /// only call this method when the allocation debt is above some threshold.
  ///
  /// This method will always return at least once when collection enters the
  /// `Sleeping` phase, i.e. it will never transition from the `Sweeping`
  /// phase to the `Marking` phase without returning in-between.
  #[inline]
  pub fn collect_debt<C>(&mut self, ctx: &C)
  where
    for<'a> Root<'a, R>: Collect<C>,
  {
    unsafe {
      self.context.do_collection(&self.root, ctx, 0.0, None);
    }
  }

  /// Run only the *marking* part of incremental garbage collection until
  /// allocation debt is <= 0.0.
  ///
  /// This does *not* transition collection past the `Marked` phase. Does
  /// nothing if the collection phase is `Marked` or `Sweeping`, otherwise
  /// acts like `Arena::collect_debt`.
  #[inline]
  pub fn mark_debt<C>(&mut self, ctx: &C) -> Option<MarkedArena<'_, R>>
  where
    for<'a> Root<'a, R>: Collect<C>,
  {
    if matches!(self.context.phase(), Phase::Mark | Phase::Sleep) {
      unsafe {
        self.context.do_collection(&self.root, ctx, 0.0, Some(EarlyStop::BeforeSweep));
      }
    }

    if self.context.phase() == Phase::Mark && !self.context.gray_remaining() {
      Some(MarkedArena(self))
    } else {
      None
    }
  }

  /// Run the current garbage collection cycle to completion, stopping once
  /// garbage collection has restarted in the sleep phase. If the collector is
  /// currently in the sleep phase, this restarts the collection and performs
  /// a full collection before transitioning back to the sleep phase.
  #[inline]
  pub fn collect_all<C>(&mut self, ctx: &C)
  where
    for<'a> Root<'a, R>: Collect<C>,
  {
    unsafe {
      self.context.do_collection(&self.root, ctx, f64::NEG_INFINITY, None);
    }
  }

  /// Runs all of the remaining *marking* part of the current garbage collection
  /// cycle.
  ///
  /// Similarly to `Arena::mark_debt`, this does not transition collection  past
  /// the `Marked` phase, and does nothing if the collector is currently in
  /// the `Marked` phase or the `Sweeping` phase.
  #[inline]
  pub fn mark_all<C>(&mut self, ctx: &C) -> Option<MarkedArena<'_, R>>
  where
    for<'a> Root<'a, R>: Collect<C>,
  {
    if matches!(self.context.phase(), Phase::Mark | Phase::Sleep) {
      unsafe {
        self.context.do_collection(
          &self.root,
          ctx,
          f64::NEG_INFINITY,
          Some(EarlyStop::BeforeSweep),
        );
      }
    }

    if self.context.phase() == Phase::Mark && !self.context.gray_remaining() {
      Some(MarkedArena(self))
    } else {
      None
    }
  }
}

pub struct MarkedArena<'a, R: for<'b> Rootable<'b>>(&'a mut Arena<R>);

impl<'a, R> MarkedArena<'a, R>
where
  R: for<'b> Rootable<'b>,
{
  /// Examine the state of a fully marked arena.
  ///
  /// Allows you to determine whether `GcWeak` pointers are "dead" (aka,
  /// soon-to-be-dropped) and potentially resurrect them for this cycle.
  ///
  /// Note that the arena is guaranteed to be *fully marked* only at the
  /// *beginning* of this callback, any mutation that resurrects a pointer or
  /// triggers a write barrier can immediately invalidate this.
  #[inline]
  pub fn finalize<F, T>(self, f: F) -> T
  where
    F: for<'gc> FnOnce(&'gc Finalization, &'gc Root<'gc, R>) -> T,
  {
    unsafe {
      let mc: &'static Finalization = &*(self.0.context.finalization_context() as *const _);
      let root: &'static Root<'_, R> = &*(&self.0.root as *const _);
      f(mc, root)
    }
  }

  /// Immediately transition the arena out of [`CollectionPhase::Marked`] to
  /// [`CollectionPhase::Sweeping`].
  #[inline]
  pub fn start_sweeping<C>(self, ctx: &C)
  where
    for<'b> Root<'b, R>: Collect<C>,
  {
    unsafe {
      self.0.context.do_collection(
        &self.0.root,
        ctx,
        f64::NEG_INFINITY,
        Some(EarlyStop::AfterSweep),
      );
    }
    assert_eq!(self.0.context.phase(), Phase::Sweep);
  }
}

/// Create a temporary arena without a root object and perform the given
/// operation on it.
///
/// No garbage collection will be done until the very end of the call, at which
/// point all allocations will be collected.
///
/// This is a convenience function that makes it a little easier to quickly test
/// code that uses `gc-arena`, it is not very useful on its own.
pub fn rootless_mutate<F, R>(f: F) -> R
where
  F: for<'gc> FnOnce(&'gc Mutation) -> R,
{
  unsafe {
    let context = Context::new();
    f(context.mutation_context())
  }
}
