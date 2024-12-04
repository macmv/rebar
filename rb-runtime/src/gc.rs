use std::collections::HashMap;

use rb_gc::{lock::GcRefLock, Arena, Collect, Collection, Gc};
use rb_mir::MirContext;

use crate::GcValue;

pub struct GcRoot<'ctx> {
  /// Stores all the GC'able objects on each thread's stack.
  ///
  /// JIT compiled functions will push/pop to this stack
  pub threads: HashMap<u64, Stack<'ctx>>,
}

unsafe impl Collect<MirContext> for GcRoot<'_> {
  fn trace(&self, ctx: &MirContext, cc: &Collection) { self.threads.trace(ctx, cc); }
}

pub type GcArena =
  Arena<rb_gc::__DynRootable<dyn for<'gc> rb_gc::Rootable<'gc, Root = GcRoot<'gc>>>>;

#[derive(Default)]
pub struct Stack<'ctx> {
  pub frames: Vec<GcRefLock<Frame<'ctx>>>,
}

unsafe impl Collect<MirContext> for Stack<'_> {
  fn trace(&self, ctx: &MirContext, cc: &Collection) { self.frames.trace(ctx, cc); }
}

#[derive(Default)]
pub struct Frame<'ctx> {
  pub values: Vec<Gc<GcValue<'ctx>>>,
}

unsafe impl Collect<MirContext> for Frame<'_> {
  fn trace(&self, ctx: &MirContext, cc: &Collection) { self.values.trace(ctx, cc); }
}

#[test]
fn gc_works() {
  use rb_gc::lock::RefLock;

  type MyArena = Arena<rb_gc::__DynRootable<dyn for<'gc> rb_gc::Rootable<'gc, Root = GcRoot<'gc>>>>;

  let mut arena = MyArena::new(|_| GcRoot { threads: HashMap::new() });

  let tid = 3; // I am thread 3 (FIXME: use `ThreadId`)

  let (m, root) = arena.mutate_root();
  let thread = root.threads.entry(tid).or_insert_with(Stack::default);

  // When a function begins, this is called.
  thread.frames.push(Gc::new(m, RefLock::new(Frame::default())));

  // When a value like `Value::String` is created, it's inserted into the current
  // frame (note that we don't need mutable access here).
  let v = GcValue::String(Gc::new::<()>(m, "hello".into()));
  thread.frames.last().unwrap().borrow_mut(m).values.push(Gc::new(m, v));

  // When a function returns, this is called.
  thread.frames.pop().unwrap();
}
