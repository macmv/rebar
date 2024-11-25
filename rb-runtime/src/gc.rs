use std::collections::HashMap;

use rb_gc::{lock::GcRefLock, Arena, Collect, Collection, Gc};

use crate::intrinsics::GcValue;

pub struct GcRoot {
  /// Stores all the GC'able objects on each thread's stack.
  ///
  /// JIT compiled functions will push/pop to this stack
  pub threads: HashMap<u64, Stack>,
}

unsafe impl Collect for GcRoot {
  fn trace(&self, cc: &Collection) { self.threads.trace(cc); }
}

pub type GcArena = Arena<rb_gc::__DynRootable<dyn for<'gc> rb_gc::Rootable<'gc, Root = GcRoot>>>;

#[derive(Default)]
pub struct Stack {
  pub frames: Vec<GcRefLock<Frame>>,
}

unsafe impl Collect for Stack {
  fn trace(&self, cc: &Collection) { self.frames.trace(cc); }
}

#[derive(Default)]
pub struct Frame {
  pub values: Vec<Gc<GcValue>>,
}

unsafe impl Collect for Frame {
  fn trace(&self, cc: &Collection) { self.values.trace(cc); }
}

#[test]
fn gc_works() {
  use rb_gc::lock::RefLock;

  type MyArena = Arena<rb_gc::__DynRootable<dyn for<'gc> rb_gc::Rootable<'gc, Root = GcRoot>>>;

  let mut arena = MyArena::new(|_| GcRoot { threads: HashMap::new() });

  let tid = 3; // I am thread 3 (FIXME: use `ThreadId`)

  let (m, root) = arena.mutate_root();
  let thread = root.threads.entry(tid).or_insert_with(Stack::default);

  // When a function begins, this is called.
  thread.frames.push(Gc::new(m, RefLock::new(Frame::default())));

  // When a value like `Value::String` is created, it's inserted into the current
  // frame (note that we don't need mutable access here).
  let v = GcValue::String(Gc::new(m, "hello".into()));
  thread.frames.last().unwrap().borrow_mut(m).values.push(Gc::new(m, v));

  // When a function returns, this is called.
  thread.frames.pop().unwrap();
}
