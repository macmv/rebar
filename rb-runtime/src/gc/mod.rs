use std::collections::HashMap;

use gc_arena::{lock::GcRefLock, Arena, Collect, Gc, Rootable};

mod value;

use crate::GcValue;

#[derive(Collect)]
#[collect(no_drop)]
pub struct GcRoot<'gc> {
  /// Stores all the GC'able objects on each thread's stack.
  ///
  /// JIT compiled functions will push/pop to this stack
  pub threads: HashMap<u64, Stack<'gc>>,
}

pub type GcArena = Arena<Rootable![GcRoot<'_>]>;

#[derive(Default, Collect)]
#[collect(no_drop)]
pub struct Stack<'gc> {
  pub frames: Vec<GcRefLock<'gc, Frame<'gc>>>,
}

#[derive(Default, Collect)]
#[collect(no_drop)]
pub struct Frame<'gc> {
  pub values: Vec<Gc<'gc, GcValue<'gc>>>,
}

/// An opaque ID for a GC'ed object. This is usually just the pointer to the
/// heap-allocated object.
#[derive(Default, Collect, Clone, Copy, PartialEq, Eq, Hash)]
#[collect(no_drop)]
pub struct GcId(pub u64);

#[test]
fn gc_works() {
  use gc_arena::lock::RefLock;

  type MyArena = Arena<Rootable![GcRoot<'_>]>;

  let mut arena = MyArena::new(|_| GcRoot { threads: HashMap::new() });

  let tid = 3; // I am thread 3 (FIXME: use `ThreadId`)

  arena.mutate_root(|m, root| {
    let thread = root.threads.entry(tid).or_insert_with(Stack::default);

    // When a function begins, this is called.
    thread.frames.push(Gc::new(m, RefLock::new(Frame::default())));

    // When a value like `Value::String` is created, it's inserted into the current
    // frame (note that we don't need mutable access here).
    let v = GcValue::String("hello".into());
    thread.frames.last().unwrap().borrow_mut(m).values.push(Gc::new(m, v));

    // When a function returns, this is called.
    thread.frames.pop().unwrap();
  });
}
