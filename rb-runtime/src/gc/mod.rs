use std::{collections::HashMap, thread::ThreadId};

use gc_arena::{Arena, Collect, Gc, Rootable};

mod value;

pub use value::{GcValue, RString};

#[derive(Collect)]
#[collect(no_drop)]
pub struct GcRoot<'gc> {
  /// Stores all the GC'able objects on each thread's stack.
  ///
  /// JIT compiled functions will push/pop to this stack
  threads: HashMap<u64, Stack<'gc>>,
}

#[derive(Default, Collect)]
#[collect(no_drop)]
struct Stack<'gc> {
  frames: Vec<Frame<'gc>>,
}

#[derive(Default, Collect)]
#[collect(no_drop)]
struct Frame<'gc> {
  values: Vec<Gc<'gc, GcValue>>,
}

#[test]
fn gc_works() {
  type MyArena = Arena<Rootable![GcRoot<'_>]>;

  let mut arena = MyArena::new(|_| GcRoot { threads: HashMap::new() });

  let tid = 3; // I am thread 3 (FIXME: use `ThreadId`)

  arena.mutate_root(|m, root| {
    let thread = root.threads.entry(tid).or_insert_with(Stack::default);

    // When a function begins, this is called.
    thread.frames.push(Frame::default());

    // When a value like `Value::String` is created, it's inserted into the current
    // frame.
    thread.frames.last_mut().unwrap().values.push(Gc::new(m, GcValue::String("hello".into())));

    // When a function returns, this is called.
    thread.frames.pop().unwrap();
  });
}
