use std::marker::PhantomData;

use rb_gc::Gc;
use rb_value::{RebarArgs, ValueType};

use crate::{GcArray, GcValue};

pub struct OwnedRebarArgsParser<'a> {
  args:   *const RebarArgs,
  offset: usize,

  _phantom: PhantomData<&'a ()>,
}

impl<'a> OwnedRebarArgsParser<'a> {
  pub fn new(args: *const RebarArgs) -> Self {
    OwnedRebarArgsParser { args, offset: 0, _phantom: PhantomData }
  }

  unsafe fn next(&mut self) -> i64 {
    let v = *(&*self.args).arg(self.offset) as i64;
    self.offset += 1;
    v
  }

  unsafe fn value_owned(&mut self, vt: ValueType) -> GcValue {
    match vt {
      ValueType::String => {
        let ptr = self.next();

        GcValue::String(Gc::from_ptr(ptr as *const String))
      }
      ValueType::Array => {
        let ptr = self.next();

        GcValue::Array(Gc::from_ptr(ptr as *const GcArray))
      }
      _ => unreachable!("not an owned value: {vt:?}"),
    }
  }

  /// Parses a value to get tracked by the GC. This value should not be dropped!
  pub unsafe fn value_owned_unsized(&mut self) -> GcValue {
    let ty = self.next();
    let vt = ValueType::try_from(ty).unwrap();
    self.value_owned(vt)
  }
}
