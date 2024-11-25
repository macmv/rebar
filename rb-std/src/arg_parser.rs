use std::marker::PhantomData;

use rb_value::{DynamicValueType, RbArray, RebarArgs, ValueType};

use crate::{slice::RbSlice, value::Value};

pub struct RebarArgsParser<'a> {
  args:   *const RebarArgs,
  offset: usize,

  _phantom: PhantomData<&'a ()>,
}

impl<'a> RebarArgsParser<'a> {
  pub fn new(args: *const RebarArgs) -> Self {
    RebarArgsParser { args, offset: 0, _phantom: PhantomData }
  }

  unsafe fn next(&mut self) -> i64 {
    let v = *(&*self.args).arg(self.offset) as i64;
    self.offset += 1;
    v
  }

  unsafe fn value_const(&mut self, vt: ValueType) -> Value<'a> {
    match vt {
      ValueType::Nil => Value::Nil,
      // Booleans only use 8 bits, so cast the value to a u8 and just compare that.
      ValueType::Bool => {
        // The value will always take up 8 bytes, even if less bytes are used.
        Value::Bool(self.next() as u8 != 0)
      }
      ValueType::Int => Value::Int(self.next()),
      ValueType::String => {
        let ptr = self.next();

        // NB: `ptr` is a pointer from `rb-gc`.
        let gc = &*(ptr as *const String);

        Value::String(::std::mem::transmute(gc.as_str()))
      }
      ValueType::Array => {
        let ptr = self.next();

        // NB: `ptr` is a pointer from `rb-gc` to a `GcArray`.
        //
        // TODO: Get `GcArray` in here!
        #[repr(C)]
        struct GcArrayTmp {
          arr: RbArray,
          vt:  DynamicValueType,
        }

        let arr = &*(ptr as *const GcArrayTmp);

        Value::Array(RbSlice::new(&arr.arr, arr.vt))
      }
      v => unimplemented!("{v:?}"),
    }
  }

  /*
  unsafe fn value_owned(&mut self, vt: ValueType) -> GcValue {
    match vt {
      ValueType::String => {
        let ptr = self.next();

        let gc = Gc::from_ptr(ptr as *const String);

        GcValue::String(gc)
      }
      ValueType::Array => {
        let ptr = self.next();

        GcValue::Array(Gc::from_ptr(ptr as *const GcArray))
      }
      _ => unreachable!("not an owned value: {vt:?}"),
    }
  }
  */

  pub unsafe fn value(&mut self, dvt: DynamicValueType) -> Value<'a> {
    let start = self.offset;
    let v = match dvt {
      DynamicValueType::Const(vt) => self.value_const(vt),
      DynamicValueType::Union(_) => {
        // A nil will only take up one slot, so we must check for that to avoid reading
        // out of bounds.
        let dyn_ty = self.next();

        let vt = ValueType::try_from(dyn_ty).unwrap();

        self.value_const(vt)
      }
    };

    let expected_end = start + dvt.len() as usize;
    if self.offset < expected_end {
      self.offset = expected_end;
    } else if self.offset > expected_end {
      panic!("read too many slots while parsing argument of type {dvt:?}");
    }

    v
  }

  /// Parses a single value, and renders the current parser unusable. If the
  /// value passed in changes type, the amount of slots parsed could change,
  /// which makes this inconsistent. So, after calling this, a subsequent
  /// value cannot be parsed.
  pub unsafe fn value_unsized(&mut self) -> Value<'a> {
    let ty = self.next();
    let vt = ValueType::try_from(ty).unwrap();
    self.value_const(vt)
  }

  /*
  /// Parses a value to get tracked by the GC. This value should not be dropped!
  pub unsafe fn value_owned_unsized(&mut self) -> GcValue {
    let ty = self.next();
    let vt = ValueType::try_from(ty).unwrap();
    self.value_owned(vt)
  }
  */
}
