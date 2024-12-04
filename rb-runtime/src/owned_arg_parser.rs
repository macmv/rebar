use rb_gc::Gc;
use rb_mir::MirContext;
use rb_value::{DynamicValueType, RebarArgs, ValueType};

use crate::{gc_value::GcStruct, GcArray, GcValue};

pub struct OwnedRebarArgsParser<'a> {
  ctx: &'a MirContext,

  args:              *const RebarArgs,
  pub(crate) offset: usize,
}

impl<'a> OwnedRebarArgsParser<'a> {
  pub fn new(ctx: &'a MirContext, args: *const RebarArgs) -> Self {
    OwnedRebarArgsParser { ctx, args, offset: 0 }
  }

  unsafe fn next(&mut self) -> i64 {
    let v = *(&*self.args).arg(self.offset) as i64;
    self.offset += 1;
    v
  }

  pub(crate) unsafe fn value_owned(&mut self, vt: ValueType) -> GcValue {
    match vt {
      ValueType::String => {
        let ptr = self.next();

        GcValue::String(Gc::from_ptr(ptr as *const String))
      }
      ValueType::Array => {
        let ptr = self.next();

        GcValue::Array(Gc::from_ptr(ptr as *const GcArray))
      }

      ValueType::Struct(id) => {
        let strct = &self.ctx.structs[&id];

        let ptr = (&*self.args).arg(self.offset) as *const RebarArgs;

        for (_, ty) in strct.fields.iter() {
          match DynamicValueType::for_type(self.ctx, ty) {
            DynamicValueType::Const(vt) => match vt {
              ValueType::Int => self.offset += 1,

              ValueType::String | ValueType::Array => {
                self.value_owned(vt);
              }

              _ => todo!("skip const value: {vt:?}"),
            },
            DynamicValueType::Union(len) => {
              self.offset += 1; // Type slot
              self.offset += len as usize; // Ignore the whole value.
            }
          }
        }

        GcValue::Struct(GcStruct { ctx: std::mem::transmute(self.ctx), strct: strct.clone(), ptr })
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
