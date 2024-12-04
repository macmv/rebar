use std::fmt;

use rb_mir::{ast::StructId, MirContext};
use rb_value::DynamicValueType;

use crate::{RebarArgsParser, Value};

#[derive(Clone, Copy)]
pub struct RbStruct {
  pub id:  StructId,
  pub ptr: *const i64,
}

pub struct FieldsIter<'a> {
  ctx:    &'a MirContext,
  strct:  &'a rb_mir::Struct,
  parser: RebarArgsParser<'a>,
  idx:    usize,
}

impl RbStruct {
  pub fn new(id: StructId, ptr: *const i64) -> Self { RbStruct { id, ptr } }

  pub fn len(&self, ctx: &MirContext) -> usize { ctx.structs[&self.id].fields.len() }

  pub fn fields<'a>(&self, ctx: &'a MirContext) -> FieldsIter<'a> {
    let strct = &ctx.structs[&self.id];
    let parser = RebarArgsParser::new(ctx, self.ptr as *const _);

    FieldsIter { ctx, strct, parser, idx: 0 }
  }
}

impl<'a> Iterator for FieldsIter<'a> {
  type Item = Value<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.idx >= self.strct.fields.len() {
      return None;
    }

    let value = unsafe {
      self.parser.value(DynamicValueType::for_type(self.ctx, &self.strct.fields[self.idx].1))
    };
    self.idx += 1;

    Some(value)
  }
}

impl fmt::Debug for RbStruct {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut s = f.debug_struct("RbStruct");

    // FIXME
    /*
    unsafe {
      let strct = &self.ctx.structs[&self.id];
      let mut parser = RebarArgsParser::new(self.ctx, self.ptr as *const _);

      for field in &strct.fields {
        s.field("foo", &parser.value(DynamicValueType::for_type(self.ctx, &field.1)));
      }
    }
    */

    s.finish()
  }
}

impl PartialEq for RbStruct {
  fn eq(&self, _other: &Self) -> bool {
    // FIXME
    /*
    if self.id != other.id {
      return false;
    }

    let a = self.fields();
    let b = other.fields();

    // The length must be the same if the IDs are the same.
    a.zip(b).all(|(a, b)| a == b)
    */
    false
  }
}
