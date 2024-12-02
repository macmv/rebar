use std::fmt;

use rb_mir::{ast::StructId, MirContext};
use rb_value::DynamicValueType;

use crate::{RebarArgsParser, Value};

pub struct RbStruct<'a> {
  ctx: &'a MirContext,
  id:  StructId,
  ptr: *const i64,
}

pub struct FieldsIter<'a> {
  ctx:    &'a MirContext,
  strct:  &'a rb_mir::Struct,
  parser: RebarArgsParser<'a>,
  idx:    usize,
}

impl<'a> RbStruct<'a> {
  pub fn new(ctx: &'a MirContext, id: StructId, ptr: *const i64) -> Self {
    RbStruct { ctx, id, ptr }
  }

  pub fn len(&self) -> usize { self.ctx.structs[&self.id].fields.len() }

  pub fn fields(&self) -> FieldsIter<'a> {
    let strct = &self.ctx.structs[&self.id];
    let parser = RebarArgsParser::new(self.ctx, self.ptr as *const _);

    FieldsIter { ctx: self.ctx, strct, parser, idx: 0 }
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

impl fmt::Debug for RbStruct<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut s = f.debug_struct("RbStruct");
    unsafe {
      let strct = &self.ctx.structs[&self.id];
      let mut parser = RebarArgsParser::new(self.ctx, self.ptr as *const _);

      for field in &strct.fields {
        s.field("foo", &parser.value(DynamicValueType::for_type(self.ctx, &field.1)));
      }
    }

    s.finish()
  }
}

impl PartialEq for RbStruct<'_> {
  fn eq(&self, other: &Self) -> bool {
    if self.id != other.id {
      return false;
    }

    let a = self.fields();
    let b = other.fields();

    // The length must be the same if the IDs are the same.
    a.zip(b).all(|(a, b)| a == b)
  }
}
