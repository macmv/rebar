use std::fmt;

use rb_value::{DynamicValueType, RbArray, RebarArgs};

use crate::RebarArgsParser;

use super::Value;

/// The rust-friendly version of an `RbArray`.
pub struct RbSlice<'a> {
  // SAFETY: This `&RbArray` is quite special: the value of this reference is garunteed to also be
  // a valid `Box<RbArray>` pointer, and that pointer is used as a key in the garbage collector to
  // determine if the array is referenced or not.
  pub elems: &'a RbArray,
  pub vt:    DynamicValueType,
}

impl<'a> RbSlice<'a> {
  pub fn new(elems: &'a RbArray, vt: DynamicValueType) -> Self {
    assert!(
      elems.len() % vt.len() as usize == 0,
      "array length {} must be a multiple of the slot size {} for the type {:?}",
      elems.len(),
      vt.len(),
      vt
    );

    Self { elems, vt }
  }

  pub fn as_ptr(&self) -> *const i64 { self.elems.as_ptr() }

  pub fn iter(&self) -> ValueIter {
    ValueIter {
      parser: RebarArgsParser::new(self.elems.as_ptr() as *const RebarArgs),
      vt:     self.vt,

      idx: 0,
      len: self.len(),
    }
  }

  pub fn len(&self) -> usize { self.elems.len() / self.vt.len() as usize }
}

impl PartialEq for RbSlice<'_> {
  fn eq(&self, other: &Self) -> bool { self.iter().eq(other.iter()) }
}
impl Eq for RbSlice<'_> {}

impl fmt::Debug for RbSlice<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_list().entries(self.iter()).finish()
  }
}

pub struct ValueIter<'a> {
  parser: RebarArgsParser<'a>,
  vt:     DynamicValueType,

  idx: usize,
  len: usize,
}

impl<'a> Iterator for ValueIter<'a> {
  type Item = Value<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.idx == self.len {
      return None;
    }

    self.idx += 1;
    unsafe { Some(self.parser.value(self.vt)) }
  }
}
