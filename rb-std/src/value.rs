use crate::slice::RbSlice;

/// A value with references to rebar values. This typically has the lifetime of
/// the native rust function that is being passed this value.
#[derive(Debug, PartialEq)]
pub enum Value<'a> {
  Nil,
  Int(i64),
  Bool(bool),
  String(&'a str),
  Array(RbSlice<'a>),
}

/// An owned value, created from rust, that will be passed back to rebar.
#[derive(Debug, PartialEq)]
pub enum OwnedValue {
  Nil,
  Int(i64),
  Bool(bool),
  String(String),
  Array(Vec<i64>),
}
