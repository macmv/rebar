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

impl Value<'_> {
  pub fn as_int(&self) -> i64 {
    match self {
      Value::Int(i) => *i,
      _ => panic!("expected int"),
    }
  }

  pub fn as_bool(&self) -> bool {
    match self {
      Value::Bool(b) => *b,
      _ => panic!("expected bool"),
    }
  }

  pub fn as_str(&self) -> &str {
    match self {
      Value::String(s) => s,
      _ => panic!("expected str"),
    }
  }
}

impl OwnedValue {
  pub fn as_int(&self) -> i64 {
    match self {
      OwnedValue::Int(i) => *i,
      _ => panic!("expected int"),
    }
  }

  pub fn as_bool(&self) -> bool {
    match self {
      OwnedValue::Bool(b) => *b,
      _ => panic!("expected bool"),
    }
  }

  pub fn as_str(&self) -> &str {
    match self {
      OwnedValue::String(s) => s,
      _ => panic!("expected str"),
    }
  }
}
