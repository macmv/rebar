use std::fmt;

use crate::{slice::RbSlice, RbStruct};

/// A value with references to rebar values. This typically has the lifetime of
/// the native rust function that is being passed this value.
#[derive(Debug, PartialEq)]
pub enum Value<'a> {
  Nil,
  Int(i64),
  Bool(bool),
  String(&'a String),
  Array(RbSlice<'a>),
  Struct(RbStruct<'a>),
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

impl fmt::Display for Value<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Value::Nil => write!(f, "nil"),
      Value::Int(i) => write!(f, "{}", i),
      Value::Bool(b) => write!(f, "{}", b),
      Value::String(s) => write!(f, "{}", s),
      Value::Array(arr) => {
        write!(f, "[")?;
        for (i, elem) in arr.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{elem}")?;
        }
        write!(f, "]")
      }
      Value::Struct(s) => write!(f, "{s:?}"),
    }
  }
}
