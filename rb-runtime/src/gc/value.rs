use gc_arena::Collect;

#[derive(Collect)]
#[collect(no_drop)]
pub enum GcValue {
  String(RString),
}

/// Stores a string in a single pointer. This pointer is used by the rebar
/// runtime to refer to a string.
///
/// SAFETY: This value is typically stored in a GcRoot. This value must stay
/// alive as long as the rebar runtime refers to this string.
#[derive(Collect)]
#[collect(no_drop)]
pub struct RString {
  pointer: Box<[u8]>,
}

impl From<&str> for RString {
  fn from(s: &str) -> Self { RString::new(s) }
}

impl GcValue {
  pub fn as_ptr(&self) -> *const u8 {
    match self {
      GcValue::String(s) => s.as_ptr(),
    }
  }
}

impl RString {
  pub fn new(content: &str) -> Self {
    let mut bytes = vec![0; content.len() + 8];
    bytes[0..8].copy_from_slice(&(content.len() as u64).to_le_bytes());
    bytes[8..].copy_from_slice(content.as_bytes());

    Self { pointer: bytes.into_boxed_slice() }
  }

  pub fn as_ptr(&self) -> *const u8 { self.pointer.as_ptr() }
}
