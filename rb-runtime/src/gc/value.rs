use gc_arena::Collect;

#[derive(Collect)]
#[collect(no_drop)]
pub enum GcValue {
  String(String),
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

pub struct RStr {
  pointer: *const u8,
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

  pub fn as_str(&self) -> RStr {
    // SAFETY: `self.pointer` is a valid pointer to a length-prefixed string.
    unsafe { RStr::from_ptr(self.pointer.as_ptr()) }
  }
}

impl RStr {
  pub unsafe fn from_ptr(ptr: *const u8) -> Self { Self { pointer: ptr } }

  pub fn as_str(&self) -> &str {
    let len = u64::from_le_bytes(unsafe { *(self.pointer as *const [u8; 8]) }) as usize;
    let ptr = unsafe { self.pointer.add(8) };

    unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, len)) }
  }
}
