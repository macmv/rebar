use rowan::{TextRange, TextSize};

#[derive(Debug, PartialEq, Eq)]
pub struct SyntaxError {
  message: String,
  range:   TextRange,
}

impl SyntaxError {
  pub fn new(message: impl Into<String>, range: TextRange) -> Self {
    SyntaxError { message: message.into(), range }
  }

  pub fn new_at_offset(error: impl Into<String>, offset: TextSize) -> Self {
    Self::new(error, TextRange::empty(offset))
  }

  pub fn message(&self) -> &str { &self.message }
  pub fn span(&self) -> TextRange { self.range }
}
