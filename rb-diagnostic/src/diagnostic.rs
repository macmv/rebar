use std::fmt;

pub struct Diagnostic {
  pub message: String,
  pub span:    rb_syntax::TextRange,
}

impl fmt::Display for Diagnostic {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "{} at {:?}", self.message, self.span)
  }
}
