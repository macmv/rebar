use line_index::LineCol;
use rb_syntax::TextRange;

use crate::{sources::SourceId, Sources};

pub struct Diagnostic {
  pub message: String,
  pub span:    Span,
}

pub struct Span {
  pub file:  SourceId,
  pub range: TextRange,
}

impl Diagnostic {
  pub fn error(message: impl Into<String>, span: Span) -> Self {
    Diagnostic { message: message.into(), span }
  }

  pub fn render(&self, sources: &Sources) -> String {
    let source = &sources[self.span.file];

    let mut lines = source.line_index.lines(self.span.range);
    if lines.next().is_some() {
      // Multi-line span
      let _lines = source.line_index.lines(self.span.range);

      // TODO
      "".into()
    } else {
      let line = source.line_index.line_col(self.span.range.start()).line;
      let start = source.line_index.offset(LineCol { line, col: 0 }).unwrap();
      let end = source.line_index.offset(LineCol { line: line + 1, col: 0 }).unwrap();

      let line = &source.source[u32::from(start) as usize..u32::from(end) as usize];

      format!("{}\n{}", line, self.message)
    }
  }
}
