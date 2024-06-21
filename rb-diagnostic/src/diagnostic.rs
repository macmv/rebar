use line_index::LineCol;
use rb_syntax::TextRange;
use std::fmt::Write;

use crate::{sources::SourceId, Sources};

pub struct Diagnostic {
  pub message: String,
  pub span:    Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    let _ = lines.next();
    if lines.next().is_some() {
      let start = source.line_index.line_col(self.span.range.start());
      let start_line_num = start.line + 1;
      let start_col_num = start.col + 1;

      let end = source.line_index.line_col(self.span.range.end());
      let end_line_num = end.line + 1;
      let _end_col_num = end.col + 1;

      let margin_str = " ".repeat(end_line_num.ilog10() as usize + 1);

      let mut out = String::new();

      writeln!(out, "error: {}", self.message).unwrap();
      writeln!(out, "{}--> {}:{}:{}", margin_str, source.name, start_line_num, start_col_num)
        .unwrap();

      let lines = source.line_index.lines(self.span.range);
      for line in lines {
        let pos = source.line_index.line_col(line.start());
        let line_num = pos.line + 1;
        let _col_num = pos.col + 1;

        let line_str = &source.source[line].trim();

        writeln!(out, "{} | {}", line_num, line_str).unwrap();
      }

      out
    } else {
      let pos = source.line_index.line_col(self.span.range.start());
      let line_num = pos.line + 1;
      let col_num = pos.col + 1;

      let start_col = pos.col as usize;
      let mut end_col = source.line_index.line_col(self.span.range.end()).col as usize;
      if start_col == end_col {
        end_col += 1;
      }

      let start =
        u32::from(source.line_index.offset(LineCol { line: pos.line, col: 0 }).unwrap()) as usize;
      let end = u32::from(source.line_index.offset(LineCol { line: pos.line + 1, col: 0 }).unwrap())
        as usize;

      let line_str = &source.source[start..end].trim();

      let margin_str = " ".repeat(line_num.ilog10() as usize + 1);
      let underline_str = format!("{}{}", " ".repeat(start_col), "^".repeat(end_col - start_col));

      let mut out = String::new();

      writeln!(out, "error: {}", self.message).unwrap();
      writeln!(out, "{}--> {}:{}:{}", margin_str, source.name, line_num, col_num).unwrap();
      writeln!(out, "{} |", margin_str).unwrap();
      writeln!(out, "{} | {}", line_num, line_str).unwrap();
      writeln!(out, "{} | {}", margin_str, underline_str).unwrap();

      out
    }
  }
}
