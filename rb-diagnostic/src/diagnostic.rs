use line_index::LineCol;
use rb_syntax::{TextRange, TextSize};
use std::fmt::{Display, Write};

use crate::{Sources, sources::SourceId};

pub struct Diagnostic {
  pub message: String,
  pub span:    Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
  pub file:  SourceId,
  pub range: TextRange,
}

impl Span {
  pub fn at_offset(&self, offset: u32, len: u32) -> Self {
    let offset = self.range.start() + TextSize::new(offset);
    Span { file: self.file, range: TextRange::at(offset, TextSize::new(len)) }
  }
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

      let line_str = &source.source[start..end].trim_end();

      let margin_str = " ".repeat(line_num.ilog10() as usize + 1);
      let underline_str = format!("{}{}", " ".repeat(start_col), "^".repeat(end_col - start_col));

      let mut out = String::new();

      writeln!(out, "{}: {}", red(bold("error")), bold(&self.message)).unwrap();
      writeln!(out, "{}{} {}:{}:{}", margin_str, blue("-->"), source.name, line_num, col_num)
        .unwrap();
      writeln!(out, "{} {}", margin_str, blue("|")).unwrap();
      writeln!(out, "{} {} {}", blue(bold(line_num)), blue("|"), line_str).unwrap();
      writeln!(out, "{} {} {}", margin_str, blue("|"), underline_str).unwrap();

      out
    }
  }
}

const RESET: &str = "\x1b[0m";
const BOLD: &str = "\x1b[1m";
const RED: &str = "\x1b[31m";
const BLUE: &str = "\x1b[34m";

struct Color<D: Display>(D, &'static str);
impl<D: Display> Display for Color<D> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.1)?;
    write!(f, "{}", self.0)?;
    write!(f, "{}", RESET)?;
    Ok(())
  }
}

fn red(s: impl Display) -> impl Display { Color(s, RED) }
fn bold(s: impl Display) -> impl Display { Color(s, BOLD) }
fn blue(s: impl Display) -> impl Display { Color(s, BLUE) }
