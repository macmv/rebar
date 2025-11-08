use line_index::LineCol;
use rb_syntax::{TextRange, TextSize};
use std::fmt::{Display, Write};

use crate::{Sources, sources::SourceId};

pub struct Render<'a> {
  sources: &'a Sources,
  color:   bool,
}

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
  /// Only for tests.
  pub fn blank() -> Self {
    Span { file: SourceId::from_raw(0.into()), range: TextRange::empty(TextSize::from(0u32)) }
  }

  pub fn at_offset(&self, offset: u32, len: u32) -> Self {
    let offset = self.range.start() + TextSize::new(offset);
    Span { file: self.file, range: TextRange::at(offset, TextSize::new(len)) }
  }
}

impl Diagnostic {
  pub fn error(message: impl Into<String>, span: Span) -> Self {
    Diagnostic { message: message.into(), span }
  }

  pub fn render(&self, sources: &Sources) -> String { Render::new(sources).render(self) }
  pub fn render_with_color(&self, sources: &Sources) -> String {
    Render::new(sources).with_color().render(self)
  }
}

impl<'a> Render<'a> {
  pub fn new(sources: &'a Sources) -> Self { Render { sources, color: false } }

  pub fn with_color(mut self) -> Self {
    self.color = true;
    self
  }

  pub fn render(&self, diagnostic: &Diagnostic) -> String {
    let source = &self.sources[diagnostic.span.file];

    let mut lines = source.line_index.lines(diagnostic.span.range);
    let _ = lines.next();
    if lines.next().is_some() {
      let start = source.line_index.line_col(diagnostic.span.range.start());
      let start_line_num = start.line + 1;
      let start_col_num = start.col + 1;

      let end = source.line_index.line_col(diagnostic.span.range.end());
      let end_line_num = end.line + 1;
      let _end_col_num = end.col + 1;

      let start =
        u32::from(source.line_index.offset(LineCol { line: start.line, col: 0 }).unwrap()) as usize;
      let end = source
        .line_index
        .offset(LineCol { line: end.line + 1, col: 0 })
        .map(|o| u32::from(o) as usize)
        .unwrap_or(source.source.len());

      let margin_str = " ".repeat(end_line_num.ilog10() as usize + 1);

      let mut out = String::new();

      writeln!(out, "{}: {}", self.red(self.bold("error")), self.bold(&diagnostic.message))
        .unwrap();
      writeln!(
        out,
        "{}{} {}:{}:{}",
        margin_str,
        self.blue("-->"),
        source.name,
        start_line_num,
        start_col_num
      )
      .unwrap();
      writeln!(out, "{} {}", margin_str, self.blue("|")).unwrap();

      for (i, line) in source.source[start..end].lines().enumerate() {
        let line_num = start_line_num + i as u32;
        let line_str = line.trim_end();

        let line_num_len = line_num.ilog10() as usize + 1;
        writeln!(
          out,
          "{}{} {} {}",
          " ".repeat(margin_str.len() - line_num_len),
          self.blue(self.bold(line_num)),
          self.blue("|"),
          line_str
        )
        .unwrap();
      }

      writeln!(out, "{} {}", margin_str, self.blue("|")).unwrap();

      out
    } else {
      let pos = source.line_index.line_col(diagnostic.span.range.start());
      let line_num = pos.line + 1;
      let col_num = pos.col + 1;

      let start_col = pos.col as usize;
      let mut end_col = source.line_index.line_col(diagnostic.span.range.end()).col as usize;
      if start_col == end_col {
        end_col += 1;
      }

      let start =
        u32::from(source.line_index.offset(LineCol { line: pos.line, col: 0 }).unwrap()) as usize;
      let end = source
        .line_index
        .offset(LineCol { line: pos.line + 1, col: 0 })
        .map(|o| u32::from(o) as usize)
        .unwrap_or(source.source.len());

      let line_str = &source.source[start..end].trim_end();

      let margin_str = " ".repeat(line_num.ilog10() as usize + 1);
      let underline_str = format!("{}{}", " ".repeat(start_col), "^".repeat(end_col - start_col));

      let mut out = String::new();

      writeln!(out, "{}: {}", self.red(self.bold("error")), self.bold(&diagnostic.message))
        .unwrap();
      writeln!(out, "{}{} {}:{}:{}", margin_str, self.blue("-->"), source.name, line_num, col_num)
        .unwrap();
      writeln!(out, "{} {}", margin_str, self.blue("|")).unwrap();
      writeln!(out, "{} {} {}", self.blue(self.bold(line_num)), self.blue("|"), line_str).unwrap();
      writeln!(out, "{} {} {}", margin_str, self.blue("|"), underline_str).unwrap();

      out
    }
  }
}

struct Color<'a, D: Display> {
  render:  &'a Render<'a>,
  display: D,
  color:   &'static str,
}

impl<D: Display> Display for Color<'_, D> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if self.render.color {
      write!(f, "{}", self.color)?;
    }
    write!(f, "{}", self.display)?;
    if self.render.color {
      write!(f, "{}", RESET)?;
    }
    Ok(())
  }
}

const RESET: &str = "\x1b[0m";
const BOLD: &str = "\x1b[1m";
const RED: &str = "\x1b[31m";
const BLUE: &str = "\x1b[34m";

impl Render<'_> {
  fn color<D: Display>(&self, s: D, color: &'static str) -> Color<'_, D> {
    Color { render: self, display: s, color }
  }

  fn red(&self, s: impl Display) -> impl Display { self.color(s, RED) }
  fn bold(&self, s: impl Display) -> impl Display { self.color(s, BOLD) }
  fn blue(&self, s: impl Display) -> impl Display { self.color(s, BLUE) }
}
