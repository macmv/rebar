use line_index::LineCol;
use rb_syntax::{TextRange, TextSize};
use std::fmt::{self, Display, Write};

use crate::{Sources, sources::SourceId};

pub struct DiagnosticRender<'a> {
  sources:    &'a Sources,
  diagnostic: &'a Diagnostic,
  color:      bool,
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

  pub fn render<'a>(&'a self, sources: &'a Sources) -> DiagnosticRender<'a> {
    DiagnosticRender::new(sources, self)
  }
  pub fn render_with_color<'a>(&'a self, sources: &'a Sources) -> DiagnosticRender<'a> {
    DiagnosticRender::new(sources, self).with_color()
  }
}

impl<'a> DiagnosticRender<'a> {
  pub fn new(sources: &'a Sources, diagnostic: &'a Diagnostic) -> Self {
    DiagnosticRender { sources, diagnostic, color: false }
  }

  pub fn with_color(mut self) -> Self {
    self.color = true;
    self
  }
}

impl fmt::Display for DiagnosticRender<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let source = &self.sources[self.diagnostic.span.file];

    let mut lines = source.line_index.lines(self.diagnostic.span.range);
    let _ = lines.next();
    if lines.next().is_some() {
      let start = source.line_index.line_col(self.diagnostic.span.range.start());
      let start_line_num = start.line + 1;
      let start_col_num = start.col + 1;

      let end = source.line_index.line_col(self.diagnostic.span.range.end());
      let end_line_num = end.line + 1;
      let _end_col_num = end.col + 1;

      let start =
        u32::from(source.line_index.offset(LineCol { line: start.line, col: 0 }).unwrap()) as usize;
      let end = source
        .line_index
        .offset(LineCol { line: end.line + 1, col: 0 })
        .map(|o| u32::from(o) as usize)
        .unwrap_or(source.source.len());

      let margin_str = spaces(end_line_num.ilog10() as usize + 1);

      writeln!(f, "{}: {}", self.red(self.bold("error")), self.bold(&self.diagnostic.message))?;
      writeln!(
        f,
        "{}{} {}:{}:{}",
        margin_str,
        self.blue("-->"),
        source.name,
        start_line_num,
        start_col_num
      )?;
      writeln!(f, "{} {}", margin_str, self.blue("|"))?;

      for (i, line) in source.source[start..end].lines().enumerate() {
        let line_num = start_line_num + i as u32;
        let line_str = line.trim_end();

        let line_num_len = line_num.ilog10() as usize + 1;
        writeln!(
          f,
          "{}{} {} {}",
          spaces(margin_str.len - line_num_len),
          self.blue(self.bold(line_num)),
          self.blue("|"),
          line_str
        )?;
      }

      writeln!(f, "{} {}", margin_str, self.blue("|"))?;

      Ok(())
    } else {
      let pos = source.line_index.line_col(self.diagnostic.span.range.start());
      let line_num = pos.line + 1;
      let col_num = pos.col + 1;

      let start_col = pos.col as usize;
      let mut end_col = source.line_index.line_col(self.diagnostic.span.range.end()).col as usize;
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
      let margin_str = spaces(line_num.ilog10() as usize + 1);

      let bar = self.blue("|");

      writeln!(
        f,
        "{error}: {message}",
        error = self.red(self.bold("error")),
        message = self.bold(&self.diagnostic.message)
      )?;
      writeln!(
        f,
        "{margin_str}{arrow} {source}:{line_num}:{col_num}",
        arrow = self.blue("-->"),
        source = source.name,
      )?;
      writeln!(f, "{margin_str} {bar}")?;
      writeln!(f, "{line_num} {bar} {line_str}", line_num = self.blue(self.bold(line_num)))?;
      writeln!(
        f,
        "{margin_str} {bar} {spaces}{underline}",
        spaces = spaces(start_col),
        underline = self.red(self.bold(carrots(end_col - start_col)))
      )?;

      Ok(())
    }
  }
}

struct Repeated {
  len: usize,
  c:   char,
}

fn spaces(len: usize) -> Repeated { Repeated { len, c: ' ' } }
fn carrots(len: usize) -> Repeated { Repeated { len, c: '^' } }

impl Display for Repeated {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for _ in 0..self.len {
      f.write_char(self.c)?;
    }
    Ok(())
  }
}

struct Color<'a, D: Display> {
  render:  &'a DiagnosticRender<'a>,
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

impl DiagnosticRender<'_> {
  fn color<D: Display>(&self, s: D, color: &'static str) -> Color<'_, D> {
    Color { render: self, display: s, color }
  }

  fn red(&self, s: impl Display) -> impl Display { self.color(s, RED) }
  fn bold(&self, s: impl Display) -> impl Display { self.color(s, BOLD) }
  fn blue(&self, s: impl Display) -> impl Display { self.color(s, BLUE) }
}
