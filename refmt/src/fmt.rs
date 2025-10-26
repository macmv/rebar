//! Formats a CST.
//!
//! TODO: Move to another crate.

use rb_syntax::{cst, AstNode, NodeOrToken, SyntaxKind, SyntaxKind::*, SyntaxNode, SyntaxToken, T};

pub struct Formatter {
  pub max_line_length: u32,

  /// Indent width in spaces.
  pub indent: u32,
}

impl Default for Formatter {
  fn default() -> Self { Self { max_line_length: 80, indent: 2 } }
}

fn is_whitespace(kind: SyntaxKind) -> bool { matches!(kind, T![ws] | T![nl]) }

#[derive(Clone)]
struct FormatterContext<'a> {
  formatter: &'a Formatter,

  // The current indent level. Multiply this by `formatter.indent` to get the actual indent.
  indent: u32,

  out: String,

  multiline: bool,
}

impl Formatter {
  fn ctx(&self) -> FormatterContext<'_> {
    FormatterContext { formatter: self, indent: 0, out: String::new(), multiline: false }
  }

  fn fmt(&self, cst: &cst::SourceFile) -> String {
    let mut ctx = self.ctx();
    ctx.fmt_syntax(cst.syntax(), false);
    ctx.out
  }
}

enum Spacing {
  None,
  Space,
  Newline,
}

impl FormatterContext<'_> {
  fn increase_indent(&mut self, kind: SyntaxKind) {
    match kind {
      T!['{'] | T!['['] | T!['('] => self.indent += 1,

      _ => {}
    }
  }

  fn decrease_indent(&mut self, kind: SyntaxKind) {
    match kind {
      T!['}'] | T![']'] | T![')'] => self.indent -= 1,

      _ => {}
    }
  }

  fn spacing(&self, token: &SyntaxToken) -> (Spacing, Spacing) {
    use Spacing::*;

    match (token.kind(), token.parent().unwrap().kind()) {
      (T![ws], _) => {
        let text = token.text().to_string();
        if text.trim().is_empty() {
          (None, None)
        } else if text.trim().starts_with("/*") {
          (Space, Space)
        } else if text.trim().starts_with("//") {
          (None, Newline)
        } else {
          panic!("unexpected whitespace: {:?}", text);
        }
      }

      // Newlines in some places are significant, elsewhere we just make our own newlines (for
      // example, blocks add newlines as part of the `{` token, so we want to remove user-defined
      // newlines there).
      (T![nl], SOURCE_FILE) => (None, Newline),
      (T![nl], STRUCT_BLOCK | BLOCK) => {
        // The newlines in the middle of blocks matter, but the first and last don't.
        if self.before(token).kind() == T!['{'] || self.after(token).kind() == T!['}'] {
          (None, None)
        } else {
          (None, Newline)
        }
      }
      (T![nl], _) => (None, None),
      (T![']'], ATTR) => (None, Newline),

      (T![')'], _) if self.multiline => {
        if self.before(token).kind() == T![,] {
          (None, None)
        } else {
          (Newline, None)
        }
      }
      (T!['('], _) if self.multiline => (None, Newline),

      (T!['('] | T![')'] | IDENT, _) => (None, None),

      // The opening brace in if statements and defs needs some extra whitespace.
      (T!['{'], BLOCK)
        if matches!(token.parent().unwrap().parent().unwrap().kind(), IF_EXPR | FUNCTION_DEF) =>
      {
        (Space, if self.multiline { Newline } else { Space })
      }
      (T!['{'], STRUCT_BLOCK) => (Space, if self.multiline { Newline } else { Space }),
      (T!['{'], STRUCT_EXPR) => (Space, if self.multiline { Newline } else { Space }),

      (T!['{'] | T!['}'], INTERPOLATION) => (None, None),

      (T![']'], _) if self.multiline => (Newline, None),
      (T!['['], _) if self.multiline => (None, Newline),
      (T![']'], _) => (None, None),
      (T!['['], _) => (None, None),

      (T!['}'], _) if self.multiline => (Newline, None),
      (T!['{'], _) if self.multiline => (None, Newline),
      (T!['}'], _) => (Space, None),
      (T!['{'], _) => (None, Space),

      (T![fn], _) => {
        // extern "syscall" fn...
        if self.before(token).kind() == STRING {
          (Space, Space)
        } else {
          (None, Space)
        }
      }
      (T![->], _) => (Space, Space),
      (T![let] | T![if] | T![fn] | T![extern] | T![struct], _) => (None, Space),
      (T![else], _) => (Space, None),

      (_, BINARY_OP) => {
        if self.multiline {
          (None, Space)
        } else {
          (Space, Space)
        }
      }

      (_, LITERAL) => (None, None),

      (T![,], _) if self.multiline => (None, Newline),
      (T![,] | T![:], _) => (None, Space),
      (T![=] | T![|], _) => (Space, Space),

      (_, _) => (None, None),
    }
  }

  fn before(&self, t: &SyntaxToken) -> NodeOrToken {
    let mut prev = NodeOrToken::from(t.clone());
    while let Some(p) = prev.prev_sibling_or_token() {
      prev = p;
      if !is_whitespace(prev.kind()) {
        break;
      }
    }
    prev
  }

  fn after(&self, t: &SyntaxToken) -> NodeOrToken {
    let mut next = NodeOrToken::from(t.clone());
    while let Some(n) = next.next_sibling_or_token() {
      next = n;
      if !is_whitespace(next.kind()) {
        break;
      }
    }
    next
  }

  fn fmt_syntax(&mut self, node: &SyntaxNode, parent_can_retry: bool) -> bool {
    let mut parent_needs_retry = false;

    for node in node.children_with_tokens() {
      match node {
        NodeOrToken::Node(ref n) => {
          match n.kind() {
            // Special case: leave the insides of strings alone, except for interpolations, which
            // we want to format.
            STRING => {
              let s = cst::String::cast(n.clone()).unwrap();

              let str = n.text().to_string();

              let start = n.text_range().start();
              let mut prev = 0;
              for interpolation in s.interpolations() {
                let range = interpolation.syntax().text_range();

                self.out += &str[prev..u32::from(range.start() - start) as usize];
                self.fmt_syntax(interpolation.syntax(), false);

                prev = u32::from(range.end() - start) as usize;
              }

              self.out += &str[prev..];

              continue;
            }
            _ => {}
          }

          let retry = match n.kind() {
            // Expressions that can toggle the multiline flag.
            BLOCK if n.parent().unwrap().kind() != IF_EXPR => Some(self.clone()),
            CALL_EXPR | BINARY_EXPR | IF_EXPR | ARRAY_EXPR | STRUCT_EXPR => Some(self.clone()),
            _ => None,
          };

          // Any blocks with multiple expressions are always multiline.
          let always_multiline = match n.kind() {
            STRUCT_BLOCK => true,
            BLOCK if n.children().count() > 1 => true,
            _ => false,
          };

          let old_multiline = self.multiline;
          if self.multiline && retry.is_some() {
            self.multiline = false;
          }
          if always_multiline {
            parent_needs_retry = true;
            self.multiline = true;
          }
          let needs_retry = self.fmt_syntax(n, retry.is_some() || parent_can_retry);
          self.multiline = old_multiline;

          if needs_retry {
            // If we cannot retry this node, propogate the `needs_retry` flag up to the
            // parent.
            parent_needs_retry = true;
          }

          if let Some(retry) = retry {
            if (self.over_line_limit() && !parent_can_retry) || needs_retry {
              self.reset(retry);
              self.multiline = true;
              self.fmt_syntax(n, parent_can_retry);

              if n.kind() == BINARY_EXPR {
                self.multiline = false
              }
            }
          }
        }
        NodeOrToken::Token(ref t) => {
          let (left, right) = self.spacing(t);

          let text = t.text().to_string();
          if text.trim().is_empty() && !text.contains('\n') {
            self.increase_indent(t.kind());
            self.decrease_indent(t.kind());
            continue;
          }

          match (t.kind(), t.parent().unwrap().kind()) {
            // Add trailing commas on mutliline calls.
            (T![')'], ARG_LIST) if self.multiline => {
              if self.before(t).kind() != T![,] {
                self.out += ",";
              }
            }
            (T![']'], ARRAY_EXPR) if self.multiline => {
              if self.before(t).kind() != T![,] {
                self.out += ",";
              }
            }
            // Remove trailing commas on non-multiline calls.
            (T![,], ARG_LIST) if !self.multiline => {
              if self.after(t).kind() == T![')'] {
                continue;
              }
            }
            (T![,], ARRAY_EXPR) if !self.multiline => {
              if self.after(t).kind() == T![']'] {
                continue;
              }
            }

            // Add indents to multiline binary ops.
            (_, BINARY_OP) if self.multiline => {
              self.out += "\n  ";
            }
            _ => {}
          }

          match left {
            Spacing::None => {}
            Spacing::Space => self.out += " ",
            Spacing::Newline => {
              // Don't insert too many blank lines.
              if !self.out.ends_with("\n\n") {
                self.out += "\n"
              }
            }
          }

          // Decrease indent before writing the actual indent, and increase indent after.
          // This makes blocks line up correctly.
          self.decrease_indent(t.kind());

          if !text.trim().is_empty() && self.out.ends_with('\n') {
            for _ in 0..self.indent * self.formatter.indent {
              self.out.push(' ');
            }
          }

          self.increase_indent(t.kind());

          self.out += text.trim();

          match right {
            Spacing::None => {}
            Spacing::Space => self.out += " ",
            Spacing::Newline => {
              // Don't insert too many blank lines.
              if !self.out.ends_with("\n\n") {
                self.out += "\n"
              }
            }
          }
        }
      }
    }

    parent_needs_retry
  }

  fn reset(&mut self, retry: FormatterContext) {
    self.out = retry.out;
    self.indent = retry.indent;
  }

  fn over_line_limit(&self) -> bool {
    let current_line_len = self.out.chars().rev().take_while(|&c| c != '\n').count() as u32;

    current_line_len > self.formatter.max_line_length
  }
}

pub fn format(cst: &cst::SourceFile) -> String { format_opts(cst, Formatter::default()) }

// TODO: Hook up formatter options to the CLI.
pub fn format_opts(cst: &cst::SourceFile, fmt: Formatter) -> String {
  let mut out = fmt.fmt(cst);

  while out.ends_with('\n') {
    out.pop();
  }
  out.push('\n');

  out
}
