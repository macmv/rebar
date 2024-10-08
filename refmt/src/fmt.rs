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
  fn ctx(&self) -> FormatterContext {
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
  fn indent(&mut self, kind: SyntaxKind) {
    match kind {
      T!['{'] | T!['('] => self.indent += 1,
      T!['}'] | T![')'] => self.indent -= 1,

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
      (T![nl], BLOCK) => {
        // The newlines in the middle of blocks matter, but the first and last don't.
        if self.before(token).kind() == T!['{'] || self.after(token).kind() == T!['}'] {
          (None, None)
        } else {
          (None, Newline)
        }
      }
      (T![nl], _) => (None, None),

      (T![')'], _) if self.multiline => (None, None),
      (T!['('], _) if self.multiline => (None, Newline),

      (T!['('] | T![')'] | IDENT, _) => (None, None),

      // The opening brace in if statements and defs needs some extra whitespace.
      (T!['{'], BLOCK)
        if matches!(token.parent().unwrap().parent().unwrap().kind(), IF_EXPR | DEF) =>
      {
        (Space, if self.multiline { Newline } else { Space })
      }

      (T!['{'] | T!['}'], INTERPOLATION) => (None, None),

      (T!['}'], _) if self.multiline => (Newline, None),
      (T!['{'], _) if self.multiline => (None, Newline),
      (T!['}'], _) => (Space, None),
      (T!['{'], _) => (None, Space),

      (T![let] | T![if] | T![def], _) => (None, Space),
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
      (T![=], _) => (Space, Space),

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

  fn fmt_syntax(&mut self, node: &SyntaxNode, parent_can_retry: bool) {
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
            CALL_EXPR | BINARY_EXPR | IF_EXPR => Some(self.clone()),
            _ => None,
          };

          // Any blocks with multiple expressions are always multiline.
          let always_multiline = match n.kind() {
            BLOCK if n.children().count() > 1 => true,
            _ => false,
          };

          let old_multiline = self.multiline;
          if self.multiline && retry.is_some() {
            self.multiline = false;
          }
          if always_multiline {
            self.multiline = true;
          }
          self.fmt_syntax(n, retry.is_some() || parent_can_retry);
          self.multiline = old_multiline;

          if let Some(retry) = retry {
            if self.over_line_limit() && !parent_can_retry {
              self.reset(retry);
              self.multiline = true;
              self.fmt_syntax(n, parent_can_retry);
              self.multiline = false;
            }
          }
        }
        NodeOrToken::Token(ref t) => {
          let (left, right) = self.spacing(t);
          self.indent(t.kind());

          let text = t.text().to_string();
          if text.trim().is_empty() && !text.contains('\n') {
            continue;
          }

          match (t.kind(), t.parent().unwrap().kind()) {
            // Add trailing commas on mutliline calls.
            (T![')'], ARG_LIST) if self.multiline => {
              if self.before(t).kind() != T![,] {
                self.out += ",\n";
              }
            }
            // Remove trailing commas on non-multiline calls.
            (T![,], ARG_LIST) if !self.multiline => {
              if self.after(t).kind() == T![')'] {
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

          if !text.trim().is_empty() {
            if self.out.ends_with('\n') {
              for _ in 0..self.indent * self.formatter.indent {
                self.out.push(' ');
              }
            }
          }

          self.out += &text.trim();

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
  let mut out = String::new();

  out += &fmt.fmt(&cst);

  while out.ends_with('\n') {
    out.pop();
  }
  out.push('\n');

  out
}

#[cfg(test)]
mod tests {
  use rb_test::{expect, Expect};

  use super::*;

  fn check(input: &str, expected: Expect) {
    let input = input.strip_prefix('\n').unwrap();

    let cst = cst::SourceFile::parse(input);
    for error in cst.errors() {
      panic!("{}", error.message());
    }

    expected.assert_eq(&format_opts(
      &cst.tree(),
      Formatter { max_line_length: 30, ..Default::default() },
    ));
  }

  #[test]
  fn it_works() {
    check(
      r#"
        print_impl  (  2   *   3+4+5)
      "#,
      expect![@r#"
        print_impl(2 * 3 + 4 + 5)
      "#],
    );
  }

  #[test]
  fn call_singleline() {
    check(
      r#"
        print_impl(2+3,   4*5)
      "#,
      expect![@r#"
        print_impl(2 + 3, 4 * 5)
      "#],
    );

    check(
      r#"
        print_impl(2,3,)
      "#,
      expect![@r#"
        print_impl(2, 3)
      "#],
    );

    check(
      r#"
        print_impl(
          2,
          3,
        )
      "#,
      expect![@r#"
        print_impl(2, 3)
      "#],
    );
  }

  #[test]
  fn call_multline() {
    check(
      r#"
        print_impl(very_long_arg_1, very_long_arg_2)
      "#,
      expect![@r#"
        print_impl(
          very_long_arg_1,
          very_long_arg_2,
        )
      "#],
    );
    check(
      r#"
        print_impl(
          very_long_arg_1,
          very_long_arg_2,
        )
      "#,
      expect![@r#"
        print_impl(
          very_long_arg_1,
          very_long_arg_2,
        )
      "#],
    );
  }

  #[test]
  fn keep_line_comment() {
    check(
      r#"
        // hello
        print(1, 2)
      "#,
      expect![@r#"
        // hello
        print(1, 2)
      "#],
    );
  }

  #[test]
  fn keep_trailing_comment() {
    check(
      r#"
        print(1, 2)
        // hello
      "#,
      expect![@r#"
        print(1, 2)
        // hello
      "#],
    );
  }

  #[test]
  fn keep_empty_line() {
    check(
      r#"
        print(1)
        print(2)
      "#,
      expect![@r#"
        print(1)
        print(2)
      "#],
    );

    check(
      r#"
        print(1)

        print(2)
      "#,
      expect![@r#"
        print(1)

        print(2)
      "#],
    );

    check(
      r#"
        print(1)


        print(2)
      "#,
      expect![@r#"
        print(1)

        print(2)
      "#],
    );

    check(
      r#"
        print(1)



        print(2)
      "#,
      expect![@r#"
        print(1)

        print(2)
      "#],
    );
  }

  #[test]
  fn keep_empty_lines_comments() {
    check(
      r#"
        // hello
        print(2)
      "#,
      expect![@r#"
        // hello
        print(2)
      "#],
    );

    check(
      r#"
        // hello

        print(2)
      "#,
      expect![@r#"
        // hello

        print(2)
      "#],
    );

    check(
      r#"
        // hello


        print(2)
      "#,
      expect![@r#"
        // hello

        print(2)
      "#],
    );

    check(
      r#"
        // hello



        print(2)
      "#,
      expect![@r#"
        // hello

        print(2)
      "#],
    );

    check(
      r#"
        print(1)


        // hello


        print(2)
      "#,
      expect![@r#"
        print(1)

        // hello

        print(2)
      "#],
    );
  }

  #[test]
  fn no_leading_whitespace() {
    check(
      &r#"
        // hi
        print(1)
      "#
      .lines()
      .map(|line| line.trim())
      .collect::<Vec<_>>()
      .join("\n"),
      expect![@r#"
        // hi
        print(1)
      "#],
    );

    check(
      &r#"
        assert_eq(2 + 3, 5)

        // precedence should work
        assert_eq(2 * 3 + 4, 10)
        assert_eq(4 + 2 * 3, 10)
      "#
      .lines()
      .map(|line| line.trim())
      .collect::<Vec<_>>()
      .join("\n"),
      expect![@r#"
        assert_eq(2 + 3, 5)

        // precedence should work
        assert_eq(2 * 3 + 4, 10)
        assert_eq(4 + 2 * 3, 10)
      "#],
    );
  }

  #[test]
  fn handle_trailing_newlines() {
    check(
      &r#"
        assert_eq(2 + 3, 5)

        // precedence should work
        assert_eq(2 * 3 + 4, 10)
        assert_eq(4 + 2 * 3, 10)

      "#
      .lines()
      .map(|line| line.trim())
      .collect::<Vec<_>>()
      .join("\n"),
      expect![@r#"
        assert_eq(2 + 3, 5)

        // precedence should work
        assert_eq(2 * 3 + 4, 10)
        assert_eq(4 + 2 * 3, 10)
      "#],
    );

    check(
      &r#"
        assert_eq(2 + 3, 5)

        // precedence should work
        assert_eq(2 * 3 + 4, 10)
        assert_eq(4 + 2 * 3, 10)

      "#,
      expect![@r#"
        assert_eq(2 + 3, 5)

        // precedence should work
        assert_eq(2 * 3 + 4, 10)
        assert_eq(4 + 2 * 3, 10)
      "#],
    );
  }

  #[test]
  fn let_stmt() {
    check(
      &r#"
        let   foo   =   3
      "#,
      expect![@r#"
        let foo = 3
      "#],
    );
  }

  #[test]
  fn if_stmt() {
    check(
      &r#"
        if  0  {
          println(2  +  3)
        }  else  {
          println(4  +  5)
        }
      "#,
      expect![@r#"
        if 0 {
          println(2 + 3)
        } else {
          println(4 + 5)
        }
      "#],
    );

    check(
      &r#"
        if  0  {
          println(2)
          println(3)
        }  else  {
          println(4)
          println(5)
        }
      "#,
      expect![@r#"
        if 0 {
          println(2)
          println(3)
        } else {
          println(4)
          println(5)
        }
      "#],
    );
  }

  #[test]
  fn long_binary_op() {
    check(
      &r#"
        fooooooooooooooooooooooooooooooooooo + baaaaaaaaaaaaaaaaaar
      "#,
      expect![@r#"
        fooooooooooooooooooooooooooooooooooo
          + baaaaaaaaaaaaaaaaaar
      "#],
    );

    check(
      &r#"
        1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10
      "#,
      expect![@r#"
        1 + 2 + 3 + 4 + 5 + 6 + 7 + 8
          + 9 + 10
      "#],
    );
  }

  #[test]
  fn def_stmt() {
    check(
      &r#"
        def  foo  (  x : int ,  y : str )  {
          x  +  y
        }
      "#,
      expect![@r#"
        def foo(x: int, y: str) { x
          + y }
      "#],
    );

    check(
      &r#"
        def foo(x:int,y:str){x+y}
      "#,
      expect![@r#"
        def foo(x: int, y: str) { x
          + y }
      "#],
    );
  }

  #[test]
  fn blocks() {
    check(
      r#"
        {
           let  x  =  2  +  3
           let  y  =  4
        }
      "#,
      expect![@r#"
        {
          let x = 2 + 3
          let y = 4
        }
      "#],
    );
  }

  #[test]
  fn strings() {
    check(
      r#"
        assert_eq (  "  h  "  ,  "  h  "  )
      "#,
      expect![@r#"
        assert_eq("  h  ", "  h  ")
      "#],
    );
  }

  #[test]
  fn interpolated_string() {
    check(
      r#"
        "hello #{  2  +  3  }"
      "#,
      expect![@r#"
        "hello #{2 + 3}"
      "#],
    );
  }

  #[test]
  fn arrays() {
    check(
      r#"
        [  ]
      "#,
      expect![@r#"
        []
      "#],
    );

    check(
      r#"
        [  1  ,  2  ,  3  ]
      "#,
      expect![@r#"
        [1, 2, 3]
      "#],
    );
  }
}
