//! Formats a CST.
//!
//! TODO: Move to another crate.

use rb_syntax::{cst, AstNode, NodeOrToken, SyntaxKind, SyntaxNode, T};

pub struct Formatter {
  pub max_line_length: u32,
}

impl Default for Formatter {
  fn default() -> Self { Self { max_line_length: 80 } }
}

fn is_whitespace(kind: SyntaxKind) -> bool { matches!(kind, T![ws] | T![nl]) }

impl Formatter {
  fn fmt_leading_whitespace(&self, node: &SyntaxNode) -> String {
    // Iterate backwards until we find the first non-whitespace node.
    let mut curr = NodeOrToken::from(node.clone());
    let mut found_ws = false;
    while let Some(ws) = curr.prev_sibling_or_token() {
      if !is_whitespace(ws.kind()) {
        break;
      }
      curr = ws;
      found_ws = true;
    }
    if !found_ws {
      return "".into();
    }

    let is_start = curr.prev_sibling_or_token().is_none();

    // Iterate forward and format said whitespace.
    let mut out = String::new();
    loop {
      let s = match curr {
        NodeOrToken::Node(ref n) => n.text().to_string(),
        NodeOrToken::Token(ref n) => n.text().to_string(),
      };

      out += &s;

      if let Some(node) = curr.next_sibling_or_token() {
        curr = node;
        if !is_whitespace(curr.kind()) {
          break;
        }
      } else {
        break;
      }
    }

    let out = out.trim_end_matches(' ');
    let out = out.strip_suffix('\n').unwrap_or(out);

    // `res` is the resulting lines between the previous statement and `node`.
    let mut res: Vec<&str> = vec![];

    const EMPTY_LINE_THRESHOLD: usize = 2;

    let mut empty_lines = 0;

    let end: &[&str] = if out.ends_with('\n') { &[""] } else { &[] };

    for line in out.lines().chain(end.into_iter().copied()) {
      let line = line.trim();

      if line.is_empty() {
        empty_lines += 1;
      } else {
        empty_lines = 0;
      }

      if empty_lines >= EMPTY_LINE_THRESHOLD {
        continue;
      }

      res.push(line);
    }

    let mut out = String::new();

    // Add the newline from the previous statement.
    if !is_start {
      out += "\n";
    }

    for line in res {
      out += line;
      out += "\n";
    }
    out
  }

  pub fn fmt_stmt(&mut self, stmt: &cst::Stmt) -> String {
    let prefix = self.fmt_leading_whitespace(stmt.syntax());

    let s = match stmt {
      cst::Stmt::ExprStmt(expr) => self.fmt_expr(&expr.expr().unwrap()),
      _ => todo!("stmt {stmt:?}"),
    };

    format!("{prefix}{s}")
  }

  pub fn fmt_expr(&mut self, expr: &cst::Expr) -> String {
    match expr {
      cst::Expr::Literal(l) => l.syntax().text().to_string(),
      cst::Expr::Name(name) => name.syntax().text().to_string(),

      cst::Expr::BinaryExpr(expr) => {
        let lhs = self.fmt_expr(&expr.lhs().unwrap());
        let op = expr.binary_op().unwrap();
        let rhs = self.fmt_expr(&expr.rhs().unwrap());

        let out = format!("{lhs} {op} {rhs}",);

        // TODO: If `out` is longer than a line, split this into multiple lines.

        out
      }

      cst::Expr::CallExpr(call) => {
        let lhs = self.fmt_expr(&call.expr().unwrap());
        let args = call
          .arg_list()
          .unwrap()
          .exprs()
          .map(|arg| self.fmt_expr(&arg))
          .collect::<Vec<_>>()
          .join(", ");

        let out = format!("{lhs}({args})");

        if out.len() > self.max_line_length as usize {
          let args = call
            .arg_list()
            .unwrap()
            .exprs()
            .map(|arg| format!("  {}", self.fmt_expr(&arg)))
            .collect::<Vec<_>>()
            .join(",\n");
          format!("{lhs}(\n{args}\n)")
        } else {
          out
        }
      }

      _ => todo!("expr {expr:?}"),
    }
  }
}

pub fn format(cst: &cst::SourceFile) -> String {
  let mut out = String::new();
  let mut fmt = Formatter::default();

  for stmt in cst.stmts() {
    out += &fmt.fmt_stmt(&stmt);
  }
  out += "\n";

  out
}

// TODO: Hook up formatter options to the CLI.
#[allow(dead_code)]
pub fn format_opts(cst: &cst::SourceFile, mut fmt: Formatter) -> String {
  let mut out = String::new();

  for stmt in cst.stmts() {
    out += &fmt.fmt_stmt(&stmt);
  }
  out += "\n";

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

    expected.assert_eq(&format_opts(&cst.tree(), Formatter { max_line_length: 30 }));
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
          very_long_arg_2
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
}
