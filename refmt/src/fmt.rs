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
    let mut out = String::new();
    let mut found_ws = false;
    for child in node.children_with_tokens() {
      if !is_whitespace(child.kind()) {
        break;
      }
      found_ws = true;

      let s = match child {
        NodeOrToken::Node(ref n) => n.text().to_string(),
        NodeOrToken::Token(ref n) => n.text().to_string(),
      };

      out += &s;
    }

    if !found_ws {
      return "".into();
    }

    // Act line there's a newline before the file.
    self.fmt_whitespace(format!("\n{out}")).trim_start().to_string()
  }

  fn fmt_trailing_whitespace(&self, node: &SyntaxNode) -> String {
    let mut out = String::new();
    let mut curr = NodeOrToken::from(node.clone());
    let mut found_ws = false;
    while let Some(ws) = curr.next_sibling_or_token() {
      found_ws = true;
      if !is_whitespace(ws.kind()) {
        break;
      }

      let s = match ws {
        NodeOrToken::Node(ref n) => n.text().to_string(),
        NodeOrToken::Token(ref n) => n.text().to_string(),
      };

      out += &s;
      curr = ws;
    }

    if !found_ws {
      return "".into();
    }

    self.fmt_whitespace(out)
  }

  fn fmt_whitespace(&self, whitespace: String) -> String {
    let out = whitespace.trim_start_matches(' ').trim_end_matches(' ');
    // let out = out.strip_suffix('\n').unwrap_or(out);

    // `res` is the resulting lines between the previous statement and `node`.
    let mut res: Vec<&str> = vec![];

    const EMPTY_LINE_THRESHOLD: usize = 2;

    let mut empty_lines = 0;

    // Note that .lines() trims the last line (but only sometimes), and .split('\n')
    // does not.
    //
    // We want to skip the first and last lines, so we use `iter.next()` in this
    // somewhat odd way.
    let mut iter = out.split('\n');
    iter.next(); // Skip the first line.
    let mut curr = iter.next();

    while let Some(line) = curr {
      curr = iter.next();
      if curr.is_none() {
        // Skip the last line.
        break;
      };

      let line = line.trim();

      if line.is_empty() {
        empty_lines += 1;
      } else {
        empty_lines = 0;
      }

      if empty_lines < EMPTY_LINE_THRESHOLD {
        res.push(line);
      }
    }

    let mut out = String::new();

    out += "\n";
    for line in res {
      out += line;
      out += "\n";
    }

    out
  }

  pub fn fmt_stmt(&mut self, stmt: &cst::Stmt) -> String {
    let s = match stmt {
      cst::Stmt::ExprStmt(expr) => self.fmt_expr(&expr.expr().unwrap()),
      cst::Stmt::Let(let_stmt) => {
        let name = let_stmt.ident_token().unwrap().text().to_string();
        let expr = self.fmt_expr(&let_stmt.expr().unwrap());

        format!("let {name} = {expr}",)
      }
      _ => todo!("stmt {stmt:?}"),
    };

    let suffix = self.fmt_trailing_whitespace(stmt.syntax());

    format!("{s}{suffix}")
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

pub fn format(cst: &cst::SourceFile) -> String { format_opts(cst, Formatter::default()) }

// TODO: Hook up formatter options to the CLI.
pub fn format_opts(cst: &cst::SourceFile, mut fmt: Formatter) -> String {
  let mut out = String::new();

  out += &fmt.fmt_leading_whitespace(cst.syntax());
  for stmt in cst.stmts() {
    out += &fmt.fmt_stmt(&stmt);
  }

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
    check(
      r#"
        print_impl(
          very_long_arg_1,
          very_long_arg_2
        )
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
}
