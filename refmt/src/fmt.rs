//! Formats a CST.
//!
//! TODO: Move to another crate.

use rb_syntax::{cst, AstNode};

pub struct Formatter {}

impl Formatter {
  pub fn fmt_stmt(&mut self, stmt: &cst::Stmt) -> String {
    match stmt {
      cst::Stmt::ExprStmt(expr) => self.fmt_expr(&expr.expr().unwrap()),
      _ => todo!("stmt {stmt:?}"),
    }
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

        format!("{lhs}({args})",)
      }

      _ => todo!("expr {expr:?}"),
    }
  }
}

pub fn format(cst: &cst::SourceFile) -> String {
  let mut out = String::new();
  let mut fmt = Formatter {};

  for stmt in cst.stmts() {
    out += &fmt.fmt_stmt(&stmt);
    out += "\n";
  }

  out
}

#[cfg(test)]
mod tests {
  use rb_test::{expect, Expect};

  use super::*;

  fn check(input: &str, expected: Expect) {
    let cst = cst::SourceFile::parse(&input);
    for error in cst.errors() {
      panic!("{}", error.message());
    }

    expected.assert_eq(&format(&cst.tree()));
  }

  #[test]
  fn it_works() {
    check(
      r#"print_impl  (  2   *   3+4+5)
      "#,
      expect![@r#"
        print_impl(2 * 3 + 4 + 5)
      "#],
    );
  }
}
