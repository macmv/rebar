//! Dead simple interpreter implementation. Should only be used for testing.

use rb_syntax::{BinaryOp, SourceFile};

pub struct RuntimeEnv {
  variables: Vec<Value>,
}

pub enum Value {
  Int(i64),
  Float(f64),
  String(String),
  Bool(bool),
  Null,
  Array(Array),
  Table(Table),
  Function(FunctionImpl),
}

pub struct Array(Vec<Value>);
pub struct Table(Vec<(String, Value)>);
pub struct FunctionImpl;

impl RuntimeEnv {
  fn new() -> Self { Self { variables: vec![] } }
}

pub fn interpret(source: &SourceFile) -> (RuntimeEnv, Option<Error>) {
  let mut env = RuntimeEnv::new();

  let mut error = None;
  dbg!(&source);
  for stmt in source.stmts() {
    if let Err(e) = env.interpret_stmt(&stmt) {
      error = Some(e);
      break;
    }
  }

  (env, error)
}

#[derive(Debug)]
pub enum Error {
  MissingExpr,
}

impl RuntimeEnv {
  fn interpret_stmt(&mut self, stmt: &rb_syntax::Stmt) -> Result<(), Error> {
    match stmt {
      rb_syntax::Stmt::ExprStmt(expr) => {
        self.interpret_expr(&expr.expr().ok_or(Error::MissingExpr)?)?;
      }
      _ => unimplemented!(),
    }

    Ok(())
  }

  fn interpret_expr(&mut self, expr: &rb_syntax::Expr) -> Result<Value, Error> {
    Ok(match expr {
      rb_syntax::Expr::BinaryExpr(bin) => {
        let lhs = bin.lhs().ok_or(Error::MissingExpr)?;
        let rhs = bin.rhs().ok_or(Error::MissingExpr)?;
        let op = bin.binary_op().ok_or(Error::MissingExpr)?;

        let lhs = self.interpret_expr(&lhs)?;
        let rhs = self.interpret_expr(&rhs)?;

        if op.plus_token().is_some() {
          match (lhs, rhs) {
            (Value::Int(lhs), Value::Int(rhs)) => Value::Int(lhs + rhs),
            (Value::Float(lhs), Value::Float(rhs)) => Value::Float(lhs + rhs),
            _ => unimplemented!(),
          }
        } else {
          unimplemented!()
        }
      }
      _ => unimplemented!(),
    })
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn interp(source: &str) {
    let (_env, res) = interpret(&SourceFile::parse(source).tree());
    if let Some(e) = res {
      panic!("Error: {:?}", e);
    }
  }

  #[test]
  fn foo() {
    interp(
      r#"1 + 2
        print("Hello, world!")
        print("Goodbye, world!")
      "#,
    );

    panic!();
  }
}
