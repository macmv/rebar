//! Dead simple interpreter implementation. Should only be used for testing.

use core::fmt;
use std::sync::Arc;

use rb_syntax::{BinaryOp, SourceFile};

pub struct RuntimeEnv {
  variables: Vec<(String, Value)>,
}

#[derive(Debug, Clone)]
pub enum Value {
  Int(i64),
  Float(f64),
  String(String),
  Bool(bool),
  Null,
  Array(Array),
  Table(Table),
  Function(Arc<FunctionImpl>),
}

#[derive(Debug, Clone)]
pub struct Array(Arc<Vec<Value>>);
#[derive(Debug, Clone)]
pub struct Table(Arc<Vec<(String, Value)>>);

pub struct FunctionImpl {
  name: String,
}

impl RuntimeEnv {
  fn new() -> Self { Self { variables: vec![] } }
}

impl fmt::Debug for FunctionImpl {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "FunctionImpl({})", self.name)
  }
}

impl FunctionImpl {
  pub fn call(&self, args: Vec<Value>) -> Value {
    println!("calling {} with args {:?}", self.name, args);

    Value::Null
  }
}

pub fn interpret(source: &SourceFile) -> (RuntimeEnv, Option<Error>) {
  let mut env = RuntimeEnv::new();

  let mut error = None;
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
      rb_syntax::Expr::Literal(lit) => {
        if let Some(lit) = lit.integer_token() {
          Value::Int(lit.text().parse().unwrap())
        } else {
          unimplemented!()
        }
      }
      rb_syntax::Expr::String(str) => Value::String(str.syntax.text().to_string()),
      rb_syntax::Expr::Name(name) => {
        let ident = name.ident_token().unwrap();
        let name = ident.text();

        self
          .variables
          .iter()
          .find(|(n, _)| n == &name)
          .map(|(_, v)| v.clone())
          .unwrap_or_else(|| Value::Function(Arc::new(FunctionImpl { name: name.to_string() })))
      }
      rb_syntax::Expr::CallExpr(bin) => {
        let lhs = bin.expr().ok_or(Error::MissingExpr)?;
        let args = bin.arg_list().ok_or(Error::MissingExpr)?;

        let lhs = self.interpret_expr(&lhs)?;

        let mut values = vec![];
        for arg in args.exprs() {
          values.push(self.interpret_expr(&arg)?);
        }

        match lhs {
          Value::Function(f) => f.call(values),
          _ => unimplemented!("cannot call {lhs:?}"),
        }
      }
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
      _ => unimplemented!("expr: {expr:?}"),
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
