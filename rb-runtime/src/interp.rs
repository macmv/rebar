//! Dead simple interpreter implementation. Should only be used for testing.

use rb_syntax::SourceFile;

struct RuntimeEnv {
  variables: Vec<Value>,
}

enum Value {
  Int(i64),
  Float(f64),
  String(String),
  Bool(bool),
  Null,
  Array(Array),
  Table(Table),
  Function(FunctionImpl),
}

struct Array(Vec<Value>);
struct Table(Vec<(String, Value)>);
struct FunctionImpl;

impl RuntimeEnv {
  fn new() -> Self { Self { variables: vec![] } }
}

pub fn interpret(source: &SourceFile) {
  let mut env = RuntimeEnv::new();

  for stmt in source.stmts() {
    match stmt {
      _ => todo!(),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn interp(source: &str) { interpret(&SourceFile::parse(source).tree()); }

  #[test]
  fn foo() {
    interp(
      r#"
      print("Hello, world!")
      print("Goodbye, world!")
    "#,
    );
  }
}
