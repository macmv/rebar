use super::Environment;

impl Environment {
  pub fn core() -> Self {
    let mut env = Environment::empty();

    env.add_fn("assert_eq", |a: i64, b: i64| -> bool { a == b } as fn(i64, i64) -> bool);

    env
  }
}
