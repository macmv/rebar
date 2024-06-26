use super::Environment;

impl Environment {
  pub fn core() -> Self {
    let mut env = Environment::empty();

    env.add_fn("assert_eq", |a: i64, b: i64| -> i64 { (a == b) as i64 });

    env
  }
}
