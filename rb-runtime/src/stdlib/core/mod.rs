use super::Environment;

impl Environment {
  pub fn core() -> Self {
    let mut env = Environment::empty();

    env.add_fn("assert_eq", |a: i64, b: i64| {
      println!("assert_eq({}, {})", a, b);
      if a != b {
        panic!("assertion failed: `(left == right)`\n  left: `{}`,\n right: `{}`", a, b);
      }
    });

    env
  }
}
