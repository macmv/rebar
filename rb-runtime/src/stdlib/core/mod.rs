use super::Environment;

impl Environment {
  pub fn core() -> Self {
    let mut env = Environment::empty();

    env.add_fn("assert_eq", |a: i64, b: i64| {
      if a != b {
        panic!("assertion failed: `(left == right)`\n  left: `{}`,\n right: `{}`", a, b);
      }
    });

    env.add_fn("assert", |v: bool| {
      if !v {
        panic!("assertion failed");
      }
    });

    env
  }
}
