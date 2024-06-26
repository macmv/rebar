use super::Environment;

impl Environment {
  pub fn std() -> Self {
    let mut env = Environment::core();

    env.add_fn("println", |v: i64| println!("{v}"));

    env
  }
}
