use super::Environment;

impl Environment {
  pub fn std() -> Self {
    let mut env = Environment::core();

    env.add_fn("println", |v: String| println!("{v}"));
    env.add_fn("replace", |src: String, a: String, b: String| src.replace(&a, &b));

    env
  }
}
