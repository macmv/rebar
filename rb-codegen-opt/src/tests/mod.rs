use std::fmt;

use rb_codegen::Function;
use rb_test::Expect;

use crate::analysis::{Analysis, AnalysisPass};

mod diff;
mod parse_ir;

pub struct TestFunction {
  pub analysis: Analysis,
  pub function: Function,
}

pub fn parse(asm: &str) -> TestFunction {
  TestFunction { analysis: Analysis::default(), function: parse_ir::parse(asm) }
}

pub fn check_transform(pass: &str, diff: Expect) {
  let (before, _) = diff::parse(&diff.trimmed());
  let mut function = parse(&before);
  diff.assert_eq(&function.transform_diff(pass));
}

impl TestFunction {
  pub fn pass<T: AnalysisPass + 'static>(&mut self) -> &T {
    self.analysis.load(T::id(), &self.function);
    self.analysis.get::<T>()
  }

  #[allow(dead_code)]
  pub fn full_optimize(&mut self) {
    let mut transformer = crate::Transformer::new(&mut self.analysis, &mut self.function);
    transformer.full_optimize();
  }

  #[track_caller]
  pub fn transform(&mut self, name: &str) {
    let mut transformer = crate::Transformer::new(&mut self.analysis, &mut self.function);
    transformer.single_pass(name);
  }

  pub fn transform_diff(&mut self, name: &str) -> String {
    let before = self.function.to_string();
    let mut transformer = crate::Transformer::new(&mut self.analysis, &mut self.function);
    transformer.single_pass(name);
    let after = self.function.to_string();

    diff::diff(before, after)
  }

  pub fn check(&self, expected: Expect) { expected.assert_eq(&self.function.to_string()); }
}

impl fmt::Display for TestFunction {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.function.fmt(f) }
}
