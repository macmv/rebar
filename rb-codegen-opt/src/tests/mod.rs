use std::fmt::{self, Formatter};

use rb_codegen::{Function, InstructionInput, InstructionOutput, Variable};
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

pub trait VariableDisplay {
  fn write_variable(&self, f: &mut Formatter, v: Variable) -> fmt::Result;
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

  pub fn check_annotated(&self, expected: Expect, annotation: &dyn VariableDisplay) {
    let annotated = AnnotatedFunction(&self.function, annotation).to_string();
    expected.assert_eq(&annotated);
  }
}

struct AnnotatedFunction<'a>(&'a Function, &'a dyn VariableDisplay);

impl fmt::Display for TestFunction {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.function.fmt(f) }
}

impl fmt::Display for AnnotatedFunction<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (i, block) in self.0.blocks.iter().enumerate() {
      writeln!(f, "block {}:", i)?;
      for phi in &block.phis {
        writeln!(f, "  {}", phi)?;
      }
      for instr in &block.instructions {
        write!(f, "  {}", instr.opcode)?;
        for (i, output) in instr.output.iter().enumerate() {
          if i != 0 {
            write!(f, ",")?;
          }
          let InstructionOutput::Var(v) = output;
          write!(f, " ")?;
          self.1.write_variable(f, *v)?;
        }
        write!(f, " =")?;
        for (i, input) in instr.input.iter().enumerate() {
          if i != 0 {
            write!(f, ",")?;
          }
          write!(f, " ")?;
          match input {
            InstructionInput::Var(v) => {
              self.1.write_variable(f, *v)?;
            }
            InstructionInput::Imm(i) => {
              write!(f, "{:#04x}", i.bits())?;
            }
          }
        }
        writeln!(f)?;
      }
      writeln!(f, "  {}", block.terminator)?;
    }
    Ok(())
  }
}
