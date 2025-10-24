use rb_codegen::Function;

use crate::analysis::Analysis;

pub mod analysis;
mod transform;

#[cfg(any(test, feature = "test"))]
mod tests;

#[cfg(feature = "test")]
pub use tests::*;

#[cfg(test)]
#[macro_use]
extern crate rb_test;

#[macro_use]
extern crate rb_codegen_opt_macros;

#[macro_use]
extern crate smallvec;

struct Transformer<'a> {
  analysis: &'a mut Analysis,
  function: &'a mut Function,
}

impl<'a> Transformer<'a> {
  pub fn new(analysis: &'a mut Analysis, function: &'a mut Function) -> Self {
    Self { analysis, function }
  }

  pub fn full_optimize(&mut self) {
    let mut passes = transform::TRANSFORM_PASSES.to_vec();
    passes.sort_by(|a, b| {
      a.phase().cmp(&b.phase()).then(
        a.invalidates()
          .len()
          .cmp(&b.invalidates().len())
          .then(a.requires().len().cmp(&b.requires().len())),
      )
    });
    for _ in 0..5 {
      for &pass in &passes {
        self.transform_pass(pass);
      }
    }
  }

  #[cfg(any(test, feature = "test"))]
  #[track_caller]
  pub fn single_pass(&mut self, name: &str) {
    let pass = transform::TRANSFORM_PASSES.iter().find(|p| p.name() == name).expect("no such pass");
    self.transform_pass(*pass);
  }

  fn transform_pass(&mut self, pass: &dyn transform::TransformPassImpl) {
    for &id in pass.requires() {
      self.analysis.load(id, self.function);
    }
    pass.run(&mut self.analysis, self.function);
    for &id in pass.invalidates() {
      self.analysis.invalidate(id);
    }
  }
}

pub fn optimize(function: &mut Function) {
  let mut analysis = Analysis::default();
  let mut transformer = Transformer::new(&mut analysis, function);
  // transformer.full_optimize();

  // TODO: Add a flag for this? Also make it test-only.
  /*
  analysis.load(analysis::control_flow_graph::ControlFlowGraph::ID, &function);
  analysis.get::<analysis::control_flow_graph::ControlFlowGraph>().show_graph();

  analysis.load(analysis::dominator_tree::DominatorTree::ID, &function);
  analysis.get::<analysis::dominator_tree::DominatorTree>().show_graph();

  analysis.load(analysis::control_flow_hints::ControlFlowHints::ID, &function);
  let hints = analysis.get::<analysis::control_flow_hints::ControlFlowHints>();
  for block in function.blocks() {
    println!("hints for {block}: {:?}", hints.hints[block]);
  }

  analysis.load(analysis::value_uses::ValueUses::ID, &function);
  let vu = analysis.get::<analysis::value_uses::ValueUses>();

  for (kind, versions) in &vu.variables_by_kind {
    println!("{kind:?}: {versions:#?}");
  }
  */
}
