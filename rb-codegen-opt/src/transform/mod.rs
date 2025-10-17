use rb_codegen::Function;

use crate::analysis::{Analysis, AnalysisPassId};

mod helper;

trait FromAnalysis<'a> {
  fn requires() -> &'static [AnalysisPassId];
  fn invalidates() -> &'static [AnalysisPassId];
  fn phase() -> Phase;

  fn from_analysis(analysis: &'a Analysis) -> Self;
}

trait TransformPass<'a>: FromAnalysis<'a> {
  fn run(&self, function: &mut Function);
}

pub trait TransformPassImpl {
  fn requires(&self) -> &[AnalysisPassId];
  fn invalidates(&self) -> &[AnalysisPassId];
  fn phase(&self) -> Phase;
  #[allow(dead_code)]
  fn name(&self) -> &'static str;

  fn run(&self, analysis: &Analysis, function: &mut Function);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Phase {
  Early,
  Normal,
  Late,
}

macro_rules! passes {
  (
    $($mod:ident::$name:ident),* $(,)?
  ) => {
    $(
      mod $mod;
    )*

    // Make an inner module so that the `TransformPassImpl` structs aren't visible,
    // which makes autocomplete within pass modules nicer.
    mod passes {
      use super::*;

      $(
        struct $name;

        impl TransformPassImpl for $name {
          fn requires(&self) -> &[AnalysisPassId] {
            <$mod::$name as FromAnalysis>::requires()
          }
          fn invalidates(&self) -> &[AnalysisPassId] {
            <$mod::$name as FromAnalysis>::invalidates()
          }
          fn phase(&self) -> Phase {
            <$mod::$name as FromAnalysis>::phase()
          }
          fn name(&self) -> &'static str {
            stringify!($mod)
          }
          fn run(&self, analysis: &Analysis, function: &mut Function) {
            <$mod::$name as FromAnalysis>::from_analysis(analysis).run(function)
          }
        }
      )*

      pub const TRANSFORM_PASSES: &[&dyn TransformPassImpl] = &[ $(&$name),* ];
    }

    pub use passes::TRANSFORM_PASSES;
  }
}

passes![
  constant_fold::ConstantFold,
  // eliminate_empty_blocks::EliminateEmptyBlocks,
  // eliminate_nop_assign::EliminateNopAssign,
  // eliminate_nop_math::EliminateNopMath,
  eliminate_unreachable_blocks::EliminateUnreachableBlocks,
  eliminate_unused_vars::EliminateUnusedVars,
  // legalize::Legalize,
  // merge_blocks::MergeBlocks,
  // update_phis::UpdatePhis,
];
