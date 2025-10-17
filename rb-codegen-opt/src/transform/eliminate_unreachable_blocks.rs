use crate::analysis::{control_flow_graph::ControlFlowGraph, dominator_tree::DominatorTree};

use super::*;

#[derive(FromAnalysis)]
#[invalidates([ControlFlowGraph, DominatorTree])]
pub struct EliminateUnreachableBlocks<'a> {
  dom: &'a DominatorTree,
}

impl<'a> TransformPass<'a> for EliminateUnreachableBlocks<'a> {
  fn run(&self, function: &mut Function) {
    function.retain_blocks(|b| b.as_u32() == 0 || self.dom.immediate_dominator(b).is_some());
  }
}
