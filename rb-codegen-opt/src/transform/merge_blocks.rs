use std::collections::HashSet;

use rb_codegen::TerminatorInstruction;

use super::*;
use crate::analysis::control_flow_graph::ControlFlowGraph;

#[derive(FromAnalysis)]
pub struct MergeBlocks<'a> {
  cfg: &'a ControlFlowGraph,
}

impl<'a> TransformPass<'a> for MergeBlocks<'a> {
  fn run(&self, function: &mut Function) {
    let mut to_remove = HashSet::new();
    for block in function.blocks() {
      if let &[pred] = self.cfg.enters(block)
        && block != pred
        && !to_remove.contains(&pred)
      {
        let (first, second) = function.two_blocks_mut(pred, block);

        assert!(
          second.phis.is_empty(),
          "{block} has only one predecessor, so it should not have any phis"
        );

        // TODO: Because `block` has a single entry point, it should be possible to
        // invert a condition to force the jump to be at the end. But, right now we
        // don't do that, and only merge blocks that directly jump between each
        // other.
        match first.terminator {
          TerminatorInstruction::Jump(target) if target == block => {}
          _ => return,
        }

        first.terminator = second.terminator.clone();
        first.instructions.append(&mut second.instructions);

        to_remove.insert(block);
      }
    }

    function.retain_blocks(|b, _| !to_remove.contains(&b));
  }
}
