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

#[cfg(test)]
mod tests {
  #[test]
  fn eliminate_unreachable_block() {
    crate::tests::check_transform(
      "eliminate_unreachable_blocks",
      expect![@r#"
          block 0:
            jump to block 1
          block 1:
            jump to block 1
        - block 2:
        -   jump to block 2
      "#],
    );
  }
}
