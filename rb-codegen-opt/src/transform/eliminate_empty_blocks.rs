use std::collections::HashMap;

use rb_codegen::{BlockId, Phi, TerminatorInstruction, Variable};

use crate::analysis::{control_flow_graph::ControlFlowGraph, dominator_tree::DominatorTree};

use super::*;

#[derive(FromAnalysis)]
#[invalidates([ControlFlowGraph, DominatorTree])]
pub struct EliminateEmptyBlocks;

impl TransformPass<'_> for EliminateEmptyBlocks {
  fn run(&self, function: &mut Function) { eliminate_empty_blocks(function); }
}

fn eliminate_empty_blocks(function: &mut Function) {
  loop {
    let mut found = None;
    for block in function.blocks() {
      let b = function.block(block);
      if let TerminatorInstruction::Jump(redirect) = &b.terminator
        && b.instructions.is_empty()
      {
        if block != *redirect {
          found = Some((block, *redirect));
          break;
        }
      }
    }

    if let Some((to_remove, redirect)) = found {
      merge_phis(function, to_remove, redirect);

      let new_redirect =
        if redirect > to_remove { BlockId::new(redirect.as_u32() - 1) } else { redirect };

      let mut i = 0;
      function.blocks.retain_mut(|block| {
        if to_remove.as_u32() == i {
          i += 1;
          return false;
        }

        helper::redirect_jumps(block, to_remove, new_redirect);
        i += 1;
        true
      });
    } else {
      break;
    }
  }
}

fn merge_phis(function: &mut Function, from: BlockId, to: BlockId) {
  let (from, to) = function.two_blocks_mut(from, to);

  let mut new_phis = HashMap::<Variable, Phi>::new();
  for phi in from.phis.drain(..).chain(to.phis.drain(..)) {
    if let Some(existing) = new_phis.get_mut(&phi.to) {
      existing.from.extend(phi.from);
      existing.to = phi.to;
    } else {
      new_phis.insert(phi.to, phi);
    }
  }

  to.phis = new_phis.into_values().collect();
  to.phis.sort_by_key(|p| p.to.id());
}
