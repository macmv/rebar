use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

use rb_codegen::{BlockId, InstructionInput, InstructionOutput, Phi, Variable, VariableSize};

use crate::analysis::{
  control_flow_graph::ControlFlowGraph, dominator_tree::DominatorTree, value_uses::ValueUses,
};

use super::*;

#[derive(FromAnalysis)]
#[invalidates([ValueUses, ControlFlowGraph, DominatorTree])]
#[phase(Early)]
pub struct UpdatePhis<'a> {
  cfg:       &'a ControlFlowGraph,
  dominator: &'a DominatorTree,
}

struct Renamer<'a> {
  next_var: u32,
  stacks:   HashMap<Variable, Vec<Variable>>,

  update: &'a UpdatePhis<'a>,
}

impl<'a> TransformPass<'a> for UpdatePhis<'a> {
  fn run(&self, function: &mut Function) {
    let mut defs = BTreeMap::<Variable, HashSet<BlockId>>::new();
    let mut last_variable_by_block = HashMap::<BlockId, HashMap<VariableSize, Variable>>::new();

    for block in function.blocks() {
      let mut last_variable = HashMap::new();
      for instr in &function.block(block).instructions {
        for &output in &instr.output {
          if let InstructionOutput::Var(out) = output {
            defs.entry(out).or_default().insert(block);
            last_variable.insert(out.size(), out);
          }
        }
      }
      last_variable_by_block.insert(block, last_variable);
    }

    let phi_sites = defs.into_iter().map(|(kind, def_blocks)| {
      let mut phi_sites = BTreeSet::new();
      let mut work = VecDeque::from_iter(def_blocks.iter().copied());
      let mut in_work = HashSet::<BlockId>::from_iter(def_blocks.iter().copied());
      while let Some(b) = work.pop_front() {
        for x in self.dominance_frontier(b) {
          if phi_sites.insert(x) {
            if in_work.insert(x) {
              work.push_back(x);
            }
          }
        }
      }

      (kind, phi_sites)
    });

    for block in &mut function.blocks {
      block.phis.clear();
    }

    for (to, sites) in phi_sites {
      for block_id in sites {
        let block = function.block_mut(block_id);
        let mut phi = Phi { to, from: BTreeMap::new() };

        for &pred in self.cfg.enters(block_id) {
          phi.from.insert(pred, None);
        }

        if block_id == BlockId::ENTRY {
          phi.from.insert(BlockId::BEFORE, None);
        }

        block.phis.push(phi);
      }
    }

    let mut renamer = Renamer { next_var: 0, stacks: HashMap::new(), update: self };
    renamer.pass(function.entry(), function);
  }
}

impl UpdatePhis<'_> {
  fn dominance_frontier(&self, block: BlockId) -> BTreeSet<BlockId> {
    let mut frontier = BTreeSet::new();

    for child in self.dominator.all_dominating(block) {
      for &succ in self.cfg.exits(child) {
        if !self.dominator.is_strict_dominator(block, succ) {
          frontier.insert(succ);
        }
      }
    }

    frontier
  }
}

impl Renamer<'_> {
  fn pass(&mut self, block: BlockId, function: &mut Function) {
    let mut pushed = HashMap::new();

    for phi in &mut function.block_mut(block).phis {
      phi.to = self.fresh_var(phi.to.size());
      self.stacks.entry(phi.to).or_default().push(phi.to);
      pushed.entry(phi.to).and_modify(|e| *e += 1).or_insert(1);
    }

    for instr in &mut function.block_mut(block).instructions {
      for input in &mut instr.input {
        match input {
          InstructionInput::Var(var) => {
            *var = self
              .stacks
              .get(&var)
              .and_then(|s| s.last())
              .copied()
              .unwrap_or_else(|| panic!("no variable on stack for {:?}", var));
          }
          _ => {}
        }
      }

      for output in &mut instr.output {
        if let InstructionOutput::Var(out) = output {
          *out = self.fresh_var(out.size());
          self.stacks.entry(*out).or_default().push(*out);
          pushed.entry(*out).and_modify(|e| *e += 1).or_insert(1);
        }
      }
    }

    for &succ in self.update.cfg.exits(block) {
      for phi in &mut function.block_mut(succ).phis {
        if let Some(&top) = self.stacks.get(&phi.to).and_then(|s| s.last()) {
          phi.from.insert(block, Some(top));
        }
      }
    }

    for &child in self.update.dominator.direct_dominating(block) {
      self.pass(child, function);
    }

    for (kind, count) in pushed {
      let new_len = self.stacks[&kind].len() - count;
      self.stacks.get_mut(&kind).unwrap().truncate(new_len);
    }
  }

  fn fresh_var(&mut self, size: VariableSize) -> Variable {
    let var = self.next_var;
    self.next_var += 1;
    Variable::new(var, size)
  }
}

#[cfg(test)]
mod tests {
  use crate::tests::parse;

  #[test]
  fn recursive_deps() {
    let mut ast = parse(
      r#"
      block 0:
        mov A 0x04
        mov [0x80](v?) A
        mov [0xff] A
        jump to block 0
      "#,
    );

    ast.transform("update_phis");

    ast.check(expect![@r#"
      block 0:
        [0x80](v0) = phi(block 0 -> v3, block before -> v?)
        A(v1) = phi(block 0 -> v2, block before -> v?)
        mov A(v2) 0x04
        mov [0x80](v3) A(v2)
        mov [0x00ff] A(v2)
        jump to block 0
    "#]);
  }
}
