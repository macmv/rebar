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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Congruence(u32);

struct CongruenceSet {
  var_to_congruence:  HashMap<Variable, Congruence>,
  congruence_to_vars: HashMap<Congruence, HashSet<Variable>>,
}

struct Renamer<'a> {
  next_var:   u32,
  stacks:     HashMap<Congruence, Vec<Variable>>,
  congruence: &'a CongruenceSet,

  update: &'a UpdatePhis<'a>,
}

impl<'a> TransformPass<'a> for UpdatePhis<'a> {
  fn run(&self, function: &mut Function) {
    let mut defs = BTreeMap::<Congruence, HashSet<BlockId>>::new();
    let mut last_variable_by_block = HashMap::<BlockId, HashMap<Congruence, Variable>>::new();

    let congruence = CongruenceSet::new(function);

    for block in function.blocks() {
      let mut last_variable = HashMap::new();
      for instr in &function.block(block).instructions {
        for &output in &instr.output {
          let InstructionOutput::Var(out) = output;
          defs.entry(congruence.lookup(out)).or_default().insert(block);
          last_variable.insert(congruence.lookup(out), out);
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
          if phi_sites.insert(x) && in_work.insert(x) {
            work.push_back(x);
          }
        }
      }

      (kind, phi_sites)
    });

    for block in &mut function.blocks {
      block.phis.clear();
    }

    for (c, sites) in phi_sites {
      for block_id in sites {
        let block = function.block_mut(block_id);
        let mut phi =
          Phi { to: *congruence.reverse_lookup(c).iter().next().unwrap(), from: BTreeMap::new() };

        for &pred in self.cfg.enters(block_id) {
          phi.from.insert(pred, None);
        }

        if block_id == BlockId::ENTRY {
          phi.from.insert(BlockId::BEFORE, None);
        }

        block.phis.push(phi);
      }
    }

    let mut renamer = Renamer {
      next_var:   0,
      stacks:     HashMap::new(),
      congruence: &congruence,
      update:     self,
    };

    for arg in function.args() {
      let cong = congruence.lookup(arg);
      renamer.stacks.entry(cong).or_default().push(arg);
      renamer.fresh_var(arg.size());
    }

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
      let cong = self.congruence.lookup(phi.to);
      phi.to = self.fresh_var(phi.to.size());
      self.stacks.entry(cong).or_default().push(phi.to);
      pushed.entry(cong).and_modify(|e| *e += 1).or_insert(1);
    }

    for instr in &mut function.block_mut(block).instructions {
      for input in &mut instr.input {
        if let InstructionInput::Var(var) = input {
          *var = self
            .stacks
            .get(&self.congruence.lookup(*var))
            .and_then(|s| s.last())
            .copied()
            .unwrap_or_else(|| panic!("no variable on stack for {:?}", var));
        }
      }

      for output in &mut instr.output {
        let InstructionOutput::Var(out) = output;
        let cong = self.congruence.lookup(*out);
        *out = self.fresh_var(out.size());
        self.stacks.entry(cong).or_default().push(*out);
        pushed.entry(cong).and_modify(|e| *e += 1).or_insert(1);
      }
    }

    if let rb_codegen::TerminatorInstruction::Return(inputs) =
      &mut function.block_mut(block).terminator
    {
      for input in inputs {
        if let InstructionInput::Var(var) = input {
          *var = self
            .stacks
            .get(&self.congruence.lookup(*var))
            .and_then(|s| s.last())
            .copied()
            .unwrap_or_else(|| panic!("no variable on stack for {:?}", var));
        }
      }
    }

    for &succ in self.update.cfg.exits(block) {
      for phi in &mut function.block_mut(succ).phis {
        let cong = self.congruence.lookup(phi.to);
        if let Some(&top) = self.stacks.get(&cong).and_then(|s| s.last()) {
          phi.from.insert(block, Some(top));
        }
      }
    }

    for &child in self.update.dominator.direct_dominating(block) {
      self.pass(child, function);
    }

    for (cong, count) in pushed {
      let new_len = self.stacks[&cong].len() - count;
      self.stacks.get_mut(&cong).unwrap().truncate(new_len);
    }
  }

  fn fresh_var(&mut self, size: VariableSize) -> Variable {
    let var = self.next_var;
    self.next_var += 1;
    Variable::new(var, size)
  }
}

impl CongruenceSet {
  pub fn new(function: &Function) -> Self {
    let mut congruence_to_vars = HashMap::<Congruence, HashSet<Variable>>::new();
    let mut var_to_congruence = HashMap::<Variable, Congruence>::new();

    for arg in function.args() {
      let c = Congruence(congruence_to_vars.len() as u32);
      congruence_to_vars.insert(c, HashSet::from([arg]));
      var_to_congruence.insert(arg, c);
    }

    for block in function.blocks() {
      for instr in &function.block(block).instructions {
        for &output in &instr.output {
          let InstructionOutput::Var(out) = output;
          let c = Congruence(congruence_to_vars.len() as u32);
          congruence_to_vars.insert(c, HashSet::from([out]));
          var_to_congruence.insert(out, c);
        }
      }
    }

    for block in function.blocks() {
      for phi in &function.block(block).phis {
        for from in phi.from.values().flatten() {
          match (var_to_congruence.get(&phi.to), var_to_congruence.get(from)) {
            // Not much to do if neither variable was defined. Maybe
            // merge it with a later variable, if that was defined?
            (None, None) => {}

            (c1, c2) if c1 == c2 => {} // Already congruent.

            (None, _) => {
              var_to_congruence.insert(phi.to, var_to_congruence[from]);
              congruence_to_vars.entry(var_to_congruence[from]).and_modify(|s| {
                s.insert(phi.to);
              });
            }

            (_, None) => {
              var_to_congruence.insert(*from, var_to_congruence[&phi.to]);
              congruence_to_vars.entry(var_to_congruence[&phi.to]).and_modify(|s| {
                s.insert(*from);
              });
            }

            (Some(&c1), Some(&c2)) => {
              for o in congruence_to_vars.remove(&c2).unwrap() {
                var_to_congruence.insert(o, c1);
                congruence_to_vars.entry(c1).and_modify(|s| {
                  s.insert(o);
                });
              }
              var_to_congruence.insert(*from, c1);
            }
          }
        }
      }
    }

    CongruenceSet { var_to_congruence, congruence_to_vars }
  }

  pub fn lookup(&self, var: Variable) -> Congruence { self.var_to_congruence[&var] }

  pub fn reverse_lookup(&self, cong: Congruence) -> &HashSet<Variable> {
    &self.congruence_to_vars[&cong]
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
        mov r0 = 0x04
        mov r1 = r0
        mov r2 = r0
        jump to block 0
      "#,
    );

    ast.transform("update_phis");

    ast.check(expect![@r#"
      block 0:
        r0 = phi(block 0 -> r3, block before -> <undef>)
        r1 = phi(block 0 -> r4, block before -> <undef>)
        r2 = phi(block 0 -> r5, block before -> <undef>)
        mov r3 = 0x04
        mov r4 = r3
        mov r5 = r3
        jump to block 0
    "#]);
  }
}
