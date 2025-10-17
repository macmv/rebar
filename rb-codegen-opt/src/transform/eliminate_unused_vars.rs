use std::collections::HashSet;

use rb_codegen::{Instruction, InstructionOutput, Variable};

use super::*;
use crate::analysis::value_uses::ValueUses;

#[derive(FromAnalysis)]
pub struct EliminateUnusedVars<'a> {
  value_uses: &'a ValueUses,
}

impl<'a> TransformPass<'a> for EliminateUnusedVars<'a> {
  fn run(&self, function: &mut Function) {
    for block in &mut function.blocks {
      block.instructions.retain(|instr| self.retain_instr(instr));
    }
  }
}

impl EliminateUnusedVars<'_> {
  fn retain_instr(&self, instr: &Instruction) -> bool {
    let [InstructionOutput::Var(var)] = instr.output.as_slice() else { return true };

    let mut seen = HashSet::new();
    self.is_used(*var, &mut seen)
  }

  fn is_used(&self, id: Variable, seen: &mut HashSet<Variable>) -> bool {
    if !seen.insert(id) {
      return false;
    }

    self
      .value_uses
      .variable_opt(id)
      .is_none_or(|v| v.required || v.used_by.iter().any(|&u| self.is_used(u, seen)))
  }
}

#[cfg(test)]
mod tests {
  use crate::tests::check_transform;

  #[test]
  fn eliminates_unused_vars() {
    check_transform(
      "eliminate_unused_vars",
      expect![@"
          block 0:
        -   mov r0 = 0x00
        -   mov r1 = r0
            trap
      "],
    );
  }
}
