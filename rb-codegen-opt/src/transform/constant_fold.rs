use rb_codegen::Instruction;

use super::*;
use crate::analysis::{
  control_flow_graph::ControlFlowGraph,
  dominator_tree::DominatorTree,
  value_uses::{ValueUses, VariableValue},
};

#[derive(FromAnalysis)]
#[invalidates([ControlFlowGraph, DominatorTree])]
pub struct ConstantFold<'a> {
  value_uses: &'a ValueUses,
}

impl<'a> TransformPass<'a> for ConstantFold<'a> {
  fn run(&self, function: &mut Function) {
    for block in &mut function.blocks {
      let mut delete = false;
      block.instructions.retain_mut(|instr| {
        if delete {
          return false;
        }

        match self.pass_instr(instr) {
          InstrChange::None => true,
          InstrChange::Remove => false,
          InstrChange::DeleteAfter => {
            delete = true;
            true
          }
        }
      });
    }
  }
}

// TODO: `pass_instr` should find conditional branches that are always taken,
// and remove all instructions after those.
#[allow(unused)]
enum InstrChange {
  None,
  Remove,
  DeleteAfter,
}

impl ConstantFold<'_> {
  fn pass_instr(&self, instr: &mut Instruction) -> InstrChange {
    for input in &mut instr.input {
      match self.value_uses.actual_value(*input) {
        VariableValue::Variable(v) => *input = v.into(),
        VariableValue::Direct(v) => *input = v.into(),
        _ => {}
      }
    }

    InstrChange::None
  }
}

#[cfg(test)]
mod tests {
  use crate::tests::check_transform;

  #[test]
  fn folds_constants() {
    check_transform(
      "constant_fold",
      expect![@r#"
          block 0:
            mov r0 = 0x00
        -   mov r1 = r0
        -   trap
        +   mov r1 = 0x00
        +   trap
      "#],
    );
  }
}
