use rb_codegen::{Instruction, InstructionOutput, Opcode};

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
    match instr.output.as_slice() {
      &[InstructionOutput::Var(v)] => {
        match self.value_uses.actual_value(rb_codegen::InstructionInput::Var(v)) {
          VariableValue::Direct(d) => {
            instr.opcode = Opcode::Move;
            instr.input = smallvec![d.into()];
            instr.output = smallvec![v.into()];
            return InstrChange::None;
          }
          _ => {}
        }
      }
      _ => {}
    }

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
  fn fold_constants() {
    check_transform(
      "constant_fold",
      expect![@r#"
          block 0:
            mov r0 = 0x00
        -   mov r1 = r0
        +   mov r1 = 0x00
            trap
      "#],
    );

    check_transform(
      "constant_fold",
      expect![@r#"
          block 0:
            mov r0 = 0x00
        -   mov r1 = r0
        -   mov r2 = r1
        +   mov r1 = 0x00
        +   mov r2 = 0x00
            trap
      "#],
    );
  }

  #[test]
  fn fold_adds() {
    check_transform(
      "constant_fold",
      expect![@r#"
          block 0:
            mov r0 = 0x01
        -   math(add) r1 = r0, 0x02
        +   mov r1 = 0x03
            trap
      "#],
    );
  }
}
