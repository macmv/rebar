use rb_codegen::{
  BlockId, Condition, Immediate, Instruction, InstructionInput, InstructionOutput, Opcode,
};

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
      let mut to_jump = None;
      block.instructions.retain_mut(|instr| {
        if to_jump.is_some() {
          return false;
        }

        match self.pass_instr(instr) {
          InstrChange::None => true,
          InstrChange::Remove => false,
          InstrChange::ReplaceWithJump { target } => {
            to_jump = Some(target);
            false
          }
        }
      });

      if let Some(target) = to_jump {
        block.terminator = rb_codegen::TerminatorInstruction::Jump(target);
      }
    }
  }
}

enum InstrChange {
  None,
  Remove,
  ReplaceWithJump { target: BlockId },
}

impl ConstantFold<'_> {
  fn pass_instr(&self, instr: &mut Instruction) -> InstrChange {
    if let &[InstructionOutput::Var(v)] = instr.output.as_slice() {
      if let VariableValue::Immediate(d) =
        self.value_uses.actual_value(rb_codegen::InstructionInput::Var(v))
      {
        instr.opcode = Opcode::Move;
        instr.input = smallvec![d.into()];
        instr.output = smallvec![v.into()];
        return InstrChange::None;
      }
    }

    for input in &mut instr.input {
      match self.value_uses.actual_value(*input) {
        VariableValue::Variable(v) => *input = v.into(),
        VariableValue::Immediate(v) => *input = v.into(),
        _ => {}
      }
    }

    if let Opcode::Branch(cond, target) = instr.opcode {
      if let &[InstructionInput::Imm(a), InstructionInput::Imm(b)] = instr.input.as_slice()
        && let Some(res) = const_condition(cond, a, b)
      {
        if res {
          return InstrChange::ReplaceWithJump { target };
        } else {
          return InstrChange::Remove;
        }
      }
    }

    InstrChange::None
  }
}

fn const_condition(cond: Condition, a: Immediate, b: Immediate) -> Option<bool> {
  match cond {
    Condition::Equal => rb_codegen::immediate!(a, b, |a, b| a == b),
    Condition::NotEqual => rb_codegen::immediate!(a, b, |a, b| a != b),
    // TODO: Signed-ness
    Condition::Less => rb_codegen::immediate!(a, b, |a, b| a < b),
    Condition::Greater => rb_codegen::immediate!(a, b, |a, b| a > b),
    Condition::LessEqual => rb_codegen::immediate!(a, b, |a, b| a <= b),
    Condition::GreaterEqual => rb_codegen::immediate!(a, b, |a, b| a >= b),
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

  #[test]
  fn folds_bitwise() {
    check_transform(
      "constant_fold",
      expect![@r#"
          block 0:
        -   math(xor) r1 = 0x03, 0x01
        -   math(or) r2 = 0x03, 0x01
        -   math(and) r3 = 0x03, 0x01
        +   mov r1 = 0x02
        +   mov r2 = 0x03
        +   mov r3 = 0x01
            trap
      "#],
    );
  }
}
