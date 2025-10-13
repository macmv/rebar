mod elf;
mod instruction;

pub use elf::generate;

pub use instruction::{Immediate, Instruction, ModRm, Opcode, Rex};

#[cfg(test)]
mod tests {

  use crate::instruction::Register;

  use super::*;

  #[test]
  fn foo_works() {
    let mut text = vec![];

    let instructions = [
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_rex(Rex::W)
        .with_reg(Register::Eax)
        .with_immediate(Immediate::i32(60)),
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_rex(Rex::W)
        .with_reg(Register::Edi)
        .with_immediate(Immediate::i32(0)),
      Instruction::new(Opcode::SYSCALL),
    ];

    for inst in &instructions {
      let (bytes, len) = inst.encode();
      text.extend_from_slice(&bytes[..len]);
    }

    elf::generate("foo.o", &text);
  }
}
