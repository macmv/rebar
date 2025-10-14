mod elf;
mod instruction;

pub use elf::generate;

pub use instruction::{Immediate, Instruction, ModReg, Opcode, Rex};

#[derive(Default)]
struct Builder {
  text: Vec<u8>,
}

impl Builder {
  fn instr(&mut self, instr: Instruction) {
    let (bytes, len) = instr.encode();
    self.text.extend_from_slice(&bytes[..len]);
  }
}

pub fn lower(function: rb_codegen::Function) -> Vec<u8> {
  let mut builder = Builder::default();

  for block in function.blocks {
    for inst in block.instructions {
      match inst.opcode {
        rb_codegen::Opcode::Syscall => builder.instr(Instruction::new(Opcode::SYSCALL)),
        op => unimplemented!("opcode {:?}", op),
      }
    }

    match block.terminator {
      rb_codegen::TerminatorInstruction::Return => builder.instr(Instruction::new(Opcode::RET)),
      _ => unimplemented!(),
    }
  }

  builder.text
}

#[cfg(test)]
mod tests {

  use crate::instruction::Register;

  use super::*;

  #[test]
  fn lower_works() {
    let function = rb_codegen::Function {
      args:   0,
      rets:   0,
      blocks: vec![rb_codegen::Block {
        instructions: vec![rb_codegen::Instruction {
          opcode: rb_codegen::Opcode::Syscall,
          input:  smallvec::smallvec![
            rb_codegen::InstructionInput::Imm(1),
            rb_codegen::InstructionInput::Imm(0),
            rb_codegen::InstructionInput::Imm(-4_i32 as u32),
            rb_codegen::InstructionInput::Imm(10),
          ],
          output: smallvec::smallvec![],
        }],
        terminator:   rb_codegen::TerminatorInstruction::Return,
      }],
    };

    let data = b"Hello, world!\n";
    let text = lower(function);

    elf::generate("foo.o", &text, data);
  }

  #[test]
  fn foo_works() {
    let mut text = vec![];

    let data = b"Hello, world!\n";

    let instructions = [
      // `write 0 reloc.foo 3`
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_rex(Rex::W)
        .with_mod(0b11, Register::Eax)
        .with_immediate(Immediate::i32(1)),
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_rex(Rex::W)
        .with_mod(0b11, Register::Edi)
        .with_immediate(Immediate::i32(0)),
      Instruction::new(Opcode::LEA).with_rex(Rex::W).with_disp(Register::Esi, -4),
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_rex(Rex::W)
        .with_mod(0b11, Register::Edx)
        .with_immediate(Immediate::i32(data.len() as u32)),
      Instruction::new(Opcode::SYSCALL),
      // `exit 0`
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_rex(Rex::W)
        .with_mod(0b11, Register::Eax)
        .with_immediate(Immediate::i32(60)),
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_rex(Rex::W)
        .with_mod(0b11, Register::Edi)
        .with_immediate(Immediate::i32(0)),
      Instruction::new(Opcode::SYSCALL),
    ];

    for inst in &instructions {
      let (bytes, len) = inst.encode();
      text.extend_from_slice(&bytes[..len]);
    }

    elf::generate("foo.o", &text, data);
  }
}
