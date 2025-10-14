mod elf;
mod instruction;

pub use elf::generate;

pub use instruction::{Immediate, Instruction, ModReg, Opcode, Rex};
use object::write::elf::Rel;

#[derive(Default)]
pub struct Builder {
  pub relocs: Vec<Rel>,
  pub text:   Vec<u8>,
}

impl Builder {
  fn reloc(&mut self, symbol: u32, offset: u64, addend: i64) {
    self.relocs.push(Rel {
      r_offset: self.text.len() as u64 + offset,
      r_sym:    symbol,
      r_type:   object::elf::R_X86_64_PC32,
      r_addend: addend,
    });
  }

  fn instr(&mut self, instr: Instruction) {
    let (bytes, len) = instr.encode();
    self.text.extend_from_slice(&bytes[..len]);
  }
}

pub fn lower(function: rb_codegen::Function) -> Builder {
  let mut builder = Builder::default();

  for block in function.blocks {
    for inst in block.instructions {
      match inst.opcode {
        // lea rsi, [rel symbol]
        rb_codegen::Opcode::Lea(symbol) => {
          builder.reloc(symbol.index, 3, -4);
          builder.instr(
            Instruction::new(Opcode::LEA)
              .with_rex(Rex::W)
              .with_disp(instruction::Register::Esi, -4),
          );
        }
        // syscall
        rb_codegen::Opcode::Syscall => builder.instr(Instruction::new(Opcode::SYSCALL)),
        op => unimplemented!("opcode {:?}", op),
      }
    }

    match block.terminator {
      rb_codegen::TerminatorInstruction::Return => builder.instr(Instruction::new(Opcode::RET)),
      _ => unimplemented!(),
    }
  }

  builder
}

#[cfg(test)]
mod tests {

  use rb_codegen::{Symbol, Variable};

  use crate::instruction::Register;

  use super::*;

  #[test]
  fn lower_works() {
    let function = rb_codegen::Function {
      args:   0,
      rets:   0,
      blocks: vec![rb_codegen::Block {
        instructions: vec![
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Lea(Symbol { index: 2 }),
            input:  smallvec::smallvec![],
            output: smallvec::smallvec![Variable::new(0).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Syscall,
            input:  smallvec::smallvec![
              rb_codegen::InstructionInput::Imm(1),
              rb_codegen::InstructionInput::Imm(0),
              Variable::new(0).into(),
              rb_codegen::InstructionInput::Imm(10),
            ],
            output: smallvec::smallvec![],
          },
        ],
        terminator:   rb_codegen::TerminatorInstruction::Return,
      }],
    };

    let data = b"Hello, world!\n";
    let builder = lower(function);

    elf::generate("foo.o", &builder.text, data, &builder.relocs);
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

    elf::generate(
      "foo.o",
      &text,
      data,
      &[Rel { r_offset: 17, r_sym: 2, r_type: object::elf::R_X86_64_PC32, r_addend: -4 }],
    );
  }
}
