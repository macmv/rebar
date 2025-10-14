mod elf;
mod instruction;

use std::path::Path;

pub use elf::generate;

pub use instruction::{Immediate, Instruction, ModReg, Opcode, Rex};
use object::write::elf::Rel;
use rb_codegen::InstructionInput;

use crate::instruction::Register;

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

  // TODO: Register allocator anyone?
  let mut reg = Register::Eax;
  fn next_register(reg: Register) -> Register {
    match reg {
      Register::Eax => Register::Edi,
      Register::Edi => Register::Esi,
      Register::Esi => Register::Edx,
      Register::Edx => Register::Eax,
      _ => unimplemented!("no more registers"),
    }
  }

  for block in function.blocks {
    for inst in block.instructions {
      match inst.opcode {
        // lea rsi, [rel symbol]
        rb_codegen::Opcode::Lea(symbol) => {
          builder.reloc(symbol.index, 3, -4);
          builder.instr(Instruction::new(Opcode::LEA).with_rex(Rex::W).with_disp(reg, -4));
          reg = next_register(reg);
        }
        rb_codegen::Opcode::Move => {
          match inst.input[0] {
            // mov rax, imm32
            InstructionInput::Imm(v) => {
              builder.instr(
                Instruction::new(Opcode::MOV_RM_IMM_16)
                  .with_rex(Rex::W)
                  .with_mod(0b11, reg)
                  .with_immediate(Immediate::i32(v)),
              );
              reg = next_register(reg);
            }
            _ => todo!(),
          }
        }
        // syscall
        rb_codegen::Opcode::Syscall => builder.instr(Instruction::new(Opcode::SYSCALL)),
        op => unimplemented!("opcode {:?}", op),
      }
    }

    match block.terminator {
      rb_codegen::TerminatorInstruction::Return => builder.instr(Instruction::new(Opcode::RET)),
      rb_codegen::TerminatorInstruction::Trap => builder.instr(Instruction::new(Opcode::INT3)),
      _ => unimplemented!(),
    }
  }

  builder
}

pub fn link(objects: &[std::path::PathBuf], output: &Path) {
  let mut cmd = std::process::Command::new("wild");
  cmd.arg("-pie");
  cmd.arg("-o").arg(&output);
  for obj in objects {
    cmd.arg(obj);
  }
  let status = cmd.status().expect("failed to execute wild");
  assert!(status.success(), "wild failed");
}

#[cfg(test)]
mod tests {

  use rb_codegen::{Symbol, Variable};
  use rb_test::temp_dir;

  use crate::instruction::Register;

  use super::*;

  #[test]
  fn lower_works() {
    let function = rb_codegen::Function {
      args:   0,
      rets:   0,
      blocks: vec![rb_codegen::Block {
        instructions: vec![
          // write 0 reloc.foo 14
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![1.into()],
            output: smallvec::smallvec![Variable::new(0).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![0.into()],
            output: smallvec::smallvec![Variable::new(1).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Lea(Symbol { index: 1 }),
            input:  smallvec::smallvec![],
            output: smallvec::smallvec![Variable::new(2).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![14.into()],
            output: smallvec::smallvec![Variable::new(3).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Syscall,
            input:  smallvec::smallvec![
              Variable::new(0).into(),
              Variable::new(1).into(),
              Variable::new(2).into(),
              Variable::new(3).into(),
            ],
            output: smallvec::smallvec![],
          },
          // exit 0
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![60.into()],
            output: smallvec::smallvec![Variable::new(4).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![0.into()],
            output: smallvec::smallvec![Variable::new(5).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Syscall,
            input:  smallvec::smallvec![Variable::new(0).into(), Variable::new(1).into(),],
            output: smallvec::smallvec![],
          },
        ],
        terminator:   rb_codegen::TerminatorInstruction::Trap,
      }],
    };

    let data = b"Hello, world!\n";
    let builder = lower(function);

    let dir = temp_dir!();
    let object_path = dir.path().join("foo.o");
    elf::generate(&object_path, &builder.text, data, &builder.relocs);
    link(&[object_path], &dir.path().join("a.out"));
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

    let dir = temp_dir!();
    elf::generate(
      &dir.path().join("foo.o"),
      &text,
      data,
      &[Rel { r_offset: 17, r_sym: 1, r_type: object::elf::R_X86_64_PC32, r_addend: -4 }],
    );
  }
}
