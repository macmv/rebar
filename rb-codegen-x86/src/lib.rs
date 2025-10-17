mod elf;
mod instruction;

use std::path::Path;

pub use elf::generate;

pub use instruction::{Immediate, Instruction, ModReg, Opcode, Prefix};
use object::write::elf::Rel;
use rb_codegen::{InstructionInput, InstructionOutput, Math};

use crate::{
  instruction::RegisterIndex,
  regalloc::{Register, RegisterSize, VariableRegisters},
};

mod regalloc;

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

pub fn lower(mut function: rb_codegen::Function) -> Builder {
  let mut builder = Builder::default();

  let mut reg = VariableRegisters::new();
  reg.pass(&mut function);

  for block in &function.blocks {
    for inst in &block.instructions {
      match inst.opcode {
        rb_codegen::Opcode::Math(
          math @ (Math::Add | Math::Sub | Math::And | Math::Or | Math::Xor),
        ) => match (inst.output[0], inst.input[0], inst.input[1]) {
          (InstructionOutput::Var(v), InstructionInput::Var(a), InstructionInput::Imm(b)) => {
            encode_binary_reg_imm(
              &mut builder,
              reg.get(v),
              reg.get(a),
              b,
              match math {
                Math::Add => Opcode::ADD_IMM8,
                Math::Sub => Opcode::SUB_IMM8,
                Math::And => Opcode::AND_IMM8,
                Math::Or => Opcode::OR_IMM8,
                Math::Xor => Opcode::XOR_IMM8,
                _ => unreachable!(),
              },
              match math {
                Math::Add => Opcode::ADD_IMM32,
                Math::Sub => Opcode::SUB_IMM32,
                Math::And => Opcode::AND_IMM32,
                Math::Or => Opcode::OR_IMM32,
                Math::Xor => Opcode::XOR_IMM32,
                _ => unreachable!(),
              },
            );
          }
          (InstructionOutput::Var(v), InstructionInput::Var(a), InstructionInput::Var(b)) => {
            encode_binary_reg_reg(
              &mut builder,
              reg.get(v),
              reg.get(a),
              reg.get(b),
              match math {
                Math::Add => Opcode::ADD_RM8,
                Math::Sub => Opcode::SUB_RM8,
                Math::And => Opcode::AND_RM8,
                Math::Or => Opcode::OR_RM8,
                Math::Xor => Opcode::XOR_RM8,
                _ => unreachable!(),
              },
              match math {
                Math::Add => Opcode::ADD_RM32,
                Math::Sub => Opcode::SUB_RM32,
                Math::And => Opcode::AND_RM32,
                Math::Or => Opcode::OR_RM32,
                Math::Xor => Opcode::XOR_RM32,
                _ => unreachable!(),
              },
            );
          }
          _ => todo!("inst {:?}", inst),
        },
        rb_codegen::Opcode::Math(
          math @ (Math::Imul
          | Math::Umul
          | Math::Idiv
          | Math::Udiv
          | Math::Neg
          | Math::Not
          | Math::Irem
          | Math::Urem),
        ) => {
          // digits: not=2, neg=3, umul=4, imul=5, udiv=6, idiv=7

          let opcode_digit = match math {
            Math::Not => 2,
            Math::Neg => 3,
            Math::Umul => 4,
            Math::Imul => 5,
            Math::Udiv | Math::Urem => 6,
            Math::Idiv | Math::Irem => 7,
            _ => unreachable!(),
          };

          match (inst.output[0], inst.input[0], inst.input[1]) {
            (InstructionOutput::Var(v), InstructionInput::Var(a), InstructionInput::Var(b)) => {
              debug_assert_eq!(reg.get(v).size, reg.get(a).size, "mul must have the same size");
              debug_assert_eq!(reg.get(v).size, reg.get(b).size, "mul must have the same size");
              match math {
                Math::Urem | Math::Irem => {
                  debug_assert_eq!(reg.get(v).index, RegisterIndex::Edx, "rem must output to edx");
                }
                _ => {
                  debug_assert_eq!(reg.get(v).index, RegisterIndex::Eax, "math must output to eax");
                }
              }
              let a = reg.get(a);
              let b = reg.get(b);

              if a.index == RegisterIndex::Eax {
                builder.instr(
                  encode_sized(a.size, Opcode::MATH_EAX_RM8, Opcode::MATH_EAX_RM32)
                    .with_digit(opcode_digit)
                    .with_mod(0b11, b.index),
                );
              } else if b.index == RegisterIndex::Eax {
                builder.instr(
                  encode_sized(b.size, Opcode::MATH_EAX_RM8, Opcode::MATH_EAX_RM32)
                    .with_digit(opcode_digit)
                    .with_mod(0b11, a.index),
                );
              } else {
                panic!("mul must multiply from eax");
              }
            }
            _ => todo!("inst {:?}", inst),
          }
        }
        rb_codegen::Opcode::Math(math @ (Math::Shl | Math::Ushr | Math::Ishr)) => {
          let opcode_digit = match math {
            Math::Shl => 4,
            Math::Ushr => 5,
            Math::Ishr => 7,
            _ => unreachable!(),
          };

          match (inst.output[0], inst.input[0], inst.input[1]) {
            (InstructionOutput::Var(v), InstructionInput::Var(a), InstructionInput::Var(b)) => {
              debug_assert_eq!(reg.get(v).size, reg.get(a).size, "shifts must be in place");
              debug_assert_eq!(
                reg.get(b).index,
                RegisterIndex::Ecx,
                "shifts can only use ecx as their operand"
              );

              builder.instr(
                encode_sized(reg.get(v).size, Opcode::SHIFT_C_8, Opcode::SHIFT_C_32)
                  .with_digit(opcode_digit)
                  .with_mod(0b11, reg.get(v).index),
              );
            }
            _ => todo!("inst {:?}", inst),
          }
        }
        rb_codegen::Opcode::Lea(symbol) => match inst.output[0] {
          // lea reg, [rel symbol]
          InstructionOutput::Var(v) => {
            builder.reloc(symbol.index, 3, -4);
            let reg = reg.get(v);
            debug_assert_eq!(reg.size, RegisterSize::Bit64, "lea only supports 64-bit registers");
            builder.instr(
              Instruction::new(Opcode::LEA).with_prefix(Prefix::RexW).with_disp(reg.index, -4),
            );
          }
          _ => todo!("inst {:?}", inst),
        },
        rb_codegen::Opcode::Move => {
          match (inst.output[0], inst.input[0]) {
            // mov reg, imm32
            (InstructionOutput::Var(o), InstructionInput::Imm(i)) => {
              let reg = reg.get(o);
              match reg.size {
                RegisterSize::Bit8 => builder.instr(
                  Instruction::new(Opcode::MOV_RD_IMM_8.with_rd(reg.index))
                    .with_immediate(Immediate::i8(i.try_into().unwrap())),
                ),
                RegisterSize::Bit16 => builder.instr(
                  Instruction::new(Opcode::MOV_RD_IMM_16.with_rd(reg.index))
                    .with_prefix(Prefix::OperandSizeOverride)
                    .with_immediate(Immediate::i16(i.try_into().unwrap())),
                ),
                RegisterSize::Bit32 => builder.instr(
                  Instruction::new(Opcode::MOV_RD_IMM_16.with_rd(reg.index))
                    .with_immediate(Immediate::i32(i.try_into().unwrap())),
                ),
                RegisterSize::Bit64 => {
                  if let Ok(i) = u32::try_from(i) {
                    // 32-bit registers get zero-extended to 64-bit
                    builder.instr(
                      Instruction::new(Opcode::MOV_RD_IMM_16.with_rd(reg.index))
                        .with_immediate(Immediate::i32(i)),
                    );
                  } else {
                    // TODO: Use the sign-extending `mov` if possible.
                    builder.instr(
                      Instruction::new(Opcode::MOV_RD_IMM_16)
                        .with_prefix(Prefix::RexW)
                        .with_immediate(Immediate::i64(i.into())),
                    );
                  }
                }
              }
            }

            // mov reg, reg
            (InstructionOutput::Var(o), InstructionInput::Var(i)) => {
              debug_assert_eq!(
                reg.get(o).size,
                reg.get(i).size,
                "move must have the same size for input and output"
              );

              let o = reg.get(o);
              let i = reg.get(i);
              match o.size {
                RegisterSize::Bit8 => builder.instr(
                  Instruction::new(Opcode::MOV_MR_8).with_mod(0b11, o.index).with_reg(i.index),
                ),
                RegisterSize::Bit16 => builder.instr(
                  Instruction::new(Opcode::MOV_MR_8)
                    .with_prefix(Prefix::OperandSizeOverride)
                    .with_mod(0b11, o.index)
                    .with_reg(i.index),
                ),
                RegisterSize::Bit32 => builder.instr(
                  Instruction::new(Opcode::MOV_MR_32.with_rd(o.index))
                    .with_mod(0b11, o.index)
                    .with_reg(i.index),
                ),
                RegisterSize::Bit64 => builder.instr(
                  Instruction::new(Opcode::MOV_MR_32.with_rd(o.index))
                    .with_prefix(Prefix::RexW)
                    .with_mod(0b11, o.index)
                    .with_reg(i.index),
                ),
              }
            }

            _ => todo!("mov {inst:?}"),
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

fn encode_binary_reg_imm(
  builder: &mut Builder,
  output: Register,
  input1: Register,
  input2: u64,
  opcode_8: Opcode,
  opcode_32: Opcode,
) {
  debug_assert_eq!(output.size, input1.size, "binary must have the same size");

  builder.instr(
    encode_sized(output.size, opcode_8, opcode_32)
      .with_mod(0b11, input1.index)
      .with_reg(output.index)
      .with_immediate(Immediate::for_size(input2, output.size)),
  );
}

fn encode_binary_reg_reg(
  builder: &mut Builder,
  output: Register,
  input1: Register,
  input2: Register,
  opcode_8: Opcode,
  opcode_32: Opcode,
) {
  debug_assert_eq!(output.size, input1.size, "binary must have the same size");
  debug_assert_eq!(output.size, input2.size, "binary must have the same size");

  if input1 == output {
    builder.instr(
      encode_sized(output.size, opcode_8, opcode_32)
        .with_mod(0b11, input2.index)
        .with_reg(output.index),
    );
  } else if input2 == output {
    builder.instr(
      encode_sized(output.size, opcode_8, opcode_32)
        .with_mod(0b11, input1.index)
        .with_reg(output.index),
    );
  } else {
    panic!("binary must be in-place");
  }
}

fn encode_sized(size: RegisterSize, opcode_8: Opcode, opcode_32: Opcode) -> Instruction {
  match size {
    RegisterSize::Bit8 => Instruction::new(opcode_8),
    RegisterSize::Bit16 => Instruction::new(opcode_32).with_prefix(Prefix::OperandSizeOverride),
    RegisterSize::Bit32 => Instruction::new(opcode_32),
    RegisterSize::Bit64 => Instruction::new(opcode_32).with_prefix(Prefix::RexW),
  }
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

  use rb_codegen::{Signature, Symbol, Variable, VariableSize};
  use rb_test::{Expect, expect, temp_dir};

  use crate::instruction::RegisterIndex;

  use super::*;

  fn disass(path: &Path, expected: Expect) {
    let output = std::process::Command::new("r2")
      .arg("-e scr.color=0")
      .arg("-e asm.comments=false")
      .arg("-e asm.nbytes=10")
      .arg("-qc")
      .arg("pD `iS~.text[2]`")
      .arg(path)
      .output()
      .expect("failed to execute objdump");
    assert!(output.status.success());
    let output = String::from_utf8(output.stdout).unwrap();
    let output =
      output.lines().skip(2).map(|l| l.trim_start()).collect::<Vec<_>>().join("\n") + "\n";
    expected.assert_eq(&output);
  }

  #[allow(unused)]
  fn disass_objdump(path: &Path, expected: Expect) {
    let output = std::process::Command::new("objdump")
      .arg("-Mintel")
      .arg("-d")
      .arg(path)
      .output()
      .expect("failed to execute objdump");
    assert!(output.status.success());
    let output = String::from_utf8(output.stdout).unwrap();
    let line = output.lines().position(|l| l.contains("<_start>:")).unwrap();
    let output = output
      .lines()
      .skip(line + 1)
      .map(|l| l.strip_prefix("  ").unwrap_or(l).replace("\t", "  "))
      .collect::<Vec<_>>()
      .join("\n")
      + "\n";
    expected.assert_eq(&output);
  }

  #[test]
  fn mov_small_variables() {
    let function = rb_codegen::Function {
      sig:    Signature { args: vec![], rets: vec![] },
      blocks: vec![rb_codegen::Block {
        instructions: vec![
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![3.into()],
            output: smallvec::smallvec![Variable::new(0, VariableSize::Bit8).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![5.into()],
            output: smallvec::smallvec![Variable::new(1, VariableSize::Bit16).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![7.into()],
            output: smallvec::smallvec![Variable::new(2, VariableSize::Bit32).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![9.into()],
            output: smallvec::smallvec![Variable::new(3, VariableSize::Bit64).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![(u32::MAX as u64 + 5).into()],
            output: smallvec::smallvec![Variable::new(4, VariableSize::Bit64).into()],
          },
        ],
        terminator:   rb_codegen::TerminatorInstruction::Trap,
      }],
    };

    let builder = lower(function);

    let dir = temp_dir!();
    let object_path = dir.path().join("foo.o");
    elf::generate(&object_path, &builder.text, b"", &builder.relocs);
    disass(
      &object_path,
      expect![@r#"
        0x08000250      b003                   mov al, 3
        0x08000252      66b80500               mov ax, 5
        0x08000256      b807000000             mov eax, 7
        0x0800025b      b809000000             mov eax, 9
        0x08000260      48b80400000001000000   movabs rax, 0x100000004
        0x0800026a      cc                     int3
      "#],
    );
  }

  #[test]
  fn lower_works() {
    let v0 = Variable::new(0, VariableSize::Bit64);
    let v1 = Variable::new(1, VariableSize::Bit64);
    let v2 = Variable::new(2, VariableSize::Bit64);
    let v3 = Variable::new(3, VariableSize::Bit64);
    let v4 = Variable::new(4, VariableSize::Bit64);
    let v5 = Variable::new(5, VariableSize::Bit64);

    let function = rb_codegen::Function {
      sig:    Signature { args: vec![], rets: vec![] },
      blocks: vec![rb_codegen::Block {
        instructions: vec![
          // write 1 reloc.foo 14
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![1.into()],
            output: smallvec::smallvec![v0.into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![1.into()],
            output: smallvec::smallvec![v1.into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Lea(Symbol { index: 1 }),
            input:  smallvec::smallvec![],
            output: smallvec::smallvec![v2.into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![14.into()],
            output: smallvec::smallvec![v3.into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Syscall,
            input:  smallvec::smallvec![v0.into(), v1.into(), v2.into(), v3.into()],
            output: smallvec::smallvec![],
          },
          // exit 0
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![60.into()],
            output: smallvec::smallvec![v4.into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![0.into()],
            output: smallvec::smallvec![v5.into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Syscall,
            input:  smallvec::smallvec![v4.into(), v5.into(),],
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
    let binary_path = dir.path().join("a.out");
    elf::generate(&object_path, &builder.text, data, &builder.relocs);
    link(&[object_path], &binary_path);
    let output = std::process::Command::new(binary_path).output().expect("failed to execute a.out");
    assert!(output.status.success());
    assert_eq!(&output.stdout, data);
  }

  #[test]
  fn foo_works() {
    let mut text = vec![];

    let data = b"Hello, world!\n";

    let instructions = [
      // `write 1 reloc.foo 3`
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_prefix(Prefix::RexW)
        .with_mod(0b11, RegisterIndex::Eax)
        .with_immediate(Immediate::i32(1)),
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_prefix(Prefix::RexW)
        .with_mod(0b11, RegisterIndex::Edi)
        .with_immediate(Immediate::i32(1)),
      Instruction::new(Opcode::LEA).with_prefix(Prefix::RexW).with_disp(RegisterIndex::Esi, -4),
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_prefix(Prefix::RexW)
        .with_mod(0b11, RegisterIndex::Edx)
        .with_immediate(Immediate::i32(data.len() as u32)),
      Instruction::new(Opcode::SYSCALL),
      // `exit 0`
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_prefix(Prefix::RexW)
        .with_mod(0b11, RegisterIndex::Eax)
        .with_immediate(Immediate::i32(60)),
      Instruction::new(Opcode::MOV_RM_IMM_16)
        .with_prefix(Prefix::RexW)
        .with_mod(0b11, RegisterIndex::Edi)
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
