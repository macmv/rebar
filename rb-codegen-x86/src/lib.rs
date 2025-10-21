mod elf;
mod instruction;

use std::path::Path;

pub use elf::generate;

pub use instruction::{Immediate, Instruction, ModReg, Opcode, Prefix};
use object::write::elf::Rel;
use rb_codegen::{
  BlockId, FunctionId, InstructionInput, InstructionOutput, Math, Symbol, SymbolDef, VariableSize,
  immediate,
};

use crate::{
  instruction::RegisterIndex,
  regalloc::{Register, RegisterSize, VariableRegisters},
};

mod regalloc;

#[derive(Default)]
pub struct ObjectBuilder {
  relocs:       Vec<Rel>,
  functions:    Vec<u64>,
  text:         Vec<u8>,
  calls:        Vec<Call>,
  ro_data:      Vec<u8>,
  data_symbols: Vec<SymbolDef>,
}

struct Call {
  offset: u64,
  target: FunctionId,
}

#[derive(Default)]
pub struct Object {
  text:         Vec<u8>,
  ro_data:      Vec<u8>,
  relocs:       Vec<Rel>,
  data_symbols: Vec<SymbolDef>,
}

#[derive(Default)]
pub struct Builder {
  relocs:        Vec<Rel>,
  calls:         Vec<Call>,
  jumps:         Vec<Jump>,
  block_offsets: Vec<u64>,
  text:          Vec<u8>,
}

pub struct Jump {
  pub size:   RegisterSize,
  pub offset: u64,
  pub target: BlockId,
}

impl ObjectBuilder {
  pub fn add_function(&mut self, mut function: rb_codegen::Function) {
    self.ro_data.extend_from_slice(&function.data);
    self.data_symbols.extend(function.data_symbols.drain(..));

    let lowered = lower(function);

    let offset = self.text.len() as u64;
    self.text.extend_from_slice(&lowered.text);
    self
      .relocs
      .extend(lowered.relocs.into_iter().map(|rel| Rel { r_offset: rel.r_offset + offset, ..rel }));
    self
      .calls
      .extend(lowered.calls.into_iter().map(|call| Call { offset: call.offset + offset, ..call }));
    self.functions.push(offset);
  }

  pub fn finish(mut self) -> Object {
    for call in self.calls {
      let rel = self.functions[call.target.as_u32() as usize] as i64 - (call.offset as i64 + 4);
      if let Ok(offset) = i32::try_from(rel) {
        self.text[call.offset as usize..call.offset as usize + 4]
          .copy_from_slice(&offset.to_le_bytes());
      } else {
        panic!("call target too far away");
      }
    }

    Object {
      text:         self.text,
      ro_data:      self.ro_data,
      relocs:       self.relocs,
      data_symbols: self.data_symbols,
    }
  }
}

impl Object {
  pub fn save(&self, path: &Path) { elf::generate(path, self); }
}

impl Builder {
  fn finish(mut self) -> Self {
    self.fill_jumps();

    self
  }

  fn fill_jumps(&mut self) {
    for jump in self.jumps.iter().rev() {
      let target_offset = self.block_offsets[jump.target.as_u32() as usize];
      let jump_offset = jump.offset;

      let relative_offset =
        i32::try_from((target_offset as i64) - (jump_offset as i64 + 1)).unwrap();
      match (jump.size, i8::try_from(relative_offset)) {
        (RegisterSize::Bit8, Ok(rel)) => {
          self.text[jump_offset as usize..jump_offset as usize + 1]
            .copy_from_slice(&rel.to_le_bytes());
        }
        // An 8-bit offset wasn't possible, so we re-encode it to a 32-bit offset.
        (RegisterSize::Bit8, Err(_)) => {
          let new_opcode: &[u8] = match self.text[jump_offset as usize - 1] {
            0xeb => &[0xe9], // jmp
            0xe3 => panic!("cannot re-encode JECXZ to a 32-bit offset"),
            0x77 => &[0x0f, 0x87], // ja
            0x73 => &[0x0f, 0x83], // jae
            0x72 => &[0x0f, 0x82], // jb
            0x76 => &[0x0f, 0x86], // jbe
            opcode => panic!("unsupported 8-bit jump opcode {opcode:#x}"),
          };

          self
            .text
            .splice(jump_offset as usize - 1..jump_offset as usize, new_opcode.iter().copied());
          self.text.splice(
            jump_offset as usize + new_opcode.len() - 1..jump_offset as usize + new_opcode.len(),
            relative_offset.to_le_bytes(),
          );
          // TODO: Any jumps in the list before where we are right now need to
          // be adjusted.
        }
        (RegisterSize::Bit32, _) => {
          self.text[jump_offset as usize..jump_offset as usize + 4]
            .copy_from_slice(&relative_offset.to_le_bytes());
        }

        _ => panic!("unsupported jump size {:?}", jump.size),
      }
    }
  }

  fn reloc(&mut self, symbol: Symbol, offset: u64, addend: i64) {
    self.relocs.push(Rel {
      r_offset: offset,
      r_sym:    symbol.index,
      r_type:   object::elf::R_X86_64_PC32,
      r_addend: addend,
    });
  }

  fn start_block(&mut self) { self.block_offsets.push(self.text.len() as u64); }

  fn jmp(&mut self, target: BlockId, size: RegisterSize) {
    self.jumps.push(Jump { size, offset: self.text.len() as u64 + 1, target });
  }

  fn call(&mut self, target: FunctionId) {
    self.calls.push(Call { offset: self.text.len() as u64 + 1, target });
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

  for id in function.blocks() {
    let block = function.block(id);
    builder.start_block();

    for inst in &block.instructions {
      match inst.opcode {
        rb_codegen::Opcode::Math(
          math @ (Math::Add | Math::Sub | Math::And | Math::Or | Math::Xor),
        ) => match (inst.output[0], inst.input[0], inst.input[1]) {
          (InstructionOutput::Var(v), InstructionInput::Var(a), InstructionInput::Imm(b)) => {
            debug_assert_eq!(reg.get(v), reg.get(a), "math must be in-place");

            fn opcode_8_for_math(math: Math) -> Opcode {
              match math {
                Math::Add => Opcode::ADD_A_IMM8,
                Math::Sub => Opcode::SUB_A_IMM8,
                Math::And => Opcode::AND_A_IMM8,
                Math::Or => Opcode::OR_A_IMM8,
                Math::Xor => Opcode::XOR_A_IMM8,
                _ => unreachable!(),
              }
            }

            fn digit_for_math(math: Math) -> u8 {
              match math {
                Math::Add => 0,
                Math::Sub => 5,
                Math::And => 4,
                Math::Or => 1,
                Math::Xor => 6,
                _ => unreachable!(),
              }
            }

            // First, prefer the accumulator-specific instructions, as those are shortest.
            if reg.get(v) == Register::AL {
              debug_assert_eq!(reg.get(v).size, reg.get(a).size, "math must be in-place");
              debug_assert_eq!(
                reg.get(v).size,
                var_to_reg_size(b.size()).unwrap(),
                "AL must have 8 bit operand"
              );
              builder.instr(
                Instruction::new(opcode_8_for_math(math)).with_immediate(Immediate::from(b)),
              );
            } else {
              match imm_to_i8(b) {
                // Next, try to fit in an imm8
                Some(imm8) => builder.instr(
                  encode_sized(reg.get(v).size, Opcode::MATH_IMM8, Opcode::MATH_EXT_IMM8)
                    .with_mod(0b11, reg.get(v).index)
                    .with_immediate(Immediate::i8(imm8 as u8))
                    .with_digit(digit_for_math(math)),
                ),
                // Doesn't fit in an imm8, use the accumulator-specific form if possible
                None if reg.get(v).index == RegisterIndex::Eax => builder.instr(
                  encode_binary_reg_imm(
                    reg.get(v),
                    b,
                    opcode_8_for_math(math),
                    match math {
                      Math::Add => Opcode::ADD_A_IMM32,
                      Math::Sub => Opcode::SUB_A_IMM32,
                      Math::And => Opcode::AND_A_IMM32,
                      Math::Or => Opcode::OR_A_IMM32,
                      Math::Xor => Opcode::XOR_A_IMM32,
                      _ => unreachable!(),
                    },
                  )
                  .with_digit(digit_for_math(math)),
                ),
                // Doesn't fit in an imm8, use the normal immediate form
                None => builder.instr(
                  encode_binary_reg_imm(reg.get(v), b, Opcode::MATH_IMM8, Opcode::MATH_IMM32)
                    .with_digit(digit_for_math(math)),
                ),
              }
            }
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
        rb_codegen::Opcode::Compare(_) => match (inst.output[0], inst.input[0], inst.input[1]) {
          (InstructionOutput::Var(v), InstructionInput::Var(a), InstructionInput::Imm(b)) => {
            // FIXME: This is wrong. `CMP_A` doesn't take a mod/rm byte.
            debug_assert_eq!(reg.get(v), reg.get(a), "compare must be in-place");

            builder.instr(encode_binary_reg_imm(
              reg.get(v),
              b,
              Opcode::CMP_A_IMM8,
              Opcode::CMP_A_IMM32,
            ));
          }
          (InstructionOutput::Var(v), InstructionInput::Var(a), InstructionInput::Var(b)) => {
            encode_binary_reg_reg(
              &mut builder,
              reg.get(v),
              reg.get(a),
              reg.get(b),
              Opcode::CMP_RM8,
              Opcode::CMP_RM32,
            );
          }
          _ => todo!("inst {:?}", inst),
        },
        rb_codegen::Opcode::Branch(condition, target) => match (inst.input[0], inst.input[1]) {
          (InstructionInput::Var(a), InstructionInput::Imm(b)) => {
            let a = reg.get(a);

            if b.is_zero() {
              builder.instr(
                encode_sized(a.size, Opcode::TEST_MR8, Opcode::TEST_MR32)
                  .with_mod(0b11, a.index)
                  .with_reg(a.index),
              );
            } else if a.index == RegisterIndex::Eax {
              debug_assert_eq!(a.size, var_to_reg_size(b.size()).unwrap());

              match b {
                // TODO: CMP imm64 doesn't exist, need to move it to a register.
                rb_codegen::Immediate::I64(v) => {
                  builder.instr(
                    encode_sized(a.size, Opcode::CMP_A_IMM8, Opcode::CMP_A_IMM32)
                      .with_immediate(Immediate::i32(v.try_into().unwrap())),
                  );
                }
                rb_codegen::Immediate::U64(v) => {
                  builder.instr(
                    encode_sized(a.size, Opcode::CMP_A_IMM8, Opcode::CMP_A_IMM32)
                      .with_immediate(Immediate::i32(v.try_into().unwrap())),
                  );
                }
                _ => {
                  builder.instr(
                    encode_sized(a.size, Opcode::CMP_A_IMM8, Opcode::CMP_A_IMM32)
                      .with_immediate(Immediate::from(b)),
                  );
                }
              }
            } else {
              todo!("encode comparisons with other registers");
            }

            let opcode = match condition {
              rb_codegen::Condition::Equal => Opcode::JE,
              rb_codegen::Condition::NotEqual => Opcode::JNE,
              rb_codegen::Condition::Greater => Opcode::JG,
              rb_codegen::Condition::Less => Opcode::JB,
              rb_codegen::Condition::GreaterEqual => Opcode::JGE,
              rb_codegen::Condition::LessEqual => Opcode::JLE,
            };

            builder.jmp(target, RegisterSize::Bit8);
            builder.instr(Instruction::new(opcode).with_immediate(Immediate::i8(0)))
          }
          (InstructionInput::Var(a), InstructionInput::Var(b)) => {
            builder.instr(
              encode_sized(reg.get(a).size, Opcode::CMP_RM8, Opcode::CMP_RM32)
                .with_mod(0b11, reg.get(a).index)
                .with_reg(reg.get(b).index),
            );

            let opcode = match condition {
              rb_codegen::Condition::Equal => Opcode::JE,
              rb_codegen::Condition::NotEqual => Opcode::JNE,
              rb_codegen::Condition::Greater => Opcode::JG,
              rb_codegen::Condition::Less => Opcode::JB,
              rb_codegen::Condition::GreaterEqual => Opcode::JGE,
              rb_codegen::Condition::LessEqual => Opcode::JLE,
            };

            builder.jmp(target, RegisterSize::Bit8);
            builder.instr(Instruction::new(opcode).with_immediate(Immediate::i8(0)))
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
              debug_assert_eq!(reg.get(v), reg.get(a), "shifts must be in place");
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
            (InstructionOutput::Var(v), InstructionInput::Var(a), InstructionInput::Imm(b)) => {
              let b = match b {
                rb_codegen::Immediate::I8(v) => v,
                // TODO: Get rid of this once number typing is sane.
                rb_codegen::Immediate::U64(v) => v as i8,
                _ => panic!("shift immediate must be an 8-bit value"),
              };

              debug_assert_eq!(reg.get(v), reg.get(a), "shifts must be in place");
              if b == 1 {
                builder.instr(
                  encode_sized(reg.get(v).size, Opcode::SHIFT_1_8, Opcode::SHIFT_1_32)
                    .with_digit(opcode_digit)
                    .with_mod(0b11, reg.get(v).index),
                );
              } else {
                builder.instr(
                  encode_sized(reg.get(v).size, Opcode::SHIFT_IMM_8, Opcode::SHIFT_IMM_32)
                    .with_digit(opcode_digit)
                    .with_mod(0b11, reg.get(v).index)
                    .with_immediate(Immediate::i8(b as u8)),
                );
              }
            }
            _ => todo!("inst {:?}", inst),
          }
        }
        rb_codegen::Opcode::Lea(symbol) => match inst.output[0] {
          // lea reg, [rel symbol]
          InstructionOutput::Var(v) => {
            builder.reloc(symbol, 3, -4);
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
              debug_assert_eq!(reg.size, var_to_reg_size(i.size()).unwrap());
              let imm = Immediate::from(i);
              match reg.size {
                RegisterSize::Bit8 => builder.instr(
                  Instruction::new(Opcode::MOV_RD_IMM_8.with_rd(reg.index)).with_immediate(imm),
                ),
                RegisterSize::Bit16 => builder.instr(
                  Instruction::new(Opcode::MOV_RD_IMM_16.with_rd(reg.index))
                    .with_prefix(Prefix::OperandSizeOverride)
                    .with_immediate(imm),
                ),
                RegisterSize::Bit32 => builder.instr(
                  Instruction::new(Opcode::MOV_RD_IMM_16.with_rd(reg.index)).with_immediate(imm),
                ),
                RegisterSize::Bit64 => {
                  if let Ok(i) = u32::try_from(i.bits()) {
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
                        .with_immediate(imm),
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

        rb_codegen::Opcode::Call(func) => {
          builder.call(func);
          builder.instr(Instruction::new(Opcode::CALL).with_immediate(Immediate::i32(0)))
        }

        // syscall
        rb_codegen::Opcode::Syscall => builder.instr(Instruction::new(Opcode::SYSCALL)),
      }
    }

    match block.terminator {
      rb_codegen::TerminatorInstruction::Jump(target) => {
        // Fallthrough
        if target == BlockId::new(id.as_u32() + 1) {
          continue;
        }

        builder.jmp(target, RegisterSize::Bit8);
        builder.instr(
          Instruction::new(Opcode::JMP).with_immediate(Immediate::i8(target.as_u32() as u8 + 3)),
        )
      }
      rb_codegen::TerminatorInstruction::Return(_) => builder.instr(Instruction::new(Opcode::RET)),
      rb_codegen::TerminatorInstruction::Trap => builder.instr(Instruction::new(Opcode::INT3)),
    }
  }

  builder.finish()
}

fn var_to_reg_size(v: VariableSize) -> Option<RegisterSize> {
  match v {
    VariableSize::Bit1 => None,
    VariableSize::Bit8 => Some(RegisterSize::Bit8),
    VariableSize::Bit16 => Some(RegisterSize::Bit16),
    VariableSize::Bit32 => Some(RegisterSize::Bit32),
    VariableSize::Bit64 => Some(RegisterSize::Bit64),
  }
}

impl From<rb_codegen::Immediate> for Immediate {
  fn from(value: rb_codegen::Immediate) -> Self {
    match value {
      rb_codegen::Immediate::I8(v) => Immediate::i8(v as u8),
      rb_codegen::Immediate::I16(v) => Immediate::i16(v as u16),
      rb_codegen::Immediate::I32(v) => Immediate::i32(v as u32),
      rb_codegen::Immediate::I64(v) => Immediate::i64(v as u64),
      rb_codegen::Immediate::U8(v) => Immediate::i8(v),
      rb_codegen::Immediate::U16(v) => Immediate::i16(v),
      rb_codegen::Immediate::U32(v) => Immediate::i32(v),
      rb_codegen::Immediate::U64(v) => Immediate::i64(v),
    }
  }
}

fn imm_to_i8(imm: rb_codegen::Immediate) -> Option<i8> { immediate!(imm, |v| i8::try_from(v).ok()) }

fn encode_binary_reg_imm(
  reg: Register,
  input2: rb_codegen::Immediate,
  opcode_8: Opcode,
  opcode_32: Opcode,
) -> Instruction {
  debug_assert_eq!(
    reg.size,
    var_to_reg_size(input2.size()).unwrap(),
    "binary must have the same size"
  );

  match input2 {
    rb_codegen::Immediate::I64(v) => {
      if let Ok(v) = i32::try_from(v) {
        return encode_sized(reg.size, opcode_8, opcode_32)
          .with_mod(0b11, reg.index)
          .with_immediate(Immediate::i32(v as u32));
      } else {
        panic!("immediate too large for binary operation");
      }
    }
    rb_codegen::Immediate::U64(v) => {
      if let Ok(v) = u32::try_from(v) {
        return encode_sized(reg.size, opcode_8, opcode_32)
          .with_mod(0b11, reg.index)
          .with_immediate(Immediate::i32(v));
      } else {
        panic!("immediate too large for binary operation");
      }
    }
    _ => {
      return encode_sized(reg.size, opcode_8, opcode_32)
        .with_mod(0b11, reg.index)
        .with_immediate(Immediate::from(input2));
    }
  }
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
      sig:          Signature { args: vec![], rets: vec![] },
      blocks:       vec![rb_codegen::Block {
        phis:         vec![],
        instructions: vec![
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![rb_codegen::Immediate::U8(3).into()],
            output: smallvec::smallvec![Variable::new(0, VariableSize::Bit8).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![rb_codegen::Immediate::U16(5).into()],
            output: smallvec::smallvec![Variable::new(1, VariableSize::Bit16).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![rb_codegen::Immediate::U32(7).into()],
            output: smallvec::smallvec![Variable::new(2, VariableSize::Bit32).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![rb_codegen::Immediate::U64(9).into()],
            output: smallvec::smallvec![Variable::new(3, VariableSize::Bit64).into()],
          },
          rb_codegen::Instruction {
            opcode: rb_codegen::Opcode::Move,
            input:  smallvec::smallvec![rb_codegen::Immediate::U64(u32::MAX as u64 + 5).into()],
            output: smallvec::smallvec![Variable::new(4, VariableSize::Bit64).into()],
          },
        ],
        terminator:   rb_codegen::TerminatorInstruction::Trap,
      }],
      data:         vec![],
      data_symbols: vec![],
    };

    let builder = lower(function);

    let dir = temp_dir!();
    let object_path = dir.path().join("foo.o");
    Object { text: builder.text, relocs: builder.relocs, ..Default::default() }.save(&object_path);
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
      sig:          Signature { args: vec![], rets: vec![] },
      blocks:       vec![rb_codegen::Block {
        phis:         vec![],
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
      data:         vec![],
      data_symbols: vec![],
    };

    let data = b"Hello, world!\n";
    let builder = lower(function);

    let dir = temp_dir!();
    let object_path = dir.path().join("foo.o");
    let binary_path = dir.path().join("a.out");
    Object {
      text: builder.text,
      ro_data: data.to_vec(),
      relocs: builder.relocs,
      ..Default::default()
    }
    .save(&object_path);
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
    Object {
      text,
      ro_data: data.to_vec(),
      relocs: vec![Rel {
        r_offset: 17,
        r_sym:    1,
        r_type:   object::elf::R_X86_64_PC32,
        r_addend: -4,
      }],
      ..Default::default()
    }
    .save(&dir.path().join("foo.o"));
  }

  #[test]
  fn call_works() {
    let mut text = vec![];

    let data = b"Hello, world!\n";

    let instructions = [
      // `call +16`
      Instruction::new(Opcode::CALL).with_immediate(Immediate::i32(16)),
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
      // `ret`
      Instruction::new(Opcode::RET),
    ];

    for inst in &instructions {
      let (bytes, len) = inst.encode();
      text.extend_from_slice(&bytes[..len]);
    }

    let dir = temp_dir!();
    Object { text, ..Default::default() }.save(&dir.path().join("foo.o"));
    disass(
      &dir.path().join("foo.o"),
      expect![@r#"
        0x08000250      e810000000             call 0x8000265
        0x08000255      48c7c03c000000         mov rax, 0x3c
        0x0800025c      48c7c700000000         mov rdi, 0
        0x08000263      0f05                   syscall
        0x08000265      48c7c001000000         mov rax, 1
        0x0800026c      48c7c701000000         mov rdi, 1
        0x08000273      488d35fcffffff         lea rsi, [0x08000276]
        0x0800027a      48c7c20e000000         mov rdx, 0xe
        0x08000281      0f05                   syscall
        0x08000283      c3                     ret
      "#],
    );
  }
}
