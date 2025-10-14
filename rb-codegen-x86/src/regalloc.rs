use rb_codegen::{InstructionInput, Variable};

use crate::instruction::RegisterIndex;

pub struct VariableRegisters {
  registers: Vec<Register>,
}

#[allow(unused)]
#[derive(Clone, Copy)]
pub enum Register {
  Rax,
  Rcx,
  Rdx,
  Rbx,
  Rsp,
  Rbp,
  Rsi,
  Rdi,

  Eax,
  Ecx,
  Edx,
  Ebx,
  Esp,
  Ebp,
  Esi,
  Edi,
}

pub enum CallingConvention {
  Syscall,
}

impl Register {
  pub fn size(&self) -> u8 {
    match self {
      Register::Rax
      | Register::Rcx
      | Register::Rdx
      | Register::Rbx
      | Register::Rsp
      | Register::Rbp
      | Register::Rsi
      | Register::Rdi => 8,
      Register::Eax
      | Register::Ecx
      | Register::Edx
      | Register::Ebx
      | Register::Esp
      | Register::Ebp
      | Register::Esi
      | Register::Edi => 4,
    }
  }

  pub fn index(&self) -> RegisterIndex {
    match self {
      Register::Rax | Register::Eax => RegisterIndex::Eax,
      Register::Rcx | Register::Ecx => RegisterIndex::Ecx,
      Register::Rdx | Register::Edx => RegisterIndex::Edx,
      Register::Rbx | Register::Ebx => RegisterIndex::Ebx,
      Register::Rsp | Register::Esp => RegisterIndex::Esp,
      Register::Rbp | Register::Ebp => RegisterIndex::Ebp,
      Register::Rsi | Register::Esi => RegisterIndex::Esi,
      Register::Rdi | Register::Edi => RegisterIndex::Edi,
    }
  }
}

impl VariableRegisters {
  pub fn new() -> Self { VariableRegisters { registers: vec![] } }

  pub fn pin_registers(&mut self, cc: CallingConvention, inputs: &[InstructionInput]) {
    let needed = inputs
      .iter()
      .filter_map(|input| match input {
        InstructionInput::Var(v) => Some(v.as_u32()),
        _ => None,
      })
      .max()
      .map_or(0, |v| v + 1) as usize;

    if self.registers.len() < needed {
      self.registers.resize(needed, Register::Rax);
    }

    match cc {
      CallingConvention::Syscall => {
        let mut arg_index = 0;
        for input in inputs {
          if let InstructionInput::Var(v) = input {
            let reg = match arg_index {
              0 => Register::Rax,
              1 => Register::Rdi,
              2 => Register::Rsi,
              3 => Register::Rdx,
              4 => Register::Rcx,
              _ => panic!("too many syscall arguments"),
            };
            self.set(*v, reg);
            arg_index += 1;
          }
        }
      }
    }
  }

  pub fn set(&mut self, var: Variable, reg: Register) {
    self.registers[var.as_u32() as usize] = reg;
  }

  pub fn get(&self, var: Variable) -> Register { self.registers[var.as_u32() as usize] }
}
