use std::fmt;

use rb_codegen::{InstructionInput, InstructionOutput, Variable, VariableSize};

use crate::instruction::RegisterIndex;

pub struct VariableRegisters {
  registers: Vec<Register>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Register {
  pub size:  RegisterSize,
  pub index: RegisterIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegisterSize {
  Bit8,
  Bit16,
  Bit32,
  Bit64,
}

pub enum CallingConvention {
  Syscall,
}

impl VariableRegisters {
  pub fn new() -> Self { VariableRegisters { registers: vec![] } }

  pub fn pin_registers(&mut self, cc: CallingConvention, inputs: &[InstructionInput]) {
    let needed = inputs
      .iter()
      .filter_map(|input| match input {
        InstructionInput::Var(v) => Some(v.id()),
        _ => None,
      })
      .max()
      .map_or(0, |v| v + 1) as usize;

    if self.registers.len() < needed {
      self.registers.resize(needed, Register::RAX);
    }

    match cc {
      CallingConvention::Syscall => {
        let mut arg_index = 0;
        for input in inputs {
          if let InstructionInput::Var(v) = input {
            let reg = match arg_index {
              0 => Register::RAX,
              1 => Register::RDI,
              2 => Register::RSI,
              3 => Register::RDX,
              4 => Register::RCX,
              _ => panic!("too many syscall arguments"),
            };
            self.set(*v, reg);
            arg_index += 1;
          }
        }
      }
    }
  }

  pub fn pick_inputs(&mut self, inputs: &[InstructionInput]) {
    for input in inputs {
      if let InstructionInput::Var(v) = input {
        if v.id() as usize >= self.registers.len() {
          self.registers.resize(v.id() as usize + 1, Register::RAX);
        }
        self.set(*v, Register::RAX);
      }
    }
  }

  pub fn pick_outputs(&mut self, outputs: &[InstructionOutput]) {
    for output in outputs {
      if let InstructionOutput::Var(v) = output {
        let size = match v.size() {
          VariableSize::Bit1 => continue,
          VariableSize::Bit8 => RegisterSize::Bit8,
          VariableSize::Bit16 => RegisterSize::Bit16,
          VariableSize::Bit32 => RegisterSize::Bit32,
          VariableSize::Bit64 => RegisterSize::Bit64,
        };

        if v.id() as usize >= self.registers.len() {
          self.registers.resize(v.id() as usize + 1, Register::RAX);
        }

        self.set(*v, Register::RAX.with_size(size));
      }
    }
  }

  pub fn set(&mut self, var: Variable, reg: Register) { self.registers[var.id() as usize] = reg; }

  pub fn get(&self, var: Variable) -> Register { self.registers[var.id() as usize] }
}

impl Register {
  pub fn with_size(self, size: RegisterSize) -> Self { Register { size, index: self.index } }
}

macro_rules! registers {
  (
    $(
      $const:ident: $str:expr, $size:ident, $index:ident;
    )*
  ) => {
    #[allow(unused)]
    impl Register {
      $(
        pub const $const: Register = Register { size: RegisterSize::$size, index: RegisterIndex::$index };
      )*
    }

    impl fmt::Debug for Register {
      fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.size, self.index) {
          $(
            (RegisterSize::$size, RegisterIndex::$index) => write!(f, $str),
          )*
        }
      }
    }
  };
}

registers! {
  AL: "al", Bit8, Eax;
  CL: "cl", Bit8, Ecx;
  DL: "dl", Bit8, Edx;
  BL: "bl", Bit8, Ebx;
  SPL: "spl", Bit8, Esp;
  BPL: "bpl", Bit8, Ebp;
  SIL: "sil", Bit8, Esi;
  DIL: "dil", Bit8, Edi;

  AX: "ax", Bit16, Eax;
  CX: "cx", Bit16, Ecx;
  DX: "dx", Bit16, Edx;
  BX: "bx", Bit16, Ebx;
  SP: "sp", Bit16, Esp;
  BP: "bp", Bit16, Ebp;
  SI: "si", Bit16, Esi;
  DI: "di", Bit16, Edi;

  EAX: "eax", Bit32, Eax;
  ECX: "ecx", Bit32, Ecx;
  EDX: "edx", Bit32, Edx;
  EBX: "ebx", Bit32, Ebx;
  ESP: "esp", Bit32, Esp;
  EBP: "ebp", Bit32, Ebp;
  ESI: "esi", Bit32, Esi;
  EDI: "edi", Bit32, Edi;

  RAX: "rax", Bit64, Eax;
  RCX: "rcx", Bit64, Ecx;
  RDX: "rdx", Bit64, Edx;
  RBX: "rbx", Bit64, Ebx;
  RSP: "rsp", Bit64, Esp;
  RBP: "rbp", Bit64, Ebp;
  RSI: "rsi", Bit64, Esi;
  RDI: "rdi", Bit64, Edi;
}
