use std::fmt;

use rb_codegen::{Function, InstructionInput, InstructionOutput, Variable, VariableSize};

use crate::instruction::RegisterIndex;

pub struct VariableRegisters {
  registers: Vec<Register>,
}

struct Lifetimes {
  lifetimes: Vec<Option<Lifetime>>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Lifetime {
  def: InstructionLocation,

  first_use: InstructionLocation,
  last_use:  InstructionLocation,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InstructionLocation {
  pub block:       u32,
  pub instruction: u32,
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

  pub fn pass(&mut self, function: &Function) {
    let lifetimes = Lifetimes::solve(function);
    let mut used = [Option::<Variable>::None; 16];

    for (b, block) in function.blocks.iter().enumerate() {
      for (i, inst) in block.instructions.iter().enumerate() {
        let loc = InstructionLocation { block: b as u32, instruction: i as u32 };
        if let rb_codegen::Opcode::Syscall = inst.opcode {
          self.pin_registers(CallingConvention::Syscall, &inst.input);
          continue;
        }

        for output in &inst.output {
          if let InstructionOutput::Var(v) = *output {
            let size = match v.size() {
              VariableSize::Bit1 => continue,
              VariableSize::Bit8 => RegisterSize::Bit8,
              VariableSize::Bit16 => RegisterSize::Bit16,
              VariableSize::Bit32 => RegisterSize::Bit32,
              VariableSize::Bit64 => RegisterSize::Bit64,
            };

            for (index, used) in used.iter_mut().enumerate() {
              if used.is_none_or(|u| !lifetimes.is_used_at(u, loc)) {
                *used = Some(v);
                self.set(
                  v,
                  Register {
                    index: unsafe { std::mem::transmute::<u8, RegisterIndex>(index as u8) },
                    size,
                  },
                );
                break;
              }
            }
          }
        }
      }
    }
  }

  fn pin_registers(&mut self, cc: CallingConvention, inputs: &[InstructionInput]) {
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

  pub fn set(&mut self, var: Variable, reg: Register) {
    if var.id() as usize >= self.registers.len() {
      self.registers.resize(var.id() as usize + 1, Register::RAX);
    }
    self.registers[var.id() as usize] = reg;
  }

  pub fn get(&self, var: Variable) -> Register { self.registers[var.id() as usize] }
}

impl Lifetimes {
  fn solve(function: &Function) -> Self {
    let mut l = Lifetimes { lifetimes: vec![] };

    for (b, block) in function.blocks.iter().enumerate() {
      for (i, inst) in block.instructions.iter().enumerate() {
        let loc = InstructionLocation { block: b as u32, instruction: i as u32 };

        for input in &inst.input {
          if let InstructionInput::Var(v) = input {
            l.add_use(*v, loc);
          }
        }

        for output in &inst.output {
          if let InstructionOutput::Var(v) = output {
            l.add_def(*v, loc);
          }
        }
      }
    }

    l
  }

  fn is_used_at(&self, var: Variable, loc: InstructionLocation) -> bool {
    if let Some(l) = self.lifetimes[var.id() as usize] {
      l.first_use <= loc && loc < l.last_use
    } else {
      false
    }
  }

  fn add_use(&mut self, var: Variable, loc: InstructionLocation) {
    if self.lifetimes.len() <= var.id() as usize {
      self.lifetimes.resize(var.id() as usize + 1, None);
    }

    let prev = self.lifetimes[var.id() as usize];

    self.lifetimes[var.id() as usize] = Some(Lifetime {
      def:       prev.map_or(loc, |l| l.def),
      first_use: prev.map_or(loc, |l| l.first_use.min(loc)),
      last_use:  prev.map_or(loc, |l| l.last_use.max(loc)),
    });
  }

  fn add_def(&mut self, var: Variable, loc: InstructionLocation) {
    if self.lifetimes.len() <= var.id() as usize {
      self.lifetimes.resize(var.id() as usize + 1, None);
    }

    let prev = self.lifetimes[var.id() as usize];
    self.lifetimes[var.id() as usize] = Some(Lifetime {
      def:       loc,
      first_use: prev.map_or(loc, |l| l.first_use),
      last_use:  prev.map_or(loc, |l| l.last_use),
    });
  }
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
