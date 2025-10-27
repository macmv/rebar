use std::fmt;

use crate::RegisterIndex;

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

    impl fmt::Display for Register {
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

impl fmt::Debug for Register {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Display::fmt(self, f) }
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
  R8B: "r8b", Bit8, R8;
  R9B: "r9b", Bit8, R9;
  R10B: "r10b", Bit8, R10;
  R11B: "r11b", Bit8, R11;
  R12B: "r12b", Bit8, R12;
  R13B: "r13b", Bit8, R13;
  R14B: "r14b", Bit8, R14;
  R15B: "r15b", Bit8, R15;

  AX: "ax", Bit16, Eax;
  CX: "cx", Bit16, Ecx;
  DX: "dx", Bit16, Edx;
  BX: "bx", Bit16, Ebx;
  SP: "sp", Bit16, Esp;
  BP: "bp", Bit16, Ebp;
  SI: "si", Bit16, Esi;
  DI: "di", Bit16, Edi;
  R8W: "r8w", Bit16, R8;
  R9W: "r9w", Bit16, R9;
  R10W: "r10w", Bit16, R10;
  R11W: "r11w", Bit16, R11;
  R12W: "r12w", Bit16, R12;
  R13W: "r13w", Bit16, R13;
  R14W: "r14w", Bit16, R14;
  R15W: "r15w", Bit16, R15;

  EAX: "eax", Bit32, Eax;
  ECX: "ecx", Bit32, Ecx;
  EDX: "edx", Bit32, Edx;
  EBX: "ebx", Bit32, Ebx;
  ESP: "esp", Bit32, Esp;
  EBP: "ebp", Bit32, Ebp;
  ESI: "esi", Bit32, Esi;
  EDI: "edi", Bit32, Edi;
  R8D: "r8d", Bit32, R8;
  R9D: "r9d", Bit32, R9;
  R10D: "r10d", Bit32, R10;
  R11D: "r11d", Bit32, R11;
  R12D: "r12d", Bit32, R12;
  R13D: "r13d", Bit32, R13;
  R14D: "r14d", Bit32, R14;
  R15D: "r15d", Bit32, R15;

  RAX: "rax", Bit64, Eax;
  RCX: "rcx", Bit64, Ecx;
  RDX: "rdx", Bit64, Edx;
  RBX: "rbx", Bit64, Ebx;
  RSP: "rsp", Bit64, Esp;
  RBP: "rbp", Bit64, Ebp;
  RSI: "rsi", Bit64, Esi;
  RDI: "rdi", Bit64, Edi;
  R8: "r8", Bit64, R8;
  R9: "r9", Bit64, R9;
  R10: "r10", Bit64, R10;
  R11: "r11", Bit64, R11;
  R12: "r12", Bit64, R12;
  R13: "r13", Bit64, R13;
  R14: "r14", Bit64, R14;
  R15: "r15", Bit64, R15;
}
