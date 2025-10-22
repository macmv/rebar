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
