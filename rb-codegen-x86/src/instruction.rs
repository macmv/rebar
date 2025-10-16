use bitflags::bitflags;

use crate::regalloc::RegisterSize;

pub struct Instruction {
  pub prefix:    Prefix,
  pub opcode:    Opcode,
  pub mod_reg:   Option<ModReg>,
  pub immediate: Immediate,
}

bitflags! {
  #[derive(Clone, Copy)]
  pub struct Prefix: u8 {
    const OperandSizeOverride = 0b01;
    const RexW                = 0b10;
  }
}

const _INSTR_SIZE: () = assert!(std::mem::size_of::<Instruction>() == 16);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum RegisterIndex {
  Eax,
  Ecx,
  Edx,
  Ebx,
  Esp,
  Ebp,
  Esi,
  Edi,
}

#[derive(Clone, Copy)]
pub struct Opcode {
  code: [u8; 3],
  len:  u8,
}

#[derive(Default, Clone, Copy)]
pub struct ModReg(u8);

#[derive(Clone, Copy)]
#[repr(packed)]
pub struct Immediate {
  len:   u8,
  value: u64,
}

impl From<u8> for Opcode {
  fn from(byte: u8) -> Self { Opcode::new([byte]) }
}
impl From<[u8; 2]> for Opcode {
  fn from(bytes: [u8; 2]) -> Self { Opcode::new(bytes) }
}
impl From<[u8; 3]> for Opcode {
  fn from(bytes: [u8; 3]) -> Self { Opcode::new(bytes) }
}

impl ModReg {
  pub const ZERO: ModReg = ModReg(0);

  pub const fn from_parts(mod_bits: u8, reg_bits: u8, rm_bits: u8) -> Self {
    debug_assert!(mod_bits < 4);
    debug_assert!(reg_bits < 8);
    debug_assert!(rm_bits < 8);

    ModReg((mod_bits << 6) | (reg_bits << 3) | rm_bits)
  }

  pub const fn set_reg(&mut self, reg: RegisterIndex) { self.set_reg_bits(reg as u8); }
  pub const fn set_reg_bits(&mut self, reg: u8) { self.0 = (self.0 & 0b11000111) | (reg << 3); }
  pub const fn set_mod_rm(&mut self, m: u8, rm: u8) {
    self.0 = (self.0 & 0b00111000) | ((m & 0b11) << 6) | (rm & 0b111);
  }

  pub const fn mod_bits(&self) -> u8 { (self.0 >> 6) & 0b11 }
  pub const fn reg_bits(&self) -> u8 { (self.0 >> 3) & 0b111 }
  pub const fn rm_bits(&self) -> u8 { self.0 & 0b111 }
}

impl Opcode {
  pub const fn new<const N: usize>(bytes: [u8; N]) -> Self {
    assert!(N >= 1 && N <= 3);
    let mut code = [0; 3];
    unsafe {
      *code.as_mut_ptr() = bytes[0];
      if N >= 2 {
        *code.as_mut_ptr().add(1) = bytes[1];
      }
      if N >= 3 {
        *code.as_mut_ptr().add(2) = bytes[2];
      }
    }
    Opcode { code, len: N as u8 }
  }

  pub fn bytes(&self) -> &[u8] { &self.code[..self.len as usize] }
}

impl Immediate {
  pub const fn empty() -> Self { Immediate { len: 0, value: 0 } }
  pub const fn i8(value: u8) -> Self { Immediate { len: 1, value: value as u64 } }
  pub const fn i16(value: u16) -> Self { Immediate { len: 2, value: value as u64 } }
  pub const fn i32(value: u32) -> Self { Immediate { len: 4, value: value as u64 } }
  pub const fn i64(value: u64) -> Self { Immediate { len: 8, value: value as u64 } }
  pub const fn for_size(value: u64, size: RegisterSize) -> Self {
    match size {
      RegisterSize::Bit8 => Immediate::i8(value as u8),
      RegisterSize::Bit16 => Immediate::i16(value as u16),
      RegisterSize::Bit32 => Immediate::i32(value as u32),
      RegisterSize::Bit64 => Immediate::i64(value as u64),
    }
  }

  pub const fn is_empty(&self) -> bool { self.len == 0 }
  pub const fn len(&self) -> u8 { self.len }
  pub const fn value(&self) -> u64 { self.value }
}

impl Instruction {
  pub const fn new(opcode: Opcode) -> Self {
    Instruction { prefix: Prefix::empty(), opcode, mod_reg: None, immediate: Immediate::empty() }
  }

  pub fn encode(&self) -> ([u8; 15], usize) {
    let mut buf = [0; 15];
    let mut len = 0;
    if self.prefix.contains(Prefix::OperandSizeOverride) {
      buf[len] = 0x66;
      len += 1;
    }
    if self.prefix.contains(Prefix::RexW) {
      buf[len] = 0x48;
      len += 1;
    }

    buf[len..len + self.opcode.len as usize]
      .copy_from_slice(&self.opcode.code[..self.opcode.len as usize]);
    len += self.opcode.len as usize;

    if let Some(ModReg(mod_rm)) = self.mod_reg {
      buf[len] = mod_rm;
      len += 1;
    }

    if !self.immediate.is_empty() {
      let imm_bytes = self.immediate.value().to_le_bytes();
      let imm_len = self.immediate.len() as usize;
      buf[len..len + imm_len].copy_from_slice(&imm_bytes[..imm_len]);
      len += imm_len;
    }

    (buf, len)
  }

  /// Adds a prefix.
  pub const fn with_prefix(mut self, prefix: Prefix) -> Self {
    self.prefix.0.0 |= prefix.0.0;
    self
  }

  /// Sets the `reg` field of the ModR/M byte.
  pub const fn with_reg(mut self, reg: RegisterIndex) -> Self {
    if self.mod_reg.is_none() {
      self.mod_reg = Some(ModReg::ZERO);
    }
    self.mod_reg.as_mut().unwrap().set_reg(reg);
    self
  }

  pub const fn with_digit(mut self, digit: u8) -> Self {
    if self.mod_reg.is_none() {
      self.mod_reg = Some(ModReg::ZERO);
    }
    self.mod_reg.as_mut().unwrap().set_reg_bits(digit);
    self
  }

  /// Sets the `mod` and `r/m` fields of the ModR/M byte.
  pub const fn with_mod(mut self, modifier: u8, rm: RegisterIndex) -> Self {
    if self.mod_reg.is_none() {
      self.mod_reg = Some(ModReg::ZERO);
    }
    self.mod_reg.as_mut().unwrap().set_mod_rm(modifier, rm as u8);
    self
  }

  /// Sets the ModR/M byte to assign to the given register with a constant
  /// displacement.
  pub const fn with_disp(self, reg: RegisterIndex, disp: i32) -> Self {
    self
      .with_mod_reg(ModReg::from_parts(0b00, reg as u8, 0b101))
      .with_immediate(Immediate::i32(disp as u32))
  }

  /// Sets the ModR/M byte.
  pub const fn with_mod_reg(mut self, mod_reg: ModReg) -> Self {
    self.mod_reg = Some(mod_reg);
    self
  }

  /// Sets the immediate value.
  pub const fn with_immediate(mut self, immediate: Immediate) -> Self {
    self.immediate = immediate;
    self
  }

  pub fn immediate(&self) -> Immediate { self.immediate }
}

impl Opcode {
  pub const ADD_IMM32: Opcode = Opcode::new([0x05]);
  pub const ADD_IMM8: Opcode = Opcode::new([0x04]);
  pub const ADD_RM32: Opcode = Opcode::new([0x03]);
  pub const ADD_RM8: Opcode = Opcode::new([0x02]);
  pub const SUB_IMM32: Opcode = Opcode::new([0x2d]);
  pub const SUB_IMM8: Opcode = Opcode::new([0x2c]);
  pub const SUB_RM32: Opcode = Opcode::new([0x2b]);
  pub const SUB_RM8: Opcode = Opcode::new([0x2a]);
  pub const INT3: Opcode = Opcode::new([0xcc]);
  pub const LEA: Opcode = Opcode::new([0x8d]);
  pub const MOV_RD_IMM_16: Opcode = Opcode::new([0xb8]);
  pub const MOV_RD_IMM_8: Opcode = Opcode::new([0xb0]);
  pub const MOV_RM_IMM_16: Opcode = Opcode::new([0xc7]);
  pub const MOV_RM_IMM_8: Opcode = Opcode::new([0xc6]);
  pub const MATH_EAX_RM32: Opcode = Opcode::new([0xf7]);
  pub const MATH_EAX_RM8: Opcode = Opcode::new([0xf6]);
  pub const SHIFT_IMM_8: Opcode = Opcode::new([0xc0]);
  pub const SHIFT_IMM_32: Opcode = Opcode::new([0xc1]);
  pub const SHIFT_C_8: Opcode = Opcode::new([0xd2]);
  pub const SHIFT_C_32: Opcode = Opcode::new([0xd3]);
  pub const SHIFT_1_8: Opcode = Opcode::new([0xd0]);
  pub const SHIFT_1_32: Opcode = Opcode::new([0xd1]);
  pub const RET: Opcode = Opcode::new([0xc3]);
  pub const SYSCALL: Opcode = Opcode::new([0x0f, 0x05]);
  pub const XOR_IMM32: Opcode = Opcode::new([0x35]);
  pub const XOR_IMM8: Opcode = Opcode::new([0x34]);
  pub const XOR_RM32: Opcode = Opcode::new([0x33]);
  pub const XOR_RM8: Opcode = Opcode::new([0x32]);

  pub fn with_rd(self, rd: RegisterIndex) -> Self {
    let mut code = self.code;
    code[0] |= rd as u8;
    Opcode { code, len: self.len }
  }
}
