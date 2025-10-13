mod elf;
mod instruction;

pub use elf::generate;

pub use instruction::{Instruction, ModRm, Opcode, Rex};

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn foo_works() {
    let mut text = vec![];

    let instructions = [
      Instruction::new(Opcode::MOV_RAX_IMM)
        .with_rex(Rex::W)
        .with_mod_rm(ModRm::from_parts(0b11, 0, 0))
        .with_immediate(60),
      Instruction::new(Opcode::MOV_RDI_IMM)
        .with_rex(Rex::W)
        .with_mod_rm(ModRm::from_parts(0b11, 0, 7))
        .with_immediate(0),
      Instruction::new(Opcode::SYSCALL),
    ];

    for inst in &instructions {
      let (bytes, len) = inst.encode();
      text.extend_from_slice(&bytes[..len]);
    }

    assert_eq!(
      text,
      &[
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00, // `mov eax, 60` (exit)
        0x48, 0xc7, 0xc7, 0x00, 0x00, 0x00, 0x00, // `mov rdi, 0` (status 0)
        0x0f, 0x05, // `syscall`
      ]
    );

    elf::generate(
      "foo.o",
      &[
        0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00, // `mov eax, 60` (exit)
        0x48, 0xc7, 0xc7, 0x00, 0x00, 0x00, 0x00, // `mov rdi, 0` (status 0)
        0x0f, 0x05, // `syscall`
      ],
    );
  }
}
