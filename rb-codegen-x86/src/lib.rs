mod elf;
mod instruction;

pub use elf::generate;

pub use instruction::{Instruction, ModRm, Opcode, Rex};
