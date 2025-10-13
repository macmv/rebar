use std::{fs::File, io::BufWriter};

use object::{
  Endianness, elf,
  write::{
    StreamingBuffer,
    elf::{FileHeader, SectionHeader, Writer},
  },
};

fn foo() {
  let file = File::create("foo.o").unwrap();
  let mut buffer = StreamingBuffer::new(BufWriter::new(file));
  let mut writer = Writer::new(Endianness::Little, true, &mut buffer);

  let text = &[
    0x48, 0xc7, 0xc0, 0x3c, 0x00, 0x00, 0x00, // `mov eax, 60` (exit)
    0x48, 0xc7, 0xc7, 0x00, 0x00, 0x00, 0x00, // `mov rdi, 0` (status 0)
    0x0f, 0x05, // `syscall`
  ];

  writer.reserve_file_header();

  let text_name = writer.add_section_name(b".text");

  writer.reserve_null_section_index();
  writer.reserve_strtab_section_index();
  writer.reserve_shstrtab_section_index();
  writer.reserve_section_index();
  writer.reserve_section_headers();
  writer.reserve_strtab();
  writer.reserve_shstrtab();
  let text_offset = writer.reserve(text.len(), 4096);

  writer
    .write_file_header(&FileHeader {
      os_abi:      elf::ELFOSABI_NONE,
      abi_version: 0,
      e_type:      elf::ET_REL,
      e_machine:   elf::EM_X86_64,
      e_entry:     0,
      e_flags:     0,
    })
    .unwrap();

  writer.write_null_section_header();
  writer.write_strtab_section_header();
  writer.write_shstrtab_section_header();
  writer.write_section_header(&SectionHeader {
    name:         Some(text_name),
    sh_type:      elf::SHT_PROGBITS,
    sh_flags:     u64::from(elf::SHF_ALLOC | elf::SHF_EXECINSTR),
    sh_addr:      0x1000,
    sh_offset:    text_offset as u64,
    sh_size:      text.len() as u64,
    sh_link:      0,
    sh_info:      0,
    sh_addralign: 16,
    sh_entsize:   0,
  });

  writer.write_strtab();
  writer.write_shstrtab();
  writer.write_align(4096);
  writer.write(text);

  debug_assert_eq!(writer.reserved_len(), writer.len());
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn foo_works() { foo(); }
}
