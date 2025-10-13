use std::{fs::File, io::BufWriter};

use object::{
  Endianness, elf,
  write::{
    StreamingBuffer,
    elf::{FileHeader, SectionHeader, Sym, Writer},
  },
};

pub fn generate(filename: &str, text: &[u8]) {
  let file = File::create(filename).unwrap();
  let mut buffer = StreamingBuffer::new(BufWriter::new(file));
  let mut writer = Writer::new(Endianness::Little, true, &mut buffer);

  writer.reserve_file_header();

  let start = writer.add_string(b"_start");
  let text_name = writer.add_section_name(b".text");

  writer.reserve_null_section_index();
  writer.reserve_strtab_section_index();
  writer.reserve_shstrtab_section_index();
  writer.reserve_symtab_section_index();
  let text_section = writer.reserve_section_index();

  writer.reserve_null_symbol_index();
  writer.reserve_symbol_index(Some(text_section));

  writer.reserve_section_headers();

  writer.reserve_strtab();
  writer.reserve_shstrtab();
  writer.reserve_symtab();
  let text_offset = writer.reserve(text.len(), 16);

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
  writer.write_symtab_section_header(1);
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
  writer.write_null_symbol();
  writer.write_symbol(&Sym {
    name:     Some(start),
    section:  Some(text_section),
    st_info:  ((elf::STB_GLOBAL as u8) << 4) | (elf::STT_FUNC as u8),
    st_other: 0,
    st_shndx: 0,
    st_value: 0,
    st_size:  text.len() as u64,
  });
  writer.write_align(16);
  writer.write(text);

  debug_assert_eq!(writer.reserved_len(), writer.len());
}
