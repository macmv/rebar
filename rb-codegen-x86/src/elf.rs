use std::{fs::File, io::BufWriter, path::Path};

use object::{
  Endianness, elf,
  write::{
    StreamingBuffer,
    elf::{FileHeader, SectionHeader, Sym, Writer},
  },
};

use crate::Object;

pub fn generate(filename: &Path, object: &Object) {
  let file = File::create(filename).unwrap();
  let mut buffer = StreamingBuffer::new(BufWriter::new(file));
  let mut writer = Writer::new(Endianness::Little, true, &mut buffer);

  writer.reserve_file_header();

  let start = writer.add_string(b"_start");
  let symbol_names = object
    .data_symbols
    .iter()
    .map(|s| (s, writer.add_string(s.name.as_bytes())))
    .collect::<Vec<_>>();
  let relocation_name = writer.add_section_name(b".rela.text");
  let text_name = writer.add_section_name(b".text");
  let ro_data_name = writer.add_section_name(b".rodata");

  writer.reserve_null_section_index();
  writer.reserve_strtab_section_index();
  writer.reserve_shstrtab_section_index();
  let symtab_section = writer.reserve_symtab_section_index();
  if !object.relocs.is_empty() {
    writer.reserve_section_index();
  }
  let text_section = writer.reserve_section_index();
  let ro_data_section = writer.reserve_section_index();

  writer.reserve_section_headers();

  writer.reserve_null_symbol_index();
  writer.reserve_symbol_index(Some(text_section));
  writer.reserve_symbol_index(Some(ro_data_section));

  writer.reserve_strtab();
  writer.reserve_shstrtab();
  writer.reserve_symtab();
  let relocations_offset = if object.relocs.is_empty() {
    None
  } else {
    Some(writer.reserve_relocations(object.relocs.len(), true))
  };
  let text_offset = writer.reserve(object.text.len(), 16);
  let ro_data_offset = writer.reserve(object.ro_data.len(), 1);

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

  let non_local_symbol_start = object.data_symbols.len() as u32 + 1;

  writer.write_null_section_header();
  writer.write_strtab_section_header();
  writer.write_shstrtab_section_header();
  writer.write_symtab_section_header(non_local_symbol_start);
  if let Some(relocations_offset) = relocations_offset {
    writer.write_relocation_section_header(
      relocation_name,
      text_section,
      symtab_section,
      relocations_offset,
      1,
      true,
    );
  }
  writer.write_section_header(&SectionHeader {
    name:         Some(text_name),
    sh_type:      elf::SHT_PROGBITS,
    sh_flags:     u64::from(elf::SHF_ALLOC | elf::SHF_EXECINSTR),
    sh_addr:      0,
    sh_offset:    text_offset as u64,
    sh_size:      object.text.len() as u64,
    sh_link:      0,
    sh_info:      0,
    sh_addralign: 16,
    sh_entsize:   0,
  });
  writer.write_section_header(&SectionHeader {
    name:         Some(ro_data_name),
    sh_type:      elf::SHT_PROGBITS,
    sh_flags:     u64::from(elf::SHF_ALLOC),
    sh_addr:      0x2000,
    sh_offset:    ro_data_offset as u64,
    sh_size:      object.ro_data.len() as u64,
    sh_link:      0,
    sh_info:      0,
    sh_addralign: 16,
    sh_entsize:   0,
  });

  writer.write_strtab();
  writer.write_shstrtab();

  // 2 local symbols
  writer.write_null_symbol();
  for (symbol, id) in symbol_names {
    writer.write_symbol(&Sym {
      name:     Some(id),
      section:  Some(ro_data_section),
      st_info:  ((elf::STB_LOCAL as u8) << 4) | (elf::STT_OBJECT as u8),
      st_other: 0,
      st_shndx: 0,
      st_value: symbol.offset as u64,
      st_size:  object.ro_data.len() as u64,
    });
  }

  // all non-local symbols must be defined after.
  writer.write_symbol(&Sym {
    name:     Some(start),
    section:  Some(text_section),
    st_info:  ((elf::STB_GLOBAL as u8) << 4) | (elf::STT_FUNC as u8),
    st_other: 0,
    st_shndx: 0,
    st_value: 0,
    st_size:  object.text.len() as u64,
  });

  for reloc in &object.relocs {
    writer.write_relocation(true, reloc);
  }
  writer.write_align(16);
  writer.write(&object.text);
  writer.write(&object.ro_data);

  debug_assert_eq!(writer.reserved_len(), writer.len());
}
