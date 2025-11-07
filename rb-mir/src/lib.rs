use std::{collections::HashMap, num::NonZero};

use ast::StructId;
use rb_hir::{
  ast as hir,
  ast::{FullyQualifiedName, Path, Type},
};

pub mod ast;

// Global context needed in the JIT, that is produced by `rb-mir-lower`.
#[derive(Default, Clone)]
pub struct MirContext {
  pub struct_paths: HashMap<Path, StructId>,
  pub structs:      HashMap<StructId, Struct>,
  pub items:        HashMap<FullyQualifiedName, UserFunction>,
}

#[derive(Clone)]
pub struct UserFunction {
  pub id:   ast::FunctionId,
  pub kind: FunctionKind,
}

#[derive(Clone)]
pub enum FunctionKind {
  UserDefined,
  Intrinsic(ast::Intrinsic),
  Extern(String),
}

#[derive(Debug, Clone)]
pub struct Struct {
  pub fields: Vec<(String, Type)>,
}

#[derive(Debug)]
pub struct Layout {
  pub size:  u32,
  pub align: NonZero<u32>,
}

#[derive(Debug)]
pub struct StructLayout {
  pub layout:  Layout,
  pub offsets: Vec<u32>,
}

impl Layout {
  #[track_caller]
  pub fn new(size: u32, align: u32) -> Self {
    Self { size, align: NonZero::new(align).expect("non-zero align") }
  }
}

impl MirContext {
  pub fn layout_type(&self, ty: &Type) -> Layout {
    use hir::PrimitiveType::*;

    match ty {
      Type::SelfT => panic!("self type should be resolved"),

      Type::Primitive(Bool) => Layout::new(1, 1),
      Type::Primitive(I8 | U8) => Layout::new(1, 1),
      Type::Primitive(I16 | U16) => Layout::new(2, 2),
      Type::Primitive(I32 | U32) => Layout::new(4, 4),
      Type::Primitive(I64 | U64) => Layout::new(8, 8),
      Type::Primitive(Str) => Layout::new(16, 8),
      Type::Primitive(Never) => Layout::new(0, 1),

      Type::Ref(_, _) | Type::Function(_, _) => Layout::new(8, 8),

      Type::Struct(s) => self.layout_struct(self.struct_paths[&s]).layout,
      Type::Tuple(_) => todo!(),

      Type::Array(_) => todo!("arrays"),
      Type::Union(_) => todo!("unions"),
    }
  }

  pub fn layout_struct(&self, struct_id: StructId) -> StructLayout {
    let s = &self.structs[&struct_id];

    let mut fields =
      s.fields.iter().enumerate().map(|(i, (_, ty))| (i, self.layout_type(ty))).collect::<Vec<_>>();
    fields.sort_by_key(|(_, l)| l.align.get());

    let mut offsets = vec![0; fields.len()];
    let mut offset: u32 = 0;
    let mut struct_align = 1;

    for (index, field) in &fields {
      let align = field.align.get();
      struct_align = struct_align.max(align);

      if offset % align != 0 {
        offset += align - (offset % align);
      }

      offsets[*index] = offset;
      offset += field.size;
    }

    if offset % struct_align != 0 {
      offset += struct_align - (offset % struct_align);
    }

    StructLayout { layout: Layout::new(offset, struct_align), offsets }
  }
}
