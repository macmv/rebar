use std::fmt;

use la_arena::Idx;
use rb_hir::ast::{self as hir, Path, Type};

use crate::Typer;

/// A type with variables in it. Internal to the typer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum VType {
  Error,
  SelfT,
  Primitive(hir::PrimitiveType),
  Ref(Box<VType>, hir::Mutability),

  Array(Box<VType>),
  Tuple(Vec<VType>),

  Function(Vec<VType>, Box<VType>),

  // TODO: Build unions sometimes.
  #[allow(dead_code)]
  Union(Vec<VType>),

  Integer(IntId),

  Struct(Path),
}

impl From<Type> for VType {
  fn from(ty: Type) -> Self {
    match ty {
      Type::SelfT => VType::SelfT,
      Type::Primitive(lit) => VType::Primitive(lit),
      Type::Ref(t, m) => VType::Ref(Box::new((*t).into()), m),
      Type::Array(ty) => VType::Array(Box::new((*ty).into())),
      Type::Tuple(types) => VType::Tuple(types.into_iter().map(Into::into).collect()),
      Type::Function(args, ret) => {
        VType::Function(args.into_iter().map(Into::into).collect(), Box::new((*ret).into()))
      }
      Type::Union(types) => VType::Union(types.into_iter().map(Into::into).collect()),
      Type::Struct(name) => VType::Struct(name),
    }
  }
}

impl From<hir::PrimitiveType> for VType {
  fn from(literal: hir::PrimitiveType) -> Self { VType::Primitive(literal) }
}

impl VType {
  pub fn unit() -> Self { VType::Tuple(vec![]) }

  pub fn is_integer(&self) -> bool {
    match self {
      VType::Integer(_) => true,
      VType::Primitive(prim) if prim.is_integer() => true,

      _ => false,
    }
  }
}

pub type IntId = Idx<IntVar>;

#[derive(Debug, Clone, PartialEq)]
pub struct IntVar {
  pub deps:     Vec<IntId>,
  pub concrete: Option<hir::PrimitiveType>,
}

impl Typer<'_> {
  pub(crate) fn display_type<'a>(&'a self, ty: &'a VType) -> VTypeDisplay<'a> {
    VTypeDisplay { typer: self, vtype: ty }
  }
}

pub(crate) struct VTypeDisplay<'a> {
  typer: &'a Typer<'a>,
  vtype: &'a VType,
}

impl fmt::Display for VTypeDisplay<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.vtype {
      VType::Error => write!(f, "unknown"),
      VType::SelfT => write!(f, "Self"),
      VType::Primitive(lit) => write!(f, "{lit}"),
      VType::Ref(ty, hir::Mutability::Imm) => write!(f, "&{}", self.typer.display_type(ty)),
      VType::Ref(ty, hir::Mutability::Mut) => write!(f, "&mut {}", self.typer.display_type(ty)),
      VType::Integer(_) => write!(f, "integer"),
      VType::Array(ty) => {
        write!(f, "array<")?;
        write!(f, "{}", self.typer.display_type(ty))?;
        write!(f, ">")
      }
      VType::Tuple(tys) => {
        write!(f, "(")?;
        for (i, ty) in tys.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", self.typer.display_type(ty))?;
        }
        write!(f, ")")
      }

      VType::Function(args, ret) => {
        write!(f, "fn(")?;
        for (i, ty) in args.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", self.typer.display_type(ty))?;
        }
        write!(f, ") -> {}", self.typer.display_type(ret))
      }

      VType::Union(tys) => {
        for (i, t) in tys.iter().enumerate() {
          if i != 0 {
            write!(f, " | ")?;
          }
          write!(f, "{}", self.typer.display_type(t))?;
        }
        Ok(())
      }

      VType::Struct(path) => write!(f, "{path}"),
    }
  }
}
