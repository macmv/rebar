use std::{collections::HashMap, fmt};

use la_arena::Idx;
use rb_hir::ast::{self as hir, Path};

use crate::Typer;

/// A rendered type. This is the result of typechecking.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  SelfT,
  Primitive(hir::PrimitiveType),
  Array(Box<Type>),
  Tuple(Vec<Type>),

  Function(Vec<Type>, Box<Type>),
  Union(Vec<Type>),

  Struct(Path),
}

impl Default for Type {
  fn default() -> Self { Type::unit() }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
  pub names:   HashMap<Path, Type>,
  pub structs: HashMap<Path, Vec<(String, Type)>>,

  // A map of structs to what traits they implement.
  pub impls:  HashMap<Path, Vec<Path>>,
  // A map of traits to their definitions.
  pub traits: HashMap<Path, TraitImpls>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitImpls {
  pub trait_def: TraitDef,
  pub impls:     Vec<Path>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDef {
  pub functions: HashMap<String, Type>,
}

/// A type with variables in it. Internal to the typer.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum VType {
  Error,
  SelfT,
  Primitive(hir::PrimitiveType),

  Array(Box<VType>),
  Tuple(Vec<VType>),

  Function(Vec<VType>, Box<VType>),

  // TODO: Build unions sometimes.
  #[allow(dead_code)]
  Union(Vec<VType>),

  Integer(IntId),

  Struct(Path),
}

impl Environment {
  pub fn empty() -> Self {
    Environment {
      names:   HashMap::new(),
      structs: HashMap::new(),
      impls:   HashMap::new(),
      traits:  HashMap::new(),
    }
  }

  pub fn mini() -> Self {
    let mut env = Environment::empty();

    env.add_impls(
      &Path::from(["std", "op", "Add"]),
      TraitImpls {
        trait_def: TraitDef {
          functions: HashMap::from([(
            "add".to_string(),
            Type::Function(vec![Type::SelfT, Type::SelfT], Box::new(Type::SelfT)),
          )]),
        },
        impls:     vec![
          Path::from(["i8"]),
          Path::from(["i16"]),
          Path::from(["i32"]),
          Path::from(["i64"]),
        ],
      },
    );

    env
  }

  pub fn add_impls(&mut self, for_trait: &Path, impls: TraitImpls) {
    for t in &impls.impls {
      self.impls.entry(t.clone()).or_default().push(for_trait.clone());
      for (f, sig) in &impls.trait_def.functions {
        self.names.insert(t.join(f.clone()), sig.clone());
      }
    }

    self.traits.insert(for_trait.clone(), impls);
  }

  pub fn struct_field(&self, ty: &Path, field: &str) -> Option<&Type> {
    self.structs.get(ty)?.iter().find_map(|(f, t)| (f == field).then_some(t))
  }

  pub fn impl_type(&self, ty: &Path, method: &str) -> Option<&Type> {
    self.impls.get(ty)?.iter().filter_map(|t| self.traits[t].trait_def.functions.get(method)).next()
  }

  pub fn function_type(&self, path: &Path) -> Option<&Type> { self.names.get(path) }
}

impl Type {
  pub const fn unit() -> Self { Type::Tuple(vec![]) }

  pub(crate) fn resolve_self(&self, slf: &VType) -> VType {
    match self {
      Type::SelfT => slf.clone(),
      Type::Primitive(p) => VType::Primitive(*p),
      Type::Array(ty) => VType::Array(Box::new(ty.resolve_self(slf))),
      Type::Tuple(types) => VType::Tuple(types.iter().map(|ty| ty.resolve_self(slf)).collect()),
      Type::Function(args, ret) => VType::Function(
        args.iter().map(|ty| ty.resolve_self(slf)).collect(),
        Box::new(ret.resolve_self(slf)),
      ),
      Type::Union(types) => VType::Union(types.iter().map(|ty| ty.resolve_self(slf)).collect()),
      Type::Struct(name) => VType::Struct(name.clone()),
    }
  }
}

impl From<Type> for VType {
  fn from(ty: Type) -> Self {
    match ty {
      Type::SelfT => VType::SelfT,
      Type::Primitive(lit) => VType::Primitive(lit),
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

impl From<hir::PrimitiveType> for Type {
  fn from(literal: hir::PrimitiveType) -> Self { Type::Primitive(literal) }
}
impl From<hir::PrimitiveType> for VType {
  fn from(literal: hir::PrimitiveType) -> Self { VType::Primitive(literal) }
}

impl VType {
  pub fn unit() -> Self { VType::Tuple(vec![]) }

  pub fn is_integer(&self) -> bool {
    match self {
      VType::Integer(_) => true,

      VType::Primitive(hir::PrimitiveType::I8) => true,
      VType::Primitive(hir::PrimitiveType::I16) => true,
      VType::Primitive(hir::PrimitiveType::I32) => true,
      VType::Primitive(hir::PrimitiveType::I64) => true,
      VType::Primitive(hir::PrimitiveType::U8) => true,
      VType::Primitive(hir::PrimitiveType::U16) => true,
      VType::Primitive(hir::PrimitiveType::U32) => true,
      VType::Primitive(hir::PrimitiveType::U64) => true,

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

impl fmt::Display for Type {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Type::SelfT => write!(f, "Self"),
      Type::Primitive(p) => write!(f, "{p}"),
      Type::Array(ty) => write!(f, "Array[{}]", ty),
      Type::Tuple(types) => {
        let types: Vec<String> = types.iter().map(|ty| format!("{}", ty)).collect();
        write!(f, "({})", types.join(", "))
      }
      Type::Function(args, ret) => {
        let args: Vec<String> = args.iter().map(|ty| format!("{}", ty)).collect();
        write!(f, "fn({}) -> {}", args.join(", "), ret)
      }
      Type::Union(types) => {
        let types: Vec<String> = types.iter().map(|ty| format!("{}", ty)).collect();
        write!(f, "{}", types.join(" | "))
      }
      Type::Struct(name) => write!(f, "Struct {}", name),
    }
  }
}

impl fmt::Display for VTypeDisplay<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.vtype {
      VType::Error => write!(f, "unknown"),
      VType::SelfT => write!(f, "Self"),
      VType::Primitive(lit) => write!(f, "{lit}"),
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
