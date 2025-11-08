pub mod ast;

use std::{collections::HashMap, ops::Index};

use ast::{ExprId, FunctionId, StmtId};
use rb_diagnostic::Span;

use crate::ast::{FullyQualifiedName, Path, Type};

#[derive(Default)]
pub struct SpanMap {
  pub modules: HashMap<Path, ModuleSpanMap>,
}
impl SpanMap {
  pub fn append(&mut self, p: &Path, span_map: SpanMap) {
    for (module_path, module_span_map) in span_map.modules {
      let full_path = p.concat(&module_path);
      self.modules.insert(full_path, module_span_map);
    }
  }
}

#[derive(Default)]
pub struct ModuleSpanMap {
  pub functions: HashMap<FunctionId, FunctionSpanMap>,
}

#[derive(Default)]
pub struct FunctionSpanMap {
  pub name_span: Option<Span>,

  pub exprs: Vec<Span>,
  pub stmts: Vec<Span>,

  pub let_stmts: HashMap<StmtId, Span>,

  pub binary_ops: HashMap<ExprId, Span>,
  pub unary_ops:  HashMap<ExprId, Span>,
  pub if_exprs:   HashMap<ExprId, (Span, Option<Span>)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Environment {
  pub names:   HashMap<FullyQualifiedName, Type>,
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

impl Index<ExprId> for FunctionSpanMap {
  type Output = Span;

  fn index(&self, index: ExprId) -> &Self::Output {
    &self.exprs[index.into_raw().into_u32() as usize]
  }
}

impl Index<StmtId> for FunctionSpanMap {
  type Output = Span;

  fn index(&self, index: StmtId) -> &Self::Output {
    &self.stmts[index.into_raw().into_u32() as usize]
  }
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

    env.names.insert(
      FullyQualifiedName::new_single("panic".to_string()),
      Type::Function(vec![], Box::new(Type::Primitive(ast::PrimitiveType::Never))),
    );

    env
  }

  pub fn add_impls(&mut self, for_trait: &Path, impls: TraitImpls) {
    for t in &impls.impls {
      self.impls.entry(t.clone()).or_default().push(for_trait.clone());
      for (f, sig) in &impls.trait_def.functions {
        let sig = sig.resolve_self(&Type::from_path(t));
        self.names.insert(
          FullyQualifiedName::TraitImpl {
            trait_path:  for_trait.clone(),
            struct_path: t.clone(),
            name:        f.clone(),
          },
          sig,
        );
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

  pub fn lookup_type(&self, path: &FullyQualifiedName) -> Option<&Type> { self.names.get(path) }

  // Resolve a call like `i32::add` to `<i32 as std::op::Add>::add`
  pub fn resolve_trait_call(&self, p: &Path) -> Option<FullyQualifiedName> {
    let mut path = p.clone();
    let name = path.segments.pop()?;
    let ty = self.impls.get(&path)?;
    // TODO: how do use statements/priorities work here??
    let trait_path = ty
      .iter()
      .find(|t| self.traits.get(*t).is_some_and(|t| t.trait_def.functions.contains_key(&name)))?;

    Some(FullyQualifiedName::new_trait_impl(trait_path.clone(), path, name))
  }
}
