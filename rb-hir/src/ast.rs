use std::{collections::BTreeMap, fmt};

use la_arena::{Arena, Idx};

pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;
pub type FunctionId = Idx<Function>;
pub type StructId = Idx<Struct>;

#[derive(Debug, Default)]
pub struct Module {
  pub functions: Arena<Function>,
  pub structs:   Arena<Struct>,

  pub modules: BTreeMap<String, PartialModule>,

  // If there are any statements outside of functions, they will be stored in a "main function,"
  // stored here.
  pub main_function: Option<FunctionId>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Path {
  pub segments: Vec<String>,
}

#[derive(Debug)]
pub enum PartialModule {
  File,
  Inline(Module),
}

#[derive(Debug, Default)]
pub struct Function {
  pub name: String,

  pub attrs: Vec<Attribute>,
  pub args:  Vec<(String, TypeExpr)>,
  pub ret:   Option<TypeExpr>,

  pub exprs: Arena<Expr>,
  pub stmts: Arena<Stmt>,

  pub body: Option<Vec<StmtId>>,
}

#[derive(Debug)]
pub struct Attribute {
  pub path: String,
}

#[derive(Debug, Default)]
pub struct Struct {
  pub name: String,

  pub fields: Vec<(String, TypeExpr)>,
}

#[derive(Debug)]
pub enum Expr {
  Literal(Literal),
  Name(Path),

  String(Vec<StringInterp>),
  Array(Vec<ExprId>),

  Call(ExprId, Vec<ExprId>),
  UnaryOp(ExprId, UnaryOp),
  BinaryOp(ExprId, BinaryOp, ExprId),
  Index(ExprId, ExprId),
  StructInit(String, Vec<(String, ExprId)>),

  // TODO: Is this really needed?
  Paren(ExprId),
  Block(Vec<StmtId>),
  If { cond: ExprId, then: ExprId, els: Option<ExprId> },

  Assign { lhs: ExprId, rhs: ExprId },
}

#[derive(Clone, Debug)]
pub enum StringInterp {
  Literal(String),
  Expr(ExprId),
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
  Primitive(PrimitiveType),
  Struct(String),
  Tuple(Vec<TypeExpr>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
  Str,
  Bool,

  I8,
  I16,
  I32,
  I64,
  U8,
  U16,
  U32,
  U64,
}

#[derive(Debug)]
pub enum Stmt {
  Expr(ExprId),

  // TODO: Add type literals for explicit types.
  Let(String, ExprId),

  FunctionDef(FunctionDef),

  // TODO: Do we need this?
  Struct,
}

#[derive(Debug)]
pub struct FunctionDef {
  pub name: String,
  pub args: Vec<(String, TypeExpr)>,
  pub ret:  Option<TypeExpr>,
}

#[derive(Debug)]
pub enum Literal {
  Nil,
  Bool(bool),
  Int(i64),
}

#[derive(Debug)]
pub enum UnaryOp {
  Neg,
  Not,
}

#[derive(Debug)]
pub enum BinaryOp {
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  BitAnd,
  BitOr,
  Xor,
  ShiftLeft,
  ShiftRight,
  And,
  Or,
  Eq,
  Neq,
  Lt,
  Lte,
  Gt,
  Gte,
}

impl Path {
  pub const fn new() -> Self { Path { segments: vec![] } }

  pub fn as_single(&self) -> Option<&str> {
    match self.segments.as_slice() {
      [segment] => Some(segment),
      _ => None,
    }
  }

  pub fn push(&mut self, segment: String) { self.segments.push(segment); }

  pub fn join(&self, segment: String) -> Self {
    let mut new_path = self.clone();
    new_path.segments.push(segment);
    new_path
  }

  pub fn concat(&self, p: &Path) -> Self {
    let mut new_path = self.clone();
    new_path.segments.extend(p.segments.iter().cloned());
    new_path
  }
}

impl TypeExpr {
  pub fn unit() -> Self { TypeExpr::Tuple(vec![]) }
}

impl From<PrimitiveType> for TypeExpr {
  fn from(value: PrimitiveType) -> Self { TypeExpr::Primitive(value) }
}

pub struct ModuleIter<'a> {
  root:  &'a Module,
  stack: Vec<Path>,
}

impl Module {
  pub fn modules(&self) -> ModuleIter<'_> { ModuleIter { root: self, stack: vec![Path::new()] } }
}

impl<'a> Iterator for ModuleIter<'a> {
  type Item = (Path, &'a Module);

  fn next(&mut self) -> Option<Self::Item> {
    let path = self.stack.pop()?;
    let mut module = self.root;
    for segment in &path.segments {
      match module.modules.get(segment) {
        Some(PartialModule::Inline(submodule)) => {
          module = submodule;
        }
        _ => panic!(),
      }
    }

    for (name, partial) in &module.modules {
      if let PartialModule::Inline(_) = partial {
        let mut new_path = path.clone();
        new_path.segments.push(name.clone());
        self.stack.push(new_path);
      }
    }

    Some((path, module))
  }
}

impl fmt::Display for Path {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (i, segment) in self.segments.iter().enumerate() {
      if i != 0 {
        write!(f, "::")?;
      }
      write!(f, "{segment}")?;
    }
    Ok(())
  }
}
