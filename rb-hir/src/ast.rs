use std::{collections::BTreeMap, fmt};

use la_arena::{Arena, Idx};

pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;
pub type LocalId = Idx<Local>;
pub type FunctionId = Idx<Function>;
pub type StructId = Idx<Struct>;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialModule {
  File,
  Inline(Module),
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Function {
  pub name: String,

  pub attrs: Vec<Attribute>,
  pub sig:   Signature,

  pub exprs:  Arena<Expr>,
  pub stmts:  Arena<Stmt>,
  // Filled in by HIR resolution.
  pub locals: Arena<Local>,

  pub body: Option<Vec<StmtId>>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Signature {
  pub args: Vec<(String, TypeExpr)>,
  pub ret:  TypeExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
  pub path: String,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Struct {
  pub name: String,

  pub fields: Vec<(String, TypeExpr)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
  Literal(Literal),
  Local(LocalId),
  Name(Path),

  String(Vec<StringInterp>),
  Array(Vec<ExprId>),

  Call(ExprId, Vec<ExprId>),
  UnaryOp(ExprId, UnaryOp),
  BinaryOp(ExprId, BinaryOp, ExprId),
  Index(ExprId, ExprId),
  Field(ExprId, String),
  StructInit(Path, Vec<(String, ExprId)>),

  // TODO: Is this really needed?
  Paren(ExprId),
  Block(Vec<StmtId>),
  If { cond: ExprId, then: ExprId, els: Option<ExprId> },

  Assign { lhs: ExprId, rhs: ExprId },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Local {
  pub name: String,
  pub ty:   Option<TypeExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StringInterp {
  Literal(String),
  Expr(ExprId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeExpr {
  Primitive(PrimitiveType),
  Struct(Path),
  Tuple(Vec<TypeExpr>),
}

impl Default for TypeExpr {
  fn default() -> Self { TypeExpr::unit() }
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

  Never,
}

/// A rendered type. This is the result of typechecking. It is only produced by
/// `rb-typer`, not from parsing.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
  SelfT,
  Primitive(PrimitiveType),
  Array(Box<Type>),
  Tuple(Vec<Type>),

  Function(Vec<Type>, Box<Type>),
  Union(Vec<Type>),

  Struct(Path),
}

impl Default for Type {
  fn default() -> Self { Type::unit() }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
  Expr(ExprId),

  Let(String, Option<LocalId>, Option<TypeExpr>, ExprId),

  FunctionDef(FunctionDef),

  // TODO: Do we need this?
  Struct,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDef {
  pub name: String,
  pub args: Vec<(String, TypeExpr)>,
  pub ret:  Option<TypeExpr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Literal {
  Nil,
  Bool(bool),
  Int(i64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
  Neg,
  Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

impl<const N: usize> From<[&str; N]> for Path {
  fn from(value: [&str; N]) -> Self {
    Path { segments: value.iter().map(|s| s.to_string()).collect() }
  }
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
  pub const fn unit() -> Self { TypeExpr::Tuple(vec![]) }
}

impl Type {
  pub const fn unit() -> Self { Type::Tuple(vec![]) }
}

impl From<PrimitiveType> for TypeExpr {
  fn from(value: PrimitiveType) -> Self { TypeExpr::Primitive(value) }
}

impl From<PrimitiveType> for Type {
  fn from(literal: PrimitiveType) -> Self { Type::Primitive(literal) }
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

impl fmt::Display for PrimitiveType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      PrimitiveType::Str => write!(f, "str"),
      PrimitiveType::Bool => write!(f, "bool"),

      PrimitiveType::I8 => write!(f, "i8"),
      PrimitiveType::I16 => write!(f, "i16"),
      PrimitiveType::I32 => write!(f, "i32"),
      PrimitiveType::I64 => write!(f, "i64"),
      PrimitiveType::U8 => write!(f, "u8"),
      PrimitiveType::U16 => write!(f, "u16"),
      PrimitiveType::U32 => write!(f, "u32"),
      PrimitiveType::U64 => write!(f, "u64"),

      PrimitiveType::Never => write!(f, "!"),
    }
  }
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
