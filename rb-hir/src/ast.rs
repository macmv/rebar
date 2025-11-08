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
  pub uses:      Arena<Use>,

  pub standalone_functions: Vec<FunctionId>,
  pub impls:                Vec<Impl>,

  pub modules: BTreeMap<String, PartialModule>,

  // If there are any statements outside of functions, they will be stored in a "main function,"
  // stored here.
  pub main_function: Option<FunctionId>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Use {
  pub path:    Path,
  pub alias:   Option<String>,
  pub is_glob: bool,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Path {
  pub segments: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FullyQualifiedName {
  Bare { path: Path, name: String },
  TraitImpl { trait_path: Path, struct_path: Path, name: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PartialModule {
  File,
  Inline(Module),
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Function {
  pub name: String,

  pub ext:   Option<String>,
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

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct Impl {
  pub struct_path: TypeExpr,
  pub trait_path:  Option<Path>,
  pub functions:   Vec<FunctionId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
  Literal(Literal),
  Local(LocalId),
  Name(FullyQualifiedName),

  String(Vec<StringInterp>),
  Array(Vec<ExprId>),

  Call(ExprId, Vec<ExprId>),
  UnaryOp(ExprId, UnaryOp),
  BinaryOp(ExprId, BinaryOp, ExprId),
  Index(ExprId, ExprId),
  Field(ExprId, String),
  StructInit(Path, Vec<(String, ExprId)>),
  Cast(ExprId, TypeExpr),

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
  Ref(Box<TypeExpr>, Mutability),
  Struct(Path),
  Tuple(Vec<TypeExpr>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mutability {
  Mut,
  Imm,
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
  Ref(Box<Type>, Mutability),
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

  FunctionDef(FunctionId, FunctionDef),

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
  Bool(bool),
  Int(i64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
  Neg,
  Not,
  Ref,
  Deref,
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

  pub fn concat_slice(&self, segments: &[String]) -> Path {
    let mut new_path = self.clone();
    new_path.segments.extend_from_slice(segments);
    new_path
  }
}

impl FullyQualifiedName {
  pub fn new_single(name: String) -> Self { FullyQualifiedName::Bare { path: Path::new(), name } }

  pub fn new_bare(mut path: Path) -> Option<Self> {
    let name = path.segments.pop()?;

    Some(FullyQualifiedName::Bare { path, name })
  }

  pub fn new_trait_impl(trait_path: Path, struct_path: Path, name: String) -> Self {
    FullyQualifiedName::TraitImpl { trait_path, struct_path, name }
  }

  pub fn as_single(&self) -> Option<&str> {
    match self {
      FullyQualifiedName::Bare { path, name } if path.segments.is_empty() => Some(name),
      _ => None,
    }
  }

  pub fn to_path(&self) -> Option<Path> {
    match self {
      FullyQualifiedName::Bare { path, name } => Some(path.join(name.clone())),
      _ => None,
    }
  }
}

impl TypeExpr {
  pub const fn unit() -> Self { TypeExpr::Tuple(vec![]) }
}

impl Type {
  pub const fn unit() -> Self { Type::Tuple(vec![]) }

  // TODO: This is a terrible hack. Not sure where to put it.
  pub fn from_path(path: &Path) -> Self {
    match path.as_single() {
      Some("Self") => Type::SelfT,
      Some("str") => Type::Primitive(PrimitiveType::Str),
      Some("bool") => Type::Primitive(PrimitiveType::Bool),
      Some("i8") => Type::Primitive(PrimitiveType::I8),
      Some("i16") => Type::Primitive(PrimitiveType::I16),
      Some("i32") => Type::Primitive(PrimitiveType::I32),
      Some("i64") => Type::Primitive(PrimitiveType::I64),
      Some("u8") => Type::Primitive(PrimitiveType::U8),
      Some("u16") => Type::Primitive(PrimitiveType::U16),
      Some("u32") => Type::Primitive(PrimitiveType::U32),
      Some("u64") => Type::Primitive(PrimitiveType::U64),

      _ => Type::Struct(path.clone()),
    }
  }

  pub fn resolve_self(self: &Type, slf: &Type) -> Type {
    match self {
      Type::SelfT => slf.clone(),
      Type::Primitive(p) => Type::Primitive(*p),
      Type::Ref(t, m) => Type::Ref(Box::new(t.resolve_self(slf)), *m),
      Type::Array(ty) => Type::Array(Box::new(ty.resolve_self(slf))),
      Type::Tuple(types) => Type::Tuple(types.iter().map(|ty| ty.resolve_self(slf)).collect()),
      Type::Function(args, ret) => Type::Function(
        args.iter().map(|ty| ty.resolve_self(slf)).collect(),
        Box::new(ret.resolve_self(slf)),
      ),
      Type::Union(types) => Type::Union(types.iter().map(|ty| ty.resolve_self(slf)).collect()),
      Type::Struct(name) => Type::Struct(name.clone()),
    }
  }
}

impl From<PrimitiveType> for TypeExpr {
  fn from(value: PrimitiveType) -> Self { TypeExpr::Primitive(value) }
}

impl From<PrimitiveType> for Type {
  fn from(literal: PrimitiveType) -> Self { Type::Primitive(literal) }
}

impl PrimitiveType {
  pub fn is_integer(&self) -> bool {
    matches!(
      self,
      PrimitiveType::I8
        | PrimitiveType::I16
        | PrimitiveType::I32
        | PrimitiveType::I64
        | PrimitiveType::U8
        | PrimitiveType::U16
        | PrimitiveType::U32
        | PrimitiveType::U64
    )
  }
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

struct DisplayStmt<'a> {
  func: &'a Function,
  stmt: StmtId,
}
struct DisplayExpr<'a> {
  func: &'a Function,
  expr: ExprId,
}

impl Function {
  fn display_stmt(&self, stmt: StmtId) -> DisplayStmt<'_> { DisplayStmt { func: self, stmt } }
  fn display_expr(&self, expr: ExprId) -> DisplayExpr<'_> { DisplayExpr { func: self, expr } }
}

impl fmt::Display for Function {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "fn {}(", self.name)?;
    for (i, (arg_name, arg_type)) in self.sig.args.iter().enumerate() {
      if i != 0 {
        write!(f, ", ")?;
      }
      write!(f, "{}: {}", arg_name, arg_type)?;
    }
    write!(f, ")")?;
    if self.sig.ret != TypeExpr::unit() {
      write!(f, " -> {}", self.sig.ret)?;
    }
    if let Some(body) = &self.body {
      write!(f, " {{")?;
      for item in body {
        write!(f, "\n  {}", self.display_stmt(*item))?;
      }
      write!(f, "\n}}")?;
    }
    Ok(())
  }
}

impl fmt::Display for TypeExpr {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      TypeExpr::Primitive(p) => write!(f, "{p}"),
      TypeExpr::Ref(t, Mutability::Imm) => write!(f, "&{t}"),
      TypeExpr::Ref(t, Mutability::Mut) => write!(f, "&mut {t}"),
      TypeExpr::Struct(name) => write!(f, "{name}"),
      TypeExpr::Tuple(types) => {
        let types: Vec<String> = types.iter().map(|ty| format!("{}", ty)).collect();
        write!(f, "({})", types.join(", "))
      }
    }
  }
}

impl fmt::Display for DisplayStmt<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let stmt = &self.func.stmts[self.stmt];
    match stmt {
      Stmt::Expr(expr) => write!(f, "{}", self.func.display_expr(*expr)),
      Stmt::Let(name, _, ty, expr) => {
        write!(f, "let {}", name)?;
        if let Some(ty) = ty {
          write!(f, ": {}", ty)?;
        }
        write!(f, " = {}", self.func.display_expr(*expr))
      }
      Stmt::FunctionDef(_, _) => write!(f, "<function definition>"),
      Stmt::Struct => write!(f, "<struct definition>"),
    }
  }
}

impl fmt::Display for DisplayExpr<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.func.exprs[self.expr] {
      Expr::Literal(lit) => write!(f, "{lit}"),
      Expr::Local(local_id) => {
        let local = &self.func.locals[local_id];
        write!(f, "{}", local.name)
      }
      Expr::Name(ref name) => write!(f, "{name}"),
      Expr::String(ref parts) => {
        write!(f, "\"")?;
        for part in parts {
          match part {
            StringInterp::Literal(s) => write!(f, "{s}")?,
            StringInterp::Expr(e) => write!(f, "#{{{}}}", self.func.display_expr(*e))?,
          }
        }
        write!(f, "\"")
      }
      Expr::Array(_) => todo!(),
      Expr::Call(lhs, ref args) => {
        write!(f, "{}(", self.func.display_expr(lhs))?;
        for (i, arg) in args.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", self.func.display_expr(*arg))?;
        }
        write!(f, ")")
      }
      Expr::UnaryOp(expr, op) => {
        write!(f, "{op}{}", self.func.display_expr(expr))
      }
      Expr::BinaryOp(lhs, op, rhs) => {
        write!(f, "{} {} {}", self.func.display_expr(lhs), op, self.func.display_expr(rhs))
      }
      Expr::Index(lhs, index) => {
        write!(f, "{}[{}]", self.func.display_expr(lhs), self.func.display_expr(index))
      }
      Expr::Field(expr, ref field) => {
        write!(f, "{}.{}", self.func.display_expr(expr), field)
      }
      Expr::StructInit(ref path, ref fields) => {
        write!(f, "{} {{ ", path)?;
        for (i, (field_name, expr)) in fields.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}: {}", field_name, self.func.display_expr(*expr))?;
        }
        Ok(())
      }
      Expr::Cast(expr, ref ty) => {
        write!(f, "({}) as {}", self.func.display_expr(expr), ty)
      }
      Expr::Paren(expr) => {
        write!(f, "({})", self.func.display_expr(expr))
      }
      Expr::Block(ref stmts) => {
        write!(f, "{{")?;
        for &stmt in stmts {
          write!(f, "\n    {}", self.func.display_stmt(stmt))?;
        }
        write!(f, "\n}}")
      }
      Expr::If { cond, then, els } => {
        write!(f, "if {} {}", self.func.display_expr(cond), self.func.display_expr(then))?;
        if let Some(els) = els {
          write!(f, " else {}", self.func.display_expr(els))?;
        }
        Ok(())
      }
      Expr::Assign { lhs, rhs } => {
        write!(f, "{} = {}", self.func.display_expr(lhs), self.func.display_expr(rhs))
      }
    }
  }
}

impl fmt::Display for Literal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Literal::Bool(b) => write!(f, "{b}"),
      Literal::Int(i) => write!(f, "{i}"),
    }
  }
}

impl fmt::Display for UnaryOp {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      UnaryOp::Neg => write!(f, "-"),
      UnaryOp::Not => write!(f, "!"),
      UnaryOp::Ref => write!(f, "&"),
      UnaryOp::Deref => write!(f, "*"),
    }
  }
}

impl fmt::Display for BinaryOp {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      BinaryOp::Add => write!(f, "+"),
      BinaryOp::Sub => write!(f, "-"),
      BinaryOp::Mul => write!(f, "*"),
      BinaryOp::Div => write!(f, "/"),
      BinaryOp::Mod => write!(f, "%"),
      BinaryOp::BitAnd => write!(f, "&"),
      BinaryOp::BitOr => write!(f, "|"),
      BinaryOp::Xor => write!(f, "^"),
      BinaryOp::ShiftLeft => write!(f, "<<"),
      BinaryOp::ShiftRight => write!(f, ">>"),
      BinaryOp::And => write!(f, "&&"),
      BinaryOp::Or => write!(f, "||"),
      BinaryOp::Eq => write!(f, "=="),
      BinaryOp::Neq => write!(f, "!="),
      BinaryOp::Lt => write!(f, "<"),
      BinaryOp::Lte => write!(f, "<="),
      BinaryOp::Gt => write!(f, ">"),
      BinaryOp::Gte => write!(f, ">="),
    }
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
      Type::Ref(t, Mutability::Imm) => write!(f, "&{t}"),
      Type::Ref(t, Mutability::Mut) => write!(f, "&mut {t}"),
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

impl fmt::Display for FullyQualifiedName {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      FullyQualifiedName::Bare { path, name } => {
        if path.segments.is_empty() {
          write!(f, "{name}")
        } else {
          write!(f, "{}::{}", path, name)
        }
      }
      FullyQualifiedName::TraitImpl { trait_path, struct_path, name } => {
        write!(f, "<{} as {}>::{}", struct_path, trait_path, name)
      }
    }
  }
}
