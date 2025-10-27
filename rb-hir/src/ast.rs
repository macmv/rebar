use la_arena::{Arena, Idx};

pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;
pub type FunctionId = Idx<Function>;
pub type StructId = Idx<Struct>;

#[derive(Debug, Default)]
pub struct Module {
  pub functions: Arena<Function>,
  pub structs:   Arena<Struct>,

  // If there are any statements outside of functions, they will be stored in a "main function,"
  // stored here.
  pub main_function: Option<FunctionId>,
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
  Name(String),

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

impl TypeExpr {
  pub fn unit() -> Self { TypeExpr::Tuple(vec![]) }
}

impl From<PrimitiveType> for TypeExpr {
  fn from(value: PrimitiveType) -> Self { TypeExpr::Primitive(value) }
}
