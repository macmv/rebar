use la_arena::{Arena, Idx};

pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;
pub type FunctionId = Idx<Function>;

#[derive(Debug, Default)]
pub struct SourceFile {
  pub functions: Arena<Function>,

  // If there are any statements outside of functions, they will be stored in a "main function,"
  // stored here.
  pub main_function: Option<FunctionId>,
}

#[derive(Debug, Default)]
pub struct Function {
  pub args: Vec<(String, TypeExpr)>,

  pub exprs: Arena<Expr>,
  pub stmts: Arena<Stmt>,

  pub items: Vec<StmtId>,
}

#[derive(Debug)]
pub enum Expr {
  Literal(Literal),
  Name(String),

  Call(ExprId, Vec<ExprId>),
  UnaryOp(ExprId, UnaryOp),
  BinaryOp(ExprId, BinaryOp, ExprId),

  // TODO: Is this really needed?
  Paren(ExprId),
  Block(Vec<StmtId>),
  If { cond: ExprId, then: ExprId, els: Option<ExprId> },

  Assign { lhs: ExprId, rhs: ExprId },
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
  Nil,
  Bool,
  Int,
  Union(Vec<TypeExpr>),
}

#[derive(Debug)]
pub enum Stmt {
  Expr(ExprId),

  // TODO: Add type literals for explicit types.
  Let(String, ExprId),

  Def(String, Vec<(String, TypeExpr)>, Option<TypeExpr>),
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
  And,
  Or,
  Eq,
  Neq,
  Lt,
  Lte,
  Gt,
  Gte,
}
