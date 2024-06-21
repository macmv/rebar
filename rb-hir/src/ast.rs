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
  pub exprs: Arena<Expr>,
  pub stmts: Arena<Stmt>,

  pub items: Vec<StmtId>,
}

#[derive(Debug)]
pub enum Expr {
  Literal(Literal),
  Call(ExprId, Vec<ExprId>),
  Name(String),
  BinaryOp(ExprId, BinaryOp, ExprId),

  Assign { lhs: ExprId, rhs: ExprId },
}

#[derive(Debug)]
pub enum Stmt {
  Expr(ExprId),
}

#[derive(Debug)]
pub enum Literal {
  Int(i64),
  Bool(bool),
  Unit,
}

#[derive(Debug)]
pub enum BinaryOp {
  Add,
  Sub,
  Mul,
  Div,
  Mod,
  And,
  Or,
  Eq,
  Neq,
  Lt,
  Lte,
  Gt,
  Gte,
}
