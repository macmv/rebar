use la_arena::{Arena, Idx};
use rb_typer::Type;

pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;

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
  Binary(ExprId, BinaryOp, ExprId, Type),
  Name(String, Type),

  Assign { variable: String, ty: Type, rhs: ExprId },

  While { cond: ExprId },
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
