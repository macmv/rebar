use la_arena::{Arena, Idx};
use rb_typer::Type;

pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;

#[derive(Debug, Default)]
pub struct Function {
  pub exprs: Arena<Expr>,
  pub stmts: Arena<Stmt>,

  pub items: Vec<StmtId>,

  /// Local variables in this function.
  pub vars: Vec<Type>,
}

/// A local variable ID. Variable ids reset at the start of each function
/// definition. This mostly just makes the JIT easier to write.
#[derive(Debug, Clone, Copy)]
pub struct VarId(pub u32);

#[derive(Debug)]
pub enum Expr {
  Literal(Literal),
  Call(ExprId, Type, Vec<ExprId>),
  Binary(ExprId, BinaryOp, ExprId, Type),

  Local(VarId),
  Native(String, Type),

  Assign { variable: String, ty: Type, rhs: ExprId },

  While { cond: ExprId },
}

#[derive(Debug)]
pub enum Stmt {
  Expr(ExprId),
  Let(VarId, Type, ExprId),
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
