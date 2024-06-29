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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

/// A native function ID. These are static from the perspective of the JIT.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeFunctionId(pub u64);

#[derive(Debug)]
pub enum Expr {
  Literal(Literal),
  Call(ExprId, Type, Vec<ExprId>),

  Unary(ExprId, UnaryOp, Type),
  Binary(ExprId, BinaryOp, ExprId, Type),

  Local(VarId),
  Native(NativeFunctionId, Type),

  Block(Vec<StmtId>),

  If { cond: ExprId, then: ExprId, els: Option<ExprId> },
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
