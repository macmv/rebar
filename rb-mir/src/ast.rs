use std::collections::HashSet;

use la_arena::{Arena, Idx};
use rb_typer::Type;

pub type ExprId = Idx<Expr>;
pub type StmtId = Idx<Stmt>;

#[derive(Debug, Default)]
pub struct Function {
  pub id: UserFunctionId,

  pub exprs: Arena<Expr>,
  pub stmts: Arena<Stmt>,

  pub items: Vec<StmtId>,

  /// The parameters of this function.
  pub params: Vec<Type>,
  /// The return type of this function.
  pub ret:    Option<Type>,

  /// Local variables in this function.
  pub vars: Vec<Type>,

  /// Other user-defined functions that this function calls.
  pub deps: HashSet<UserFunctionId>,
}

/// A local variable ID. Variable ids reset at the start of each function
/// definition. This mostly just makes the JIT easier to write.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

/// A native function ID. These are static from the perspective of the JIT.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NativeFunctionId(pub u64);

/// A user-defined function ID. These are assigned just before lowering to MIR.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UserFunctionId(pub u64);

/// A user-defined struct ID. These are assigned just before lowering to MIR.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructId(pub u64);

#[derive(Debug)]
pub enum Expr {
  Literal(Literal),
  Call(UserFunctionId, Type, Vec<ExprId>),

  Array(Vec<ExprId>, Type),

  Unary(ExprId, UnaryOp, Type),
  Binary(ExprId, BinaryOp, ExprId, Type),
  Index(ExprId, ExprId, Type),

  Local(VarId, Type),
  UserFunction(UserFunctionId, Type),
  Native(NativeFunctionId, Type),
  StructInit(StructId, Vec<(String, ExprId)>),

  Block(Vec<StmtId>),

  If { cond: ExprId, then: ExprId, els: Option<ExprId>, ty: Type },
  Assign { variable: String, ty: Type, rhs: ExprId },

  While { cond: ExprId },

  CallIntrinsic(Intrinsic, Vec<ExprId>),
}

#[derive(Debug, Clone, Copy)]
pub enum Intrinsic {
  StringPtr,
  StringLen,
  Syscall,
  Trap,
}

#[derive(Debug)]
pub enum Stmt {
  Expr(ExprId),
  Let(VarId, Type, ExprId),
}

#[derive(Debug)]
pub enum Literal {
  Nil,
  Bool(bool),
  Int(i64),
  String(String),
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
