use std::{collections::HashSet, fmt};

use la_arena::{Arena, Idx};
use rb_hir::ast::Type;

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
  pub ret:    Type,

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
  SlicePtr,
  SliceLen,
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

impl Function {
  pub fn display_stmt(&self, id: StmtId) -> impl fmt::Display {
    DisplayStmt { stmt: &self.stmts[id], func: self }
  }

  pub fn display_expr(&self, id: ExprId) -> impl fmt::Display {
    DisplayExpr { expr: &self.exprs[id], func: self }
  }
}

impl fmt::Display for Function {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(f, "function {}:", self.id.0)?;

    for &stmt_id in &self.items {
      writeln!(f, "  {}", self.display_stmt(stmt_id))?;
    }

    Ok(())
  }
}

struct DisplayStmt<'a> {
  stmt: &'a Stmt,
  func: &'a Function,
}

impl fmt::Display for DisplayStmt<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.stmt {
      Stmt::Expr(expr) => {
        write!(f, "{};", self.func.display_expr(*expr))
      }

      Stmt::Let(var_id, ty, expr) => {
        write!(f, "let {}: {} = {};", var_id, ty, self.func.display_expr(*expr))
      }
    }
  }
}

impl fmt::Display for VarId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "v{}", self.0) }
}

struct DisplayExpr<'a> {
  expr: &'a Expr,
  func: &'a Function,
}

impl fmt::Display for DisplayExpr<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self.expr {
      Expr::Literal(lit) => write!(f, "{}", lit),

      Expr::Array(elements, ty) => {
        write!(f, "array::<{}>[", ty)?;
        for (i, elem) in elements.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", self.func.display_expr(*elem))?;
        }
        write!(f, "]")
      }

      Expr::Unary(arg, op, ty) => {
        let op_str = match op {
          UnaryOp::Neg => "-",
          UnaryOp::Not => "!",
        };
        write!(f, "({}{})::<{}>", op_str, self.func.display_expr(*arg), ty)
      }

      Expr::Binary(left, op, right, ty) => {
        write!(
          f,
          "({} {} {})::<{}>",
          self.func.display_expr(*left),
          op,
          self.func.display_expr(*right),
          ty
        )
      }

      Expr::Index(array, index, ty) => {
        write!(
          f,
          "{}[{}]::<{}>",
          self.func.display_expr(*array),
          self.func.display_expr(*index),
          ty
        )
      }

      Expr::Local(var_id, _) => write!(f, "{}", var_id),

      Expr::UserFunction(_, _) => todo!(),
      Expr::Native(_, _) => todo!(),

      Expr::StructInit(struct_id, fields) => {
        write!(f, "StructInit {} {{ ", struct_id.0)?;
        for (i, (name, expr)) in fields.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}: {}", name, self.func.display_expr(*expr))?;
        }
        write!(f, " }}")
      }

      Expr::Block(stmts) => {
        write!(f, "{{ ")?;
        for stmt in stmts {
          write!(f, "{} ", self.func.display_stmt(*stmt))?;
        }
        write!(f, "}}")
      }

      Expr::Call(func_id, ty, args) => {
        write!(f, "call {}::<{}>(", func_id.0, ty)?;
        for (i, arg) in args.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", self.func.display_expr(*arg))?;
        }
        write!(f, ")")
      }

      Expr::If { cond, then, els, ty } => {
        write!(f, "if {} {{ {} }}", self.func.display_expr(*cond), self.func.display_expr(*then))?;
        if let Some(els) = els {
          write!(f, " else {{ {} }}", self.func.display_expr(*els))?;
        }
        write!(f, "::<{}>", ty)
      }

      Expr::Assign { variable, ty, rhs } => {
        write!(f, "{}::<{}> = {};", variable, ty, self.func.display_expr(*rhs))
      }

      Expr::While { cond } => {
        write!(f, "while {} {{ ... }}", self.func.display_expr(*cond))
      }

      Expr::CallIntrinsic(intrinsic, args) => {
        let intrinsic_str = match intrinsic {
          Intrinsic::SlicePtr => "slice_ptr",
          Intrinsic::SliceLen => "slice_len",
          Intrinsic::Syscall => "syscall",
          Intrinsic::Trap => "trap",
        };
        write!(f, "intrinsic {}(", intrinsic_str)?;
        for (i, arg) in args.iter().enumerate() {
          if i != 0 {
            write!(f, ", ")?;
          }
          write!(f, "{}", self.func.display_expr(*arg))?;
        }
        write!(f, ")")
      }
    }
  }
}

impl fmt::Display for Literal {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Literal::Bool(v) => write!(f, "{}", v),
      Literal::Int(v) => write!(f, "{}", v),
      Literal::String(s) => write!(f, "\"{}\"", s),
    }
  }
}

impl fmt::Display for BinaryOp {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let op_str = match self {
      BinaryOp::Add => "+",
      BinaryOp::Sub => "-",
      BinaryOp::Mul => "*",
      BinaryOp::Div => "/",
      BinaryOp::Mod => "%",
      BinaryOp::BitAnd => "&",
      BinaryOp::BitOr => "|",
      BinaryOp::Xor => "^",
      BinaryOp::ShiftLeft => "<<",
      BinaryOp::ShiftRight => ">>",
      BinaryOp::And => "&&",
      BinaryOp::Or => "||",
      BinaryOp::Eq => "==",
      BinaryOp::Neq => "!=",
      BinaryOp::Lt => "<",
      BinaryOp::Lte => "<=",
      BinaryOp::Gt => ">",
      BinaryOp::Gte => ">=",
    };
    write!(f, "{}", op_str)
  }
}
