use la_arena::Idx;

pub type ExprId = Idx<Expr>;

#[derive(Debug)]
pub enum Expr {
  Literal(Literal),

  Assign { lhs: ExprId, rhs: ExprId },
}

#[derive(Debug)]
pub enum Literal {
  Int(i64),
  Bool(bool),
  Unit,
}
