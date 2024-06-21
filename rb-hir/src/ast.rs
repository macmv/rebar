use la_arena::Idx;

use crate::literal::Literal;

pub type ExprId = Idx<Expr>;

#[derive(Debug)]
pub enum Expr {
  Literal(Literal),

  Assign { lhs: ExprId, rhs: ExprId },
}
