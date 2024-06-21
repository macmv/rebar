use la_arena::Idx;
use rb_hir::literal::Literal;
use rb_typer::Type;

pub type ExprId = Idx<Expr>;

pub enum Expr {
  Literal(Literal),

  Assign { variable: String, ty: Type, rhs: ExprId },

  While { cond: ExprId },
}
