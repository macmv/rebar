//! Lowers the AST from rb_syntax into an HIR tree. Performs no type inferrence,
//! and only validates syntax.

use crate::ast as hir;
use rb_syntax::cst;

pub fn lower_expr(hir: cst::Expr) -> hir::Expr {
  match hir {
    cst::Expr::Literal(_) => todo!(),

    _ => unimplemented!("lowering for {:?}", hir),
  }
}
