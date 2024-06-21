//! Lowers HIR and the result of typechecking into MIR.

use rb_hir::ast as hir;
use rb_mir::ast as mir;
use rb_typer::Typer;

pub fn lower_expr(_: &Typer, hir: hir::Expr) -> mir::Expr {
  match hir {
    hir::Expr::Literal(_) => todo!(),

    _ => unimplemented!("lowering for {:?}", hir),
  }
}
