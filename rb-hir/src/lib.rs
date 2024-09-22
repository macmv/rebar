pub mod ast;

use std::collections::HashMap;

use ast::{ExprId, StmtId};
use rb_diagnostic::Span;

#[derive(Default)]
pub struct SpanMap {
  pub exprs: Vec<Span>,
  pub stmts: Vec<Span>,

  pub let_stmts: HashMap<StmtId, Span>,

  pub binary_ops: HashMap<ExprId, Span>,
  pub unary_ops:  HashMap<ExprId, Span>,
}
