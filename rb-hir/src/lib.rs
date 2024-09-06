pub mod ast;

use std::collections::HashMap;

use ast::ExprId;
use rb_diagnostic::Span;

#[derive(Default)]
pub struct SpanMap {
  pub exprs: Vec<Span>,
  pub stmts: Vec<Span>,

  pub binary_ops: HashMap<ExprId, Span>,
  pub unary_ops:  HashMap<ExprId, Span>,
}
