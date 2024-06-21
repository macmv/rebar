pub mod ast;

use rb_diagnostic::Span;

#[derive(Default)]
pub struct SpanMap {
  pub exprs: Vec<Span>,
  pub stmts: Vec<Span>,
}
