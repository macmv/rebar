pub mod ast;

use std::{collections::HashMap, ops::Index};

use ast::{ExprId, FunctionId, StmtId};
use rb_diagnostic::Span;

use crate::ast::Path;

#[derive(Default)]
pub struct SpanMap {
  pub modules: HashMap<Path, ModuleSpanMap>,
}

#[derive(Default)]
pub struct ModuleSpanMap {
  pub functions: HashMap<FunctionId, FunctionSpanMap>,
}

#[derive(Default)]
pub struct FunctionSpanMap {
  pub name_span: Option<Span>,

  pub exprs: Vec<Span>,
  pub stmts: Vec<Span>,

  pub let_stmts: HashMap<StmtId, Span>,

  pub binary_ops: HashMap<ExprId, Span>,
  pub unary_ops:  HashMap<ExprId, Span>,
  pub if_exprs:   HashMap<ExprId, (Span, Option<Span>)>,
}

impl Index<ExprId> for FunctionSpanMap {
  type Output = Span;

  fn index(&self, index: ExprId) -> &Self::Output {
    &self.exprs[index.into_raw().into_u32() as usize]
  }
}

impl Index<StmtId> for FunctionSpanMap {
  type Output = Span;

  fn index(&self, index: StmtId) -> &Self::Output {
    &self.stmts[index.into_raw().into_u32() as usize]
  }
}
