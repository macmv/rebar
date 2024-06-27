mod error;
mod ext;
mod generated;
mod node;
mod parse;
mod support;

pub use node::*;

pub use error::SyntaxError;
pub use ext::AstNode;
pub use rb_parser::{SyntaxKind, T};

use std::{marker::PhantomData, sync::Arc};

use rowan::GreenNode;

pub mod cst {
  pub use crate::generated::*;
}

pub use rowan::{TextRange, TextSize, WalkEvent};

/// `Parse` is the result of the parsing: a syntax tree and a collection of
/// errors.
///
/// Note that we always produce a syntax tree, even for completely invalid
/// files.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parse<T> {
  green:  GreenNode,
  errors: Option<Arc<[SyntaxError]>>,
  _ty:    PhantomData<fn() -> T>,
}

impl cst::SourceFile {
  pub fn parse(text: &str) -> Parse<cst::SourceFile> {
    let (green, errors) = parse::parse_text(text);
    let root = SyntaxNode::new_root(green.clone());

    assert_eq!(root.kind(), SyntaxKind::SOURCE_FILE);
    Parse {
      green,
      errors: if errors.is_empty() { None } else { Some(errors.into()) },
      _ty: PhantomData,
    }
  }
}

impl<T> Parse<T> {
  pub fn syntax_node(&self) -> SyntaxNode { SyntaxNode::new_root(self.green.clone()) }
  pub fn errors(&self) -> &[SyntaxError] { self.errors.as_deref().unwrap_or_default() }
}

impl<T: AstNode> Parse<T> {
  pub fn tree(&self) -> T { T::cast(self.syntax_node()).unwrap() }
}
