use std::marker::PhantomData;

use crate::{
  cst,
  node::{SyntaxElementChildren, SyntaxNode, SyntaxNodeChildren, SyntaxToken},
  support,
};
pub use rb_parser::SyntaxKind;

/// The main trait to go from untyped `SyntaxNode`  to a typed ast. The
/// conversion itself has zero runtime cost: ast and syntax nodes have exactly
/// the same representation: a pointer to the tree root and a pointer to the
/// node itself.
pub trait AstNode {
  fn can_cast(kind: SyntaxKind) -> bool
  where
    Self: Sized;

  fn cast(syntax: SyntaxNode) -> Option<Self>
  where
    Self: Sized;

  fn syntax(&self) -> &SyntaxNode;
  fn clone_for_update(&self) -> Self
  where
    Self: Sized,
  {
    Self::cast(self.syntax().clone_for_update()).unwrap()
  }
  fn clone_subtree(&self) -> Self
  where
    Self: Sized,
  {
    Self::cast(self.syntax().clone_subtree()).unwrap()
  }
}

/// Like `AstNode`, but wraps tokens rather than interior nodes.
#[allow(dead_code)]
pub trait AstToken {
  fn can_cast(token: SyntaxKind) -> bool
  where
    Self: Sized;

  fn cast(syntax: SyntaxToken) -> Option<Self>
  where
    Self: Sized;

  fn syntax(&self) -> &SyntaxToken;

  fn text(&self) -> &str { self.syntax().text() }
}

/// An iterator over `SyntaxNode` children of a particular AST type.
#[derive(Debug, Clone)]
pub struct AstChildren<N> {
  inner: SyntaxNodeChildren,
  ph:    PhantomData<N>,
}

impl<N> AstChildren<N> {
  pub(crate) fn new(parent: &SyntaxNode) -> Self {
    AstChildren { inner: parent.children(), ph: PhantomData }
  }
}

impl<N: AstNode> Iterator for AstChildren<N> {
  type Item = N;
  fn next(&mut self) -> Option<N> { self.inner.find_map(N::cast) }
}

/// An iterator over `SyntaxToken` children of a particular AST type.
#[derive(Debug, Clone)]
pub struct AstTokenChildren {
  inner: SyntaxElementChildren,
  kind:  SyntaxKind,
}

impl AstTokenChildren {
  pub(crate) fn new(parent: &SyntaxNode, kind: SyntaxKind) -> Self {
    AstTokenChildren { inner: parent.children_with_tokens(), kind }
  }
}

impl Iterator for AstTokenChildren {
  type Item = SyntaxToken;
  fn next(&mut self) -> Option<SyntaxToken> {
    loop {
      let it = self.inner.next()?;
      if it.kind() == self.kind {
        if let Some(t) = it.into_token() {
          return Some(t);
        }
      }
    }
  }
}

impl cst::BinaryExpr {
  pub fn lhs(&self) -> Option<cst::Expr> { support::children(&self.syntax).next() }
  pub fn rhs(&self) -> Option<cst::Expr> { support::children(&self.syntax).nth(1) }
}

impl cst::BinaryType {
  pub fn lhs(&self) -> Option<cst::Type> { support::children(&self.syntax).next() }
  pub fn rhs(&self) -> Option<cst::Type> { support::children(&self.syntax).nth(1) }
}

impl cst::IfExpr {
  pub fn cond(&self) -> Option<cst::Expr> { support::children(&self.syntax).next() }
  pub fn then(&self) -> Option<cst::Expr> { support::children(&self.syntax).nth(1) }
  pub fn els(&self) -> Option<cst::Expr> { support::children(&self.syntax).nth(2) }
}
