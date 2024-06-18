use crate::{
  ext::{AstChildren, AstNode, AstTokenChildren, SyntaxKind},
  node::{SyntaxNode, SyntaxToken},
};

pub(super) fn child<N: AstNode>(parent: &SyntaxNode) -> Option<N> {
  parent.children().find_map(N::cast)
}

pub(super) fn children<N: AstNode>(parent: &SyntaxNode) -> AstChildren<N> {
  AstChildren::new(parent)
}

pub(super) fn token(parent: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
  parent.children_with_tokens().filter_map(|it| it.into_token()).find(|it| it.kind() == kind)
}

pub(super) fn token_children(parent: &SyntaxNode, kind: SyntaxKind) -> AstTokenChildren {
  AstTokenChildren::new(parent, kind)
}
