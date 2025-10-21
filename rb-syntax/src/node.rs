use rb_parser::SyntaxKind;
use rowan::Language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rebar {}
impl Language for Rebar {
  type Kind = SyntaxKind;

  fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind { SyntaxKind::from(raw.0) }

  fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind { rowan::SyntaxKind(kind.into()) }
}

pub type SyntaxNode = rowan::SyntaxNode<Rebar>;
pub type SyntaxNodePtr = rowan::ast::SyntaxNodePtr<Rebar>;
pub type SyntaxToken = rowan::SyntaxToken<Rebar>;
pub type SyntaxElement = rowan::SyntaxElement<Rebar>;
pub type SyntaxNodeChildren = rowan::SyntaxNodeChildren<Rebar>;
pub type SyntaxElementChildren = rowan::SyntaxElementChildren<Rebar>;
pub type PreorderWithTokens = rowan::api::PreorderWithTokens<Rebar>;
pub type NodeOrToken = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;
