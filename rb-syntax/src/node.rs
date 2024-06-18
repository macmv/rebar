use rb_parser::SyntaxKind;
use rowan::Language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Scala {}
impl Language for Scala {
  type Kind = SyntaxKind;

  fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind { SyntaxKind::from(raw.0) }

  fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind { rowan::SyntaxKind(kind.into()) }
}

pub type SyntaxNode = rowan::SyntaxNode<Scala>;
pub type SyntaxToken = rowan::SyntaxToken<Scala>;
pub type SyntaxElement = rowan::SyntaxElement<Scala>;
pub type SyntaxNodeChildren = rowan::SyntaxNodeChildren<Scala>;
pub type SyntaxElementChildren = rowan::SyntaxElementChildren<Scala>;
pub type PreorderWithTokens = rowan::api::PreorderWithTokens<Scala>;
pub type NodeOrToken = rowan::NodeOrToken<SyntaxNode, SyntaxToken>;
