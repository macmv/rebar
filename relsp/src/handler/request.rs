// TODO

use std::error::Error;

use lsp_types::{SemanticTokenType, SemanticTokensParams, SemanticTokensResult};

use crate::{analysis::highlight::HighlightKind, global::GlobalStateSnapshot};

pub fn handle_semantic_tokens_full(
  snap: GlobalStateSnapshot,
  params: SemanticTokensParams,
) -> Result<Option<SemanticTokensResult>, Box<dyn Error>> {
  Ok(None)
}

pub fn semantic_tokens_legend() -> lsp_types::SemanticTokensLegend {
  fn token_type(kind: HighlightKind) -> SemanticTokenType {
    match kind {
      HighlightKind::Function => SemanticTokenType::new("function"),
      HighlightKind::Keyword => SemanticTokenType::new("keyword"),
      HighlightKind::Number => SemanticTokenType::new("number"),
      HighlightKind::String => SemanticTokenType::new("string"),
      HighlightKind::Parameter => SemanticTokenType::new("parameter"),
      HighlightKind::Type => SemanticTokenType::new("type"),
      HighlightKind::Variable => SemanticTokenType::new("variable"),
    }
  }

  lsp_types::SemanticTokensLegend {
    token_types:     HighlightKind::iter().map(token_type).collect(),
    token_modifiers: vec![],
  }
}
