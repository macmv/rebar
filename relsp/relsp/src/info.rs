pub fn version() -> &'static str { env!("CARGO_PKG_VERSION") }

pub fn server_capabilities() -> lsp_types::ServerCapabilities {
  lsp_types::ServerCapabilities {
    text_document_sync: Some(lsp_types::TextDocumentSyncCapability::Kind(
      lsp_types::TextDocumentSyncKind::INCREMENTAL,
    )),

    semantic_tokens_provider: Some(
      lsp_types::SemanticTokensServerCapabilities::SemanticTokensOptions(
        lsp_types::SemanticTokensOptions {
          legend: crate::handler::request::semantic_tokens_legend(),
          // range: Some(true),
          // full: Some(lsp_types::SemanticTokensFullOptions::Delta { delta: Some(true) }),
          range: Some(false),
          full: Some(lsp_types::SemanticTokensFullOptions::Delta { delta: Some(false) }),
          ..Default::default()
        },
      ),
    ),

    ..Default::default()
  }
}
