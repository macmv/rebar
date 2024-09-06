// TODO

use std::{error::Error, sync::Arc};

use lsp_types::{SemanticTokenType, SemanticTokensParams, SemanticTokensResult};
use rb_diagnostic::{Source, Sources};
use rb_syntax::cst;
use rl_analysis::{
  highlight::{Highlight, HighlightKind},
  FileId,
};

use crate::global::GlobalStateSnapshot;

pub fn handle_semantic_tokens_full(
  snap: GlobalStateSnapshot,
  params: SemanticTokensParams,
) -> Result<Option<SemanticTokensResult>, Box<dyn Error>> {
  if let Some(path) = snap.workspace_path(&params.text_document.uri) {
    let file_id = snap.files.read().path_to_id(&path);
    let file = snap.files.read().read(file_id);

    let mut sources = Sources::new();
    let id = sources.add(Source::new("inline.rbr".into(), file.clone()));
    let sources = Arc::new(sources);

    let res = rb_diagnostic::run(sources.clone(), || {
      let res = cst::SourceFile::parse(&file);

      if res.errors().is_empty() {
        rb_hir_lower::lower_source(res.tree(), id)
      } else {
        Default::default()
      }
    });

    let (hir, span_maps) = match res {
      Ok(hir) => hir,
      Err(_) => return Ok(None),
    };

    let highlight = Highlight::from_ast(hir, &span_maps[0]);

    let tokens = to_semantic_tokens(snap, file_id, &highlight)?;
    info!("tokens: {:?}", tokens);

    Ok(Some(lsp_types::SemanticTokensResult::Tokens(lsp_types::SemanticTokens {
      data:      tokens,
      result_id: None,
    })))
  } else {
    Ok(None)
  }
}

pub fn semantic_tokens_legend() -> lsp_types::SemanticTokensLegend {
  fn token_type(kind: HighlightKind) -> SemanticTokenType {
    match kind {
      HighlightKind::Function => SemanticTokenType::new("function"),
      HighlightKind::Keyword => SemanticTokenType::new("keyword"),
      HighlightKind::Number => SemanticTokenType::new("number"),
      HighlightKind::Operator => SemanticTokenType::new("operator"),
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

fn to_semantic_tokens(
  snap: GlobalStateSnapshot,
  file: FileId,
  highlight: &Highlight,
) -> Result<Vec<lsp_types::SemanticToken>, Box<dyn Error>> {
  let line_index = snap.analysis.line_index(file)?;

  let mut tokens = Vec::new();

  let mut line = 0;
  let mut col = 0;

  info!("highlight: {:?}", highlight.tokens);

  for h in highlight.tokens.iter() {
    let range = h.range;

    let pos = line_index.line_col(range.start());

    let delta_line = pos.line - line;
    if delta_line != 0 {
      col = 0;
    }
    let delta_start = pos.col - col;

    line = pos.line;
    col = pos.col;

    tokens.push(lsp_types::SemanticToken {
      delta_line,
      delta_start,
      length: (range.end() - range.start()).into(),
      token_type: h.kind as u32,
      token_modifiers_bitset: 0,
    });
  }

  Ok(tokens)
}
