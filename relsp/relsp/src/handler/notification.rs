use std::error::Error;

use crate::global::GlobalState;

pub fn handle_open_text_document(
  global: &mut GlobalState,
  params: lsp_types::DidOpenTextDocumentParams,
) -> Result<(), Box<dyn Error>> {
  if let Some(path) = global.workspace_path(&params.text_document.uri) {
    let mut w = global.files.write();
    let file_id = w.create(&path);
    w.write(file_id, params.text_document.text.clone());
  }

  Ok(())
}

pub fn handle_change_text_document(
  global: &mut GlobalState,
  params: lsp_types::DidChangeTextDocumentParams,
) -> Result<(), Box<dyn Error>> {
  if let Some(path) = global.workspace_path(&params.text_document.uri) {
    let file_id = global.files.read().path_to_id(&path);
    let file = global.files.read().read(file_id);

    let new_file = apply_changes(file.clone(), &params.content_changes);

    if file != new_file {
      global.files.write().write(file_id, new_file.clone());
    }
  }

  Ok(())
}

pub fn handle_save_text_document(
  global: &mut GlobalState,
  params: lsp_types::DidSaveTextDocumentParams,
) -> Result<(), Box<dyn Error>> {
  if let Some(_) = global.workspace_path(&params.text_document.uri) {
    // TODO: Go typecheck? Idk. We kinda do everything on every character press.
    // Not sure if we actually need to do anything on save.
  }

  Ok(())
}

fn apply_changes(
  mut file: String,
  changes: &[lsp_types::TextDocumentContentChangeEvent],
) -> String {
  for change in changes {
    match change.range {
      Some(range) => {
        let start = offset_of(&file, range.start);
        let end = offset_of(&file, range.end);

        file.replace_range(start..end, &change.text);
      }
      None => {
        file.replace_range(.., &change.text);
      }
    }
  }

  file
}

// TODO: Cache this somewhere.
fn offset_of(file: &str, pos: lsp_types::Position) -> usize {
  let mut offset = 0;

  for (i, line) in file.lines().enumerate() {
    if i == pos.line as usize {
      return offset + pos.character as usize;
    }

    offset += line.len() + 1;
  }

  offset
}
