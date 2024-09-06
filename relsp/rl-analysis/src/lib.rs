use std::{fmt, sync::Arc};

pub mod highlight;

mod file;
pub use file::FileId;
use line_index::LineIndex;

#[salsa::database(SourceDatabaseStorage, LineIndexDatabaseStorage)]
#[derive(Default)]
pub struct RootDatabase {
  pub(crate) storage: salsa::Storage<Self>,
}
impl salsa::Database for RootDatabase {}

impl fmt::Debug for RootDatabase {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RootDatabase").finish()
  }
}

#[salsa::query_group(LineIndexDatabaseStorage)]
pub trait LineIndexDatabase: SourceDatabase {
  fn line_index(&self, file_id: FileId) -> Arc<LineIndex>;
}

#[salsa::query_group(SourceDatabaseStorage)]
pub trait SourceDatabase: std::fmt::Debug {
  /// Returns the current content of the file.
  #[salsa::input]
  fn file_text(&self, file_id: FileId) -> Arc<str>;
}

fn line_index(db: &dyn LineIndexDatabase, file_id: FileId) -> Arc<LineIndex> {
  let text = db.file_text(file_id);
  Arc::new(LineIndex::new(&text))
}
