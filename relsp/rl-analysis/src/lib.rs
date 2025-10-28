use std::{collections::HashMap, fmt, panic::UnwindSafe, sync::Arc};

pub mod highlight;

mod file;
pub use file::FileId;

use rb_diagnostic::{Diagnostic, Span};
use rb_syntax::{Parse, cst};
use salsa::{Accumulator, Cancelled, Setter};

#[derive(Default)]
pub struct AnalysisHost {
  db: RootDatabase,
}

/// A snapshot of analysis at a point in time.
pub struct Analysis {
  db: RootDatabase,
}

pub type Cancellable<T> = Result<T, Cancelled>;

impl AnalysisHost {
  pub fn new() -> Self { AnalysisHost::default() }
  pub fn snapshot(&self) -> Analysis { Analysis { db: self.db.clone() } }

  pub fn change_file(&mut self, file_id: FileId, new_text: String) {
    self.db.set_file_text(file_id, Arc::from(new_text));
  }
}

impl Analysis {
  pub fn line_index(&self, file: FileId) -> Cancellable<Arc<::line_index::LineIndex>> {
    self.with_db(|db| line_index(db, db.file_text(file)).index(db))
  }

  fn with_db<T>(&self, f: impl FnOnce(&RootDatabase) -> T + UnwindSafe) -> Cancellable<T> {
    Cancelled::catch(|| f(&self.db))
  }
}

#[salsa::db]
#[derive(Default, Clone)]
struct RootDatabase {
  pub(crate) storage: salsa::Storage<Self>,

  files: HashMap<FileId, File>,
}

#[salsa::db]
impl salsa::Database for RootDatabase {}

#[salsa::db]
impl SourceDatabase for RootDatabase {
  fn file_text(&self, file: FileId) -> File { self.files.get(&file).unwrap().clone() }
  fn set_file_text(&mut self, file: FileId, text: Arc<str>) {
    if self.files.contains_key(&file) {
      self.files.get(&file).unwrap().set_text(self).to(text);
    } else {
      self.files.insert(file, File::new(self, file, text));
    }
  }
}

impl fmt::Debug for RootDatabase {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RootDatabase").finish()
  }
}

#[salsa::db]
trait SourceDatabase: salsa::Database {
  fn file_text(&self, file: FileId) -> File;
  fn set_file_text(&mut self, file: FileId, text: Arc<str>);
}

#[salsa::input]
struct File {
  id:   FileId,
  #[returns(ref)]
  text: Arc<str>,
}

#[salsa::tracked]
struct LineIndex<'db> {
  #[tracked]
  index: Arc<::line_index::LineIndex>,
}

#[salsa::tracked]
fn line_index(db: &dyn SourceDatabase, file: File) -> LineIndex<'_> {
  LineIndex::new(db, Arc::new(::line_index::LineIndex::new(&file.text(db))))
}

#[salsa::tracked]
struct ParseCst<'db> {
  #[tracked]
  parsed: Parse<cst::SourceFile>,
}

#[salsa::accumulator]
struct DiagnosticAcc(Diagnostic);

#[salsa::tracked]
fn parse_cst(db: &dyn SourceDatabase, file: File) -> ParseCst<'_> {
  let source = file.text(db);
  let res = cst::SourceFile::parse(source);

  for _error in res.errors() {
    /*
    DiagnosticAcc(Diagnostic::error(error.message(), Span { file: (), range: error.span() }))
      .accumulate(db);
    */
  }

  ParseCst::new(db, res)
}
