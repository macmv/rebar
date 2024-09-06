#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(u32);

impl FileId {
  /// DO NOT USE THIS! Its just for unit tests.
  pub fn new_raw(id: u32) -> Self { FileId(id) }
}
