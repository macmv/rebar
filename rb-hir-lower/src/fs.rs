use std::{io, path::Path};

pub trait FileSystem {
  fn read_to_string(&self, path: &Path) -> io::Result<String>;
}

pub struct Native;

impl FileSystem for Native {
  fn read_to_string(&self, path: &Path) -> io::Result<String> { std::fs::read_to_string(path) }
}
