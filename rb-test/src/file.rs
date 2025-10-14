use std::{path::PathBuf, sync::LazyLock};

#[macro_export]
macro_rules! temp_dir {
  () => {{
    // Copied from the `stdext::function_name!` macro.

    // Okay, this is ugly, I get it. However, this is the best we can get on a
    // stable rust.
    fn f() {}
    fn type_name_of<T>(_: T) -> &'static str { std::any::type_name::<T>() }
    let name = type_name_of(f);
    // `3` is the length of the `::f`.
    $crate::TempDir::new(&name[..name.len() - 3])
  }};
}

/// A temporary directory. When dropped, the directory will be removed, if the
/// `KEEP_TEMP` environment variable is not set.
pub struct TempDir {
  #[doc(hidden)]
  name: &'static str,
}

#[cfg(target_os = "linux")]
const BASE: &str = "/dev/shm";

static KEEP_TEMP_DIR: LazyLock<bool> = LazyLock::new(|| std::env::var("KEEP_TEMP").is_ok());

impl TempDir {
  #[doc(hidden)]
  pub fn new(name: &'static str) -> Self {
    let dir = TempDir { name };
    let _ = std::fs::remove_dir_all(dir.path());
    std::fs::create_dir_all(dir.path()).unwrap();
    dir
  }

  pub fn path(&self) -> PathBuf { PathBuf::from(BASE).join("rebar-test").join(self.name) }
}

impl Drop for TempDir {
  fn drop(&mut self) {
    if !*KEEP_TEMP_DIR {
      let _ = std::fs::remove_dir_all(self.path());
    }
  }
}
