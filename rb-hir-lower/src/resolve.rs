use std::collections::HashMap;

use rb_hir::ast::{self as hir, Path};

enum Item {
  Module { children: HashMap<String, Item> },
  Function,
}

pub fn resolve_hir(hir: &mut hir::Module) {
  let root = collect_module(hir);
  let _ = resolve_module(hir, &root, Path::new(), &root);
}

fn collect_module(hir: &hir::Module) -> Item {
  let mut children = HashMap::new();

  for (name, module) in &hir.modules {
    match module {
      hir::PartialModule::File => panic!("module wasn't filled in"),
      hir::PartialModule::Inline(submodule) => {
        children.insert(name.clone(), collect_module(submodule));
      }
    }
  }

  for function in hir.functions.values() {
    let prev = children.insert(function.name.clone(), Item::Function);

    if prev.is_some() {
      panic!();
    }
  }

  Item::Module { children }
}

fn resolve_module(
  hir: &mut hir::Module,
  root: &Item,
  current: Path,
  item: &Item,
) -> Result<(), ()> {
  for (name, module) in &mut hir.modules {
    match module {
      hir::PartialModule::File => panic!("module wasn't filled in"),
      hir::PartialModule::Inline(submodule) => {
        let child_item = item.get(name)?;
        let _ = resolve_module(submodule, root, current.join(name.clone()), child_item);
      }
    }
  }

  for function in hir.functions.values_mut() {
    for expr in function.exprs.values_mut() {
      match expr {
        hir::Expr::Name(p) => {
          if root.resolve(p).is_ok() {
            // absolute path
          } else {
            let abs = current.concat(p);
            if root.resolve(&abs).is_ok() {
              // relative path
              *p = abs;
            }
          }
        }

        _ => {}
      }
    }
  }

  Ok(())
}

impl Item {
  pub fn resolve(&self, path: &Path) -> Result<(), ()> {
    let mut current = self;
    for segment in &path.segments {
      current = current.get(segment)?;
    }
    Ok(())
  }

  pub fn get(&self, name: &str) -> Result<&Item, ()> {
    match self {
      Item::Module { children } => children.get(name).ok_or(()),
      Item::Function => Err(()),
    }
  }
}
