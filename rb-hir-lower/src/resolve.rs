use std::collections::HashMap;

use rb_diagnostic::emit;
use rb_hir::{
  ast::{self as hir, Path},
  SpanMap,
};

enum Item {
  Module { children: HashMap<String, Item> },
  Function,
}

pub fn resolve_hir(hir: &mut hir::Module, span_map: &SpanMap) {
  let root = collect_module(hir);
  let _ = resolve_module(hir, &root, span_map, Path::new(), &root);
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
  span_map: &SpanMap,
  current: Path,
  item: &Item,
) -> Result<(), ()> {
  for (name, module) in &mut hir.modules {
    match module {
      hir::PartialModule::File => panic!("module wasn't filled in"),
      hir::PartialModule::Inline(submodule) => {
        let child_item = item.get(name)?;
        let _ = resolve_module(submodule, root, span_map, current.join(name.clone()), child_item);
      }
    }
  }

  let span_map = &span_map.modules[&current];

  for (id, function) in hir.functions.iter_mut() {
    let span_map = &span_map.functions[&id];
    for (id, expr) in function.exprs.iter_mut() {
      match expr {
        hir::Expr::Name(p) => {
          if root.resolve(p).is_ok() {
            // absolute path
          } else {
            let abs = current.concat(p);
            if root.resolve(&abs).is_ok() {
              // relative path
              *p = abs;
            } else {
              emit!(span_map[id] => format!("unresolved name `{p}`"));
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
