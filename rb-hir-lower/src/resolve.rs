use std::collections::HashMap;

use rb_diagnostic::emit;
use rb_hir::{
  Environment, FunctionSpanMap, SpanMap,
  ast::{self as hir, Path},
};

enum Item {
  Module { children: HashMap<String, Item> },
  Function,
}

struct Resolver<'a> {
  env:      &'a Environment,
  root:     &'a Item,
  span_map: &'a SpanMap,
}

pub fn resolve_hir(env: &Environment, hir: &mut hir::Module, span_map: &SpanMap) {
  let root = collect_module(hir);
  let _ = Resolver { env, root: &root, span_map }.resolve_module(hir, Path::new(), &root);
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

impl Resolver<'_> {
  fn resolve_module(&self, hir: &mut hir::Module, current: Path, item: &Item) -> Result<(), ()> {
    for (name, module) in &mut hir.modules {
      match module {
        hir::PartialModule::File => panic!("module wasn't filled in"),
        hir::PartialModule::Inline(submodule) => {
          let child_item = item.get(name).unwrap();
          let _ = self.resolve_module(submodule, current.join(name.clone()), child_item);
        }
      }
    }

    let span_map = &self.span_map.modules[&current];

    for (id, function) in hir.functions.iter_mut() {
      let span_map = &span_map.functions[&id];

      self.resolve_function(function, span_map, &current);
    }

    Ok(())
  }

  fn resolve_function(
    &self,
    function: &mut hir::Function,
    span_map: &FunctionSpanMap,
    current: &Path,
  ) {
    let Some(ref body) = function.body else { return };

    let mut expr = 0;
    let mut locals = HashMap::<String, hir::LocalId>::new();

    for (arg, ty) in &function.sig.args {
      let id = function.locals.alloc(hir::Local { name: arg.to_string(), ty: Some(ty.clone()) });
      locals.insert(arg.clone(), id);
    }

    let mut walk_until = |locals: &HashMap<String, hir::LocalId>, e: hir::ExprId| {
      let mut id = hir::ExprId::from_raw(expr.into());
      while id <= e {
        match &mut function.exprs[id] {
          hir::Expr::Name(p) => {
            if let Some(ident) = p.as_single()
              && let Some(&local) = locals.get(ident)
            {
              // local variable
              function.exprs[id] = hir::Expr::Local(local);
            } else if self.env.lookup_type(p).is_some() {
              // absolute path
            } else if let Some(path) = p.to_path() {
              if self.root.contains(&path) {
                // absolute path
              } else if let Some(fqn) = self.env.resolve_trait_call(&path) {
                // absolute path via environment
                *p = fqn;
              } else {
                let abs = current.concat(&path);
                if self.root.contains(&abs) {
                  // relative path
                  *p = hir::FullyQualifiedName::new_bare(abs).unwrap();
                } else {
                  emit!(span_map[id] => format!("unresolved name `{p}`"));
                }
              }
            } else {
              emit!(span_map[id] => format!("unresolved name `{p}`"));
            }
          }

          _ => {}
        }

        expr += 1;
        id = hir::ExprId::from_raw(expr.into());
      }
    };

    for &item in body {
      match function.stmts[item] {
        hir::Stmt::Expr(e) => walk_until(&locals, e),
        hir::Stmt::Let(ref name, ref mut id, ref te, e) => {
          walk_until(&locals, e);

          let local =
            function.locals.alloc(hir::Local { name: name.to_string(), ty: te.clone() });
          *id = Some(local);
          locals.insert(name.clone(), local);
        }

        _ => {}
      }
    }
  }
}

impl Item {
  pub fn contains(&self, path: &Path) -> bool {
    let mut current = self;
    for segment in &path.segments {
      match current.get(segment) {
        Some(it) => current = it,
        None => return false,
      }
    }
    true
  }

  pub fn get(&self, name: &str) -> Option<&Item> {
    match self {
      Item::Module { children } => children.get(name),
      Item::Function => None,
    }
  }
}
