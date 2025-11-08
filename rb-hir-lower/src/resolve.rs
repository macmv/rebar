use std::collections::HashMap;

use rb_diagnostic::emit;
use rb_hir::{
  Environment, FunctionSpanMap, SpanMap,
  ast::{self as hir, Path},
};

struct Package {
  items: HashMap<Path, Item>,
}

enum Item {
  Function,
  Struct { functions: HashMap<String, Item> },
}

struct Resolver<'a> {
  env:      &'a Environment,
  package:  &'a Package,
  span_map: &'a SpanMap,
}

struct UseMap {
  uses: HashMap<String, Path>,
}

pub fn resolve_hir(env: &Environment, hir: &mut hir::Module, span_map: &SpanMap) {
  let mut package = Package { items: HashMap::new() };
  collect_structs(&mut package, &Path::new(), hir);
  collect_functions(&mut package, &Path::new(), hir);
  let _ = Resolver { env, package: &package, span_map }.resolve_module(hir, Path::new());
}

fn collect_structs(package: &mut Package, path: &Path, hir: &hir::Module) {
  for (name, module) in &hir.modules {
    match module {
      hir::PartialModule::File => panic!("module wasn't filled in"),
      hir::PartialModule::Inline(submodule) => {
        collect_structs(package, &path.join(name.clone()), submodule);
      }
    }
  }

  for s in hir.structs.values() {
    let path = path.join(s.name.clone());
    package.items.insert(path.clone(), Item::Struct { functions: HashMap::new() });
  }
}

fn collect_functions(package: &mut Package, path: &Path, hir: &hir::Module) {
  for (name, module) in &hir.modules {
    match module {
      hir::PartialModule::File => panic!("module wasn't filled in"),
      hir::PartialModule::Inline(submodule) => {
        collect_functions(package, &path.join(name.clone()), submodule);
      }
    }
  }

  for &id in &hir.standalone_functions {
    let function = &hir.functions[id];
    let path = path.join(function.name.clone());
    let prev = package.items.insert(path, Item::Function);

    if prev.is_some() {
      panic!();
    }
  }

  for imp in &hir.impls {
    match imp.struct_path {
      hir::TypeExpr::Struct(ref s) => {
        let struct_path = path.concat(s);
        match package.items.get_mut(&struct_path) {
          Some(Item::Struct { functions }) => {
            for &id in &imp.functions {
              let function = &hir.functions[id];
              let prev = functions.insert(function.name.clone(), Item::Function);
              if prev.is_some() {
                panic!("function `{}` is already defined for struct `{}`", function.name, s);
              }
            }
          }

          _ => panic!("impl for non-struct `{}`", s),
        }
      }
      _ => panic!(), // uhh
    }
  }
}

impl Resolver<'_> {
  fn resolve_module(&self, hir: &mut hir::Module, current: Path) -> Result<(), ()> {
    for (name, module) in &mut hir.modules {
      match module {
        hir::PartialModule::File => panic!("module wasn't filled in"),
        hir::PartialModule::Inline(submodule) => {
          let _ = self.resolve_module(submodule, current.join(name.clone()));
        }
      }
    }

    let span_map = &self.span_map.modules[&current];

    let uses = UseMap::collect(hir.uses.as_mut());

    for &id in &hir.standalone_functions {
      let function = &mut hir.functions[id];
      let span_map = &span_map.functions[&id];

      self.resolve_function(function, span_map, &current, &uses);
    }

    for imp in &mut hir.impls {
      assert!(imp.trait_path.is_none());

      match imp.struct_path {
        hir::TypeExpr::Struct(ref mut s) => {
          if self.package.contains(s) {
          } else if self.package.contains(&current.concat(s)) {
            *s = current.concat(s);
          } else {
            panic!("impl for unknown struct `{}`", s);
          }

          for &id in &imp.functions {
            let function = &mut hir.functions[id];
            let span_map = &span_map.functions[&id];

            self.resolve_function(function, span_map, &current, &uses);
          }
        }
        _ => panic!(), // uhh
      }
    }

    Ok(())
  }

  fn resolve_function(
    &self,
    function: &mut hir::Function,
    span_map: &FunctionSpanMap,
    current: &Path,
    uses: &UseMap,
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
            } else if let Some(path) = p.to_path().and_then(|p| uses.lookup(&p)) {
              // imported
              *p = hir::FullyQualifiedName::new_bare(path).unwrap();
            } else if self.env.lookup_type(p).is_some() {
              // absolute path
            } else if let Some(path) = p.to_path() {
              if self.package.contains(&path) {
                // absolute path
              } else if let Some(fqn) = self.env.resolve_trait_call(&path) {
                // absolute path via environment
                *p = fqn;
              } else {
                let abs = current.concat(&path);
                if self.package.contains(&abs) {
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

          hir::Expr::StructInit(p, _) => {
            if let Some(path) = uses.lookup(p) {
              // imported
              *p = path;
            } else {
              let abs = current.concat(&p);
              if self.package.contains(&abs) {
                // relative path
                *p = abs;
              } else {
                emit!(span_map[id] => format!("unresolved name `{p}`"));
              }
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

impl Package {
  pub fn contains(&self, path: &Path) -> bool { self.items.contains_key(path) }
}

impl UseMap {
  fn empty() -> Self { UseMap { uses: HashMap::new() } }

  fn prelude() -> Self {
    let mut uses = UseMap::empty();

    uses.add(Path::from(["sys", "assert"]));
    uses.add(Path::from(["sys", "assert_eq"]));

    uses
  }

  fn add(&mut self, path: Path) {
    let name = path.segments.last().unwrap().clone();
    self.uses.insert(name, path);
  }

  fn collect(uses: &[hir::Use]) -> Self {
    let mut map = UseMap::prelude();

    for u in uses {
      assert!(!u.is_glob);

      let name = u.alias.clone().unwrap_or_else(|| u.path.segments.last().unwrap().clone());
      map.uses.insert(name, u.path.clone());
    }

    map
  }

  fn lookup(&self, p: &Path) -> Option<Path> {
    let prefix = p.segments.first().unwrap();
    if let Some(resolved) = self.uses.get(prefix) {
      Some(resolved.concat_slice(&p.segments[1..]))
    } else {
      None
    }
  }
}

#[cfg(test)]
mod tests {
  use rb_hir::Environment;
  use rb_test::expect;

  fn check(src: &str, expected: rb_test::Expect) {
    let env = Environment::mini();
    let (_, hir, _) = crate::parse_body(&env, src);
    expected.assert_eq(&hir.functions.iter().next().unwrap().1.to_string());
  }

  #[test]
  fn expands_args() {
    check(
      r#"
      use sys::assert

      fn main(x: i32) {
        assert(x)
      }
      "#,
      expect![@r#"
        fn main(x: i32) {
          sys::assert(x)
        }"#],
    );
  }
}
