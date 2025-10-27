use std::sync::Arc;

use rb_diagnostic::{Diagnostic, Source, Sources};
use rb_hir::{ast as hir, SpanMap};
use rb_syntax::cst;

use crate::AstIdMap;

struct Collector {
  module:   hir::Module,
  errors:   Vec<Diagnostic>,
  to_check: Vec<hir::Path>,
}

pub fn parse_hir(path: &std::path::Path) -> (Sources, Result<hir::Module, Vec<Diagnostic>>) {
  let (mut sources, res) = parse_source(path, Sources::new());

  match res {
    Ok((module, _, _)) => {
      let mut collector =
        Collector { module, errors: vec![], to_check: vec![hir::Path { segments: vec![] }] };
      let root = path.parent().unwrap();
      while let Some(p) = collector.to_check.pop() {
        sources = collector.check(root, &p, sources);
      }

      if collector.errors.is_empty() {
        (sources, Ok(collector.module))
      } else {
        (sources, Err(collector.errors))
      }
    }
    Err(e) => (sources, Err(e)),
  }
}

impl Collector {
  fn check(&mut self, root: &std::path::Path, p: &hir::Path, mut sources: Sources) -> Sources {
    let mut module = &mut self.module;
    let mut path = hir::Path::new();
    let mut file_path = root.to_path_buf();
    for segment in &p.segments {
      match module.modules.iter_mut().find(|(n, _)| n == segment) {
        Some((_, hir::PartialModule::File(_))) => unreachable!("module wasn't filled in"),
        Some((_, hir::PartialModule::Inline(submodule))) => {
          path.segments.push(segment.clone());
          file_path.push(segment);
          module = submodule;
        }
        None => panic!("module {segment} not found"),
      }
    }

    for (_, module) in &mut module.modules {
      match module {
        hir::PartialModule::File(name) => {
          let (new_sources, res) = parse_source(&file_path.join(format!("{name}.rbr")), sources);
          sources = new_sources;

          match res {
            Ok((m, _, _)) => {
              let mut p = p.clone();
              p.segments.push(name.clone());
              self.to_check.push(p);

              *module = hir::PartialModule::Inline(m)
            }
            Err(e) => self.errors.extend(e),
          }
        }
        hir::PartialModule::Inline(_) => {}
      }
    }

    sources
  }
}

fn parse_source(
  path: &std::path::Path,
  mut sources: Sources,
) -> (Sources, Result<(hir::Module, SpanMap, Vec<AstIdMap>), Vec<Diagnostic>>) {
  let content = std::fs::read_to_string(&path).unwrap();
  let id = sources.add(Source::new(path.display().to_string(), content));

  let src = sources.get(id);
  let res = cst::SourceFile::parse(&src.source);
  let sources_arc = Arc::new(sources);
  let res = rb_diagnostic::run(sources_arc.clone(), || crate::lower_source(res.tree(), id));
  sources = Arc::try_unwrap(sources_arc).unwrap_or_else(|_| panic!());

  (sources, res)
}
