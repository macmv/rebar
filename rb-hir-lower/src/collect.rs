use std::{collections::HashMap, sync::Arc};

use rb_diagnostic::{Diagnostic, Source, Sources, Span};
use rb_hir::{ModuleSpanMap, SpanMap, ast as hir};
use rb_syntax::cst;

use crate::{AstIdMap, FileSystem};

struct Collector<'a, F: FileSystem> {
  fs:       &'a F,
  module:   hir::Module,
  span_map: SpanMap,

  errors:   Vec<Diagnostic>,
  to_check: Vec<hir::Path>,
}

pub fn parse_hir(
  fs: &impl FileSystem,
  path: &std::path::Path,
) -> (Sources, Result<(hir::Module, SpanMap), Vec<Diagnostic>>) {
  let (mut sources, res) = parse_source(fs, path, Sources::new());

  match res {
    Ok((module, span_map, _)) => {
      let mut collector = Collector {
        fs,
        module,
        span_map: SpanMap { modules: HashMap::new() },
        errors: vec![],
        to_check: vec![hir::Path { segments: vec![] }],
      };
      collector
        .span_map
        .modules
        .insert(hir::Path { segments: vec![] }, ModuleSpanMap { functions: span_map.functions });

      let root = path.parent().unwrap();
      while let Some(p) = collector.to_check.pop() {
        sources = collector.check(root, &p, sources);
      }

      if collector.errors.is_empty() {
        (sources, Ok((collector.module, collector.span_map)))
      } else {
        (sources, Err(collector.errors))
      }
    }
    Err(e) => (sources, Err(e)),
  }
}

impl<F: FileSystem> Collector<'_, F> {
  fn check(&mut self, root: &std::path::Path, p: &hir::Path, mut sources: Sources) -> Sources {
    let mut module = &mut self.module;
    let mut path = hir::Path::new();
    let mut file_path = root.to_path_buf();
    for segment in &p.segments {
      match module.modules.get_mut(segment) {
        Some(hir::PartialModule::File) => unreachable!("module wasn't filled in"),
        Some(hir::PartialModule::Inline(submodule)) => {
          path.segments.push(segment.clone());
          file_path.push(segment);
          module = submodule;
        }
        None => panic!("module {segment} not found"),
      }
    }

    for (name, module) in &mut module.modules {
      match module {
        hir::PartialModule::File => {
          let (new_sources, res) =
            parse_source(self.fs, &file_path.join(format!("{name}.rbr")), sources);
          sources = new_sources;

          match res {
            Ok((m, span_map, _)) => {
              let mut p = p.clone();
              p.segments.push(name.clone());
              self
                .span_map
                .modules
                .insert(p.clone(), ModuleSpanMap { functions: span_map.functions });
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

pub fn parse_source(
  fs: &impl crate::FileSystem,
  path: &std::path::Path,
  mut sources: Sources,
) -> (Sources, Result<(hir::Module, ModuleSpanMap, Vec<AstIdMap>), Vec<Diagnostic>>) {
  let content = fs.read_to_string(&path).unwrap();
  let id = sources.add(Source::new(path.display().to_string(), content));

  let src = sources.get(id);
  let res = cst::SourceFile::parse(&src.source);
  if !res.errors().is_empty() {
    return (
      sources,
      Err(
        res
          .errors()
          .into_iter()
          .map(|e| Diagnostic::error(e.message(), Span { file: id, range: e.span() }))
          .collect(),
      ),
    );
  }
  let sources_arc = Arc::new(sources);
  let res = rb_diagnostic::run(sources_arc.clone(), || crate::lower_source(res.tree(), id));
  sources = Arc::try_unwrap(sources_arc).unwrap_or_else(|_| panic!());

  (sources, res)
}
