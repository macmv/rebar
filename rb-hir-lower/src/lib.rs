//! Lowers the AST from rb_syntax into an HIR tree. Performs no type inferrence,
//! and only validates syntax.

use std::collections::HashMap;

use rb_diagnostic::{SourceId, Span, emit};
use rb_hir::{
  FunctionSpanMap, ModuleSpanMap,
  ast::{self as hir, Path, StringInterp},
};
use rb_syntax::{AstNode, SyntaxNodePtr, cst};

#[cfg(feature = "test")]
use rb_diagnostic::Sources;
#[cfg(feature = "test")]
use rb_hir::Environment;
#[cfg(feature = "test")]
use std::sync::Arc;

mod collect;
pub mod fs;
mod resolve;

pub use collect::{parse_hir, parse_source};
pub use fs::FileSystem;
pub use resolve::resolve_hir;

#[cfg(feature = "test")]
pub fn parse_body(env: &Environment, body: &str) -> (Arc<Sources>, hir::Function, FunctionSpanMap) {
  use rb_diagnostic::Source;

  let mut sources = Sources::new();
  let id = sources.add(Source::new("inline.rbr".to_string(), body.to_string()));
  let sources_arc = Arc::new(sources);
  let (func, span_map) = rb_diagnostic::run_or_exit(sources_arc.clone(), || {
    use rb_hir::SpanMap;

    let res = cst::SourceFile::parse(&body);
    if !res.errors().is_empty() {
      for error in res.errors() {
        emit!(Span { file: id, range: error.span() } => error.message());
      }
    }

    if !rb_diagnostic::is_ok() {
      return Default::default();
    }

    let (mut module, module_span_map, _) = crate::lower_source(res.tree(), id);
    if !rb_diagnostic::is_ok() {
      return Default::default();
    }

    let mut span_map = SpanMap::default();
    span_map.modules.insert(Path::new(), module_span_map);
    crate::resolve_hir(&env, &mut module, &span_map);
    let mut module_span_map = span_map.modules.remove(&Path::new()).unwrap();

    let function = module.functions[module.main_function.unwrap()].clone();
    let function_span_map =
      module_span_map.functions.remove(&module.main_function.unwrap()).unwrap();

    (function, function_span_map)
  });

  (sources_arc, func, span_map)
}

pub fn lower_source(
  cst: cst::SourceFile,
  source: SourceId,
) -> (hir::Module, ModuleSpanMap, Vec<AstIdMap>) {
  let mut out = hir::Module::default();
  let mut span_map = ModuleSpanMap::default();
  let mut ast_id_maps = vec![];

  let mut lower =
    ModuleLower { source, out: &mut out, span_map: &mut span_map, ast_id_maps: &mut ast_id_maps };
  let main = lower.source(&cst);

  out.main_function = Some(main);
  (out, span_map, ast_id_maps)
}

struct ModuleLower<'a> {
  source: SourceId,

  span_map:    &'a mut ModuleSpanMap,
  ast_id_maps: &'a mut Vec<AstIdMap>,
  out:         &'a mut hir::Module,
}

#[derive(Default)]
pub struct AstIdMap {
  pub exprs: HashMap<rb_syntax::SyntaxNodePtr, hir::ExprId>,
  pub stmts: HashMap<rb_syntax::SyntaxNodePtr, hir::StmtId>,
}

impl ModuleLower<'_> {
  fn source(&mut self, cst: &cst::SourceFile) -> hir::FunctionId {
    let mut func = hir::Function::default();
    let mut span_map = FunctionSpanMap::default();
    let mut ast_id_map = AstIdMap::default();
    let mut lower = FunctionLower {
      source:     self,
      f:          &mut func,
      span_map:   &mut span_map,
      ast_id_map: &mut ast_id_map,
    };

    let mut body = vec![];
    for stmt in cst.stmts() {
      let item = lower.stmt(stmt);
      body.push(item);
    }
    lower.f.body = Some(body);

    self.ast_id_maps.push(ast_id_map);
    let id = self.out.functions.alloc(func);
    self.span_map.functions.insert(id, span_map);
    id
  }

  fn function(&mut self, cst: &cst::Function) -> hir::FunctionId {
    let mut f = hir::Function::default();
    let mut span_map = FunctionSpanMap::default();
    let mut ast_id_map = AstIdMap::default();
    let mut lower = FunctionLower {
      source:     self,
      f:          &mut f,
      span_map:   &mut span_map,
      ast_id_map: &mut ast_id_map,
    };

    lower.span_map.name_span =
      Some(Span { file: lower.source.source, range: cst.ident_token().unwrap().text_range() });
    lower.f.name = cst.ident_token().unwrap().to_string();

    for attr in cst.attrs() {
      let path = attr.path().unwrap();
      match path {
        cst::Path::SimplePath(ref simple) => {
          // TODO: Use the path type!
          let name =
            simple.ident_tokens().map(|t| t.text().to_string()).collect::<Vec<_>>().join("::");

          lower.f.attrs.push(hir::Attribute { path: name });
        }
        _ => {
          panic!("only simple paths allowed in attributes");
        }
      }
    }

    for arg in cst.params().unwrap().params() {
      let name = arg.ident_token().unwrap().to_string();
      let ty = type_expr(lower.source.source, &arg.ty().unwrap());

      lower.f.sig.args.push((name, ty));
    }

    if let Some(ret) = cst.params().unwrap().return_type() {
      lower.f.sig.ret = type_expr(lower.source.source, &ret.ty().unwrap());
    }

    if let Some(block) = cst.block() {
      let mut body = vec![];
      for stmt in block.stmts() {
        let item = lower.stmt(stmt);
        body.push(item);
      }
      lower.f.body = Some(body);
    }

    self.ast_id_maps.push(ast_id_map);
    let id = self.out.functions.alloc(f);
    self.span_map.functions.insert(id, span_map);
    id
  }

  fn strct(&mut self, cst: &cst::Struct) -> hir::StructId {
    let mut s = hir::Struct::default();

    s.name = cst.ident_token().unwrap().to_string();

    for field in cst.struct_block().unwrap().fields() {
      let name = field.ident_token().unwrap().to_string();
      let ty = type_expr(self.source, &field.ty().unwrap());

      s.fields.push((name, ty));
    }

    self.out.structs.alloc(s)
  }
}

struct FunctionLower<'a, 'b> {
  source:     &'a mut ModuleLower<'b>,
  f:          &'a mut hir::Function,
  span_map:   &'a mut FunctionSpanMap,
  ast_id_map: &'a mut AstIdMap,
}

macro_rules! match_token {
  {
    match $id:ident {
      $($cst:ident($pat:pat) => $hir:expr,)*
    }
  } => {
    $(
      if let Some($pat) = $id.$cst() {
        $hir
      } else
    )* {
      panic!("unexpected token {}", $id)
    }
  };
}

impl FunctionLower<'_, '_> {
  fn stmt(&mut self, cst: cst::Stmt) -> hir::StmtId {
    let stmt = match cst {
      cst::Stmt::ExprStmt(ref expr) => {
        let expr = self.expr_opt(expr.expr());

        hir::Stmt::Expr(expr)
      }

      cst::Stmt::Let(ref let_stmt) => {
        let name = let_stmt.ident_token().unwrap().to_string();
        let expr = self.expr_opt(let_stmt.expr());

        let te = let_stmt.ty().map(|ty| type_expr(self.source.source, &ty));

        hir::Stmt::Let(name, None, te, expr)
      }

      // TODO: Allow inner defs to capture local variables.
      cst::Stmt::Function(ref def) => {
        self.source.function(def);

        let name = def.ident_token().unwrap().to_string();
        let args = def
          .params()
          .unwrap()
          .params()
          .map(|p| {
            (
              p.ident_token().unwrap().text().to_string(),
              type_expr(self.source.source, &p.ty().unwrap()),
            )
          })
          .collect();

        let ret = def
          .params()
          .unwrap()
          .return_type()
          .map(|ret| type_expr(self.source.source, &ret.ty().unwrap()));

        hir::Stmt::FunctionDef(hir::FunctionDef { name, args, ret })
      }

      cst::Stmt::Struct(ref strct) => {
        self.source.strct(strct);

        hir::Stmt::Struct
      }

      cst::Stmt::Mod(ref module) => {
        let name = module.ident_token().unwrap().to_string();

        let prev = self.source.out.modules.insert(name, hir::PartialModule::File);

        if prev.is_some() {
          emit!(
            Span { file: self.source.source, range: module.ident_token().unwrap().text_range() } =>
            "module already defined"
          );
        }

        hir::Stmt::Struct
      }

      cst::Stmt::Impl(ref imp) => {
        let first_ty = type_expr(self.source.source, &imp.first_ty().unwrap());
        let second_ty = imp.second_ty().map(|t| type_expr(self.source.source, &t));

        let (struct_path, trait_path) = if let Some(second_ty) = second_ty {
          match first_ty {
            hir::TypeExpr::Struct(ref p) => (second_ty, Some(p.clone())),
            _ => {
              emit!(
                Span { file: self.source.source, range: imp.first_ty().unwrap().syntax().text_range() } =>
                "expected a path type"
              );
              (second_ty, None)
            }
          }
        } else {
          (first_ty, None)
        };

        let functions = self.impl_block(imp.block().unwrap());
        self.source.out.impls.push(hir::Impl { struct_path, trait_path, functions });

        hir::Stmt::Struct
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    self.span_map.stmts.push(Span { file: self.source.source, range: cst.syntax().text_range() });
    let id = self.f.stmts.alloc(stmt);
    self.ast_id_map.stmts.insert(SyntaxNodePtr::new(cst.syntax()), id);

    if let cst::Stmt::Let(ref let_stmt) = cst {
      let span =
        Span { file: self.source.source, range: let_stmt.let_token().unwrap().text_range() };

      self.span_map.let_stmts.insert(id, span);
    }

    id
  }

  fn impl_block(&mut self, block: cst::Block) -> Vec<hir::FunctionId> {
    let mut functions = vec![];
    for stmt in block.stmts() {
      match stmt {
        cst::Stmt::Function(ref def) => {
          functions.push(self.source.function(def));
        }

        _ => {
          emit!(
            Span { file: self.source.source, range: stmt.syntax().text_range() } =>
            "only function definitions allowed in impl blocks"
          );
        }
      }
    }
    functions
  }

  #[track_caller]
  fn expr_opt(&mut self, cst: Option<cst::Expr>) -> hir::ExprId {
    match cst {
      Some(expr) => self.expr(expr),
      None => panic!("missing expression"),
    }
  }
  fn expr(&mut self, cst: cst::Expr) -> hir::ExprId {
    let expr = match cst {
      cst::Expr::Literal(ref lit) => {
        match_token! {
          match lit {
            integer_token(lit) => hir::Expr::Literal(hir::Literal::Int(lit.text().parse().unwrap())),
            true_token(_) => hir::Expr::Literal(hir::Literal::Bool(true)),
            false_token(_) => hir::Expr::Literal(hir::Literal::Bool(false)),
          }
        }
      }

      cst::Expr::String(ref lit) => {
        let start = lit.syntax().text_range().start();
        let text = lit.syntax().text().to_string();
        let span = Span { file: self.source.source, range: lit.syntax().text_range() };

        let mut segments = vec![];
        let mut prev = 1;

        for interp in lit.interpolations() {
          let left = u32::from(interp.syntax().text_range().start() - start) as usize;

          if left != prev {
            segments.push(StringInterp::Literal(parse_escapes(span, &text[prev..left])));
          }

          let expr = self.expr(interp.expr().unwrap());
          segments.push(StringInterp::Expr(expr));

          prev = u32::from(interp.syntax().text_range().end() - start) as usize;
        }

        segments.push(StringInterp::Literal(parse_escapes(span, &text[prev..text.len() - 1])));

        hir::Expr::String(segments)
      }

      cst::Expr::ArrayExpr(ref arr) => {
        let mut items = vec![];

        for expr in arr.exprs() {
          items.push(self.expr(expr));
        }

        hir::Expr::Array(items)
      }

      cst::Expr::PathExpr(ref path) => match path.path().unwrap() {
        cst::Path::FullyQualifiedPath(ref fq) => {
          let mut struct_path = Path::new();
          for tok in fq.struct_path().unwrap().ident_tokens() {
            struct_path.push(tok.text().to_string());
          }
          let mut trait_path = Path::new();
          for tok in fq.trait_path().unwrap().ident_tokens() {
            trait_path.push(tok.text().to_string());
          }

          hir::Expr::Name(hir::FullyQualifiedName::new_trait_impl(
            trait_path,
            struct_path,
            fq.ident_token().unwrap().text().to_string(),
          ))
        }
        cst::Path::SimplePath(ref simple) => {
          let mut p = Path::new();

          for tok in simple.ident_tokens() {
            p.push(tok.text().to_string());
          }

          hir::Expr::Name(hir::FullyQualifiedName::new_bare(p).unwrap())
        }
      },

      cst::Expr::Block(ref block) => {
        let mut stmts = vec![];
        for stmt in block.stmts() {
          stmts.push(self.stmt(stmt));
        }
        hir::Expr::Block(stmts)
      }

      cst::Expr::ParenExpr(ref expr) => {
        let expr = self.expr_opt(expr.expr());
        hir::Expr::Paren(expr)
      }

      cst::Expr::PrefixExpr(ref expr) => {
        let rhs = self.expr_opt(expr.expr());

        let op = unary_op_from_cst(&expr.prefix_op().unwrap());

        hir::Expr::UnaryOp(rhs, op)
      }

      cst::Expr::BinaryExpr(ref expr) => {
        let lhs = self.expr_opt(expr.lhs());
        let rhs = self.expr_opt(expr.rhs());

        let op = binary_op_from_cst(&expr.binary_op().unwrap());

        hir::Expr::BinaryOp(lhs, op, rhs)
      }

      cst::Expr::AsExpr(ref expr) => {
        let inner = self.expr_opt(expr.expr());
        let ty = type_expr(self.source.source, &expr.ty().unwrap());

        hir::Expr::Cast(inner, ty)
      }

      cst::Expr::IndexExpr(ref expr) => {
        let lhs = self.expr_opt(expr.lhs());
        let rhs = self.expr_opt(expr.rhs());

        hir::Expr::Index(lhs, rhs)
      }

      cst::Expr::FieldExpr(ref expr) => {
        let lhs = self.expr_opt(expr.expr());
        let field = expr.ident_token().unwrap().text().to_string();

        hir::Expr::Field(lhs, field)
      }

      cst::Expr::CallExpr(ref expr) => {
        let lhs = self.expr_opt(expr.expr());

        let Some(arg_list) = expr.arg_list() else {
          panic!("missing argument list {expr}");
        };

        let mut args = Vec::with_capacity(arg_list.exprs().size_hint().0);
        for arg in arg_list.exprs() {
          args.push(self.expr(arg));
        }

        hir::Expr::Call(lhs, args)
      }

      cst::Expr::IfExpr(ref expr) => hir::Expr::If {
        cond: self.expr_opt(expr.cond()),
        then: self.expr_opt(expr.then()),
        els:  expr.els().map(|e| self.expr(e)),
      },

      cst::Expr::StructExpr(ref expr) => match expr.path().unwrap() {
        cst::Path::SimplePath(simple) => {
          let mut p = Path::new();
          for tok in simple.ident_tokens() {
            p.push(tok.text().to_string());
          }

          let mut fields = Vec::with_capacity(expr.field_inits().size_hint().0);
          for field in expr.field_inits() {
            let name = field.ident_token().unwrap().to_string();
            let expr = self.expr(field.expr().unwrap());

            fields.push((name, expr));
          }

          hir::Expr::StructInit(p, fields)
        }
        _ => unreachable!("fully qualified paths not allowed in struct exprs"),
      },

      _ => unimplemented!("lowering for {:?}", cst),
    };

    self.span_map.exprs.push(Span { file: self.source.source, range: cst.syntax().text_range() });
    let id = self.f.exprs.alloc(expr);
    self.ast_id_map.exprs.insert(SyntaxNodePtr::new(cst.syntax()), id);

    match cst {
      cst::Expr::BinaryExpr(ref expr) => {
        let span = Span {
          file:  self.source.source,
          range: expr.binary_op().unwrap().syntax().text_range(),
        };

        self.span_map.binary_ops.insert(id, span);
      }
      cst::Expr::PrefixExpr(ref expr) => {
        let span = Span {
          file:  self.source.source,
          range: expr.prefix_op().unwrap().syntax().text_range(),
        };

        self.span_map.unary_ops.insert(id, span);
      }
      cst::Expr::IfExpr(ref expr) => {
        let if_span =
          Span { file: self.source.source, range: expr.if_token().unwrap().text_range() };
        let else_span =
          expr.else_token().map(|t| Span { file: self.source.source, range: t.text_range() });

        self.span_map.if_exprs.insert(id, (if_span, else_span));
      }

      _ => {}
    }

    id
  }
}

fn parse_escapes(span: Span, lit: &str) -> String {
  let mut out = String::new();
  let mut prev = '\n';
  let mut i = 0;
  let mut iter = lit.chars();

  while let Some(c) = iter.next() {
    if prev == '\\' {
      let c = match c {
        'n' => '\n',
        't' => '\t',
        'r' => '\r',
        '\\' => '\\',
        '"' => '"',
        'x' => {
          let c1 = iter.next();
          let c2 = iter.next();

          match [c1, c2] {
            [Some(c1 @ ('0'..='9' | 'a'..='f')), Some(c2 @ ('0'..='9' | 'a'..='f'))] => {
              char::from(c2.to_digit(16).unwrap() as u8 + (c1.to_digit(16).unwrap() as u8 * 16))
            }

            _ => {
              emit!(span.at_offset(i, 4) => "invalid escape sequence");
              continue;
            }
          }
        }
        _ => {
          emit!(span.at_offset(i, 2) => "unknown escape sequence");
          continue;
        }
      };

      out.pop();
      out.push(c);
    } else {
      out.push(c);
    }

    i += c.len_utf8() as u32;
    prev = c;
  }

  out
}

fn type_expr(source: SourceId, cst: &cst::Type) -> hir::TypeExpr {
  match cst {
    cst::Type::NameType(cst) => {
      let name = cst.ident_token().unwrap().text().to_string();

      match name.as_str() {
        "bool" => hir::PrimitiveType::Bool.into(),
        "str" => hir::PrimitiveType::Str.into(),
        "i8" => hir::PrimitiveType::I8.into(),
        "i16" => hir::PrimitiveType::I16.into(),
        "i32" => hir::PrimitiveType::I32.into(),
        "i64" => hir::PrimitiveType::I64.into(),
        "u8" => hir::PrimitiveType::U8.into(),
        "u16" => hir::PrimitiveType::U16.into(),
        "u32" => hir::PrimitiveType::U32.into(),
        "u64" => hir::PrimitiveType::U64.into(),
        _ => hir::TypeExpr::Struct(Path::new().join(name)),
      }
    }

    cst::Type::RefType(cst) => {
      let inner = type_expr(source, &cst.ty().unwrap());
      hir::TypeExpr::Ref(
        Box::new(inner),
        if cst.mut_token().is_some() { hir::Mutability::Mut } else { hir::Mutability::Imm },
      )
    }

    cst::Type::BinaryType(cst) => {
      let _lhs = type_expr(source, &cst.lhs().unwrap());
      let _rhs = type_expr(source, &cst.rhs().unwrap());

      todo!("unions!");
      // hir::TypeExpr::Union(vec![lhs, rhs])
    }

    cst::Type::NeverType(_) => hir::PrimitiveType::Never.into(),
  }
}

fn binary_op_from_cst(cst: &cst::BinaryOp) -> hir::BinaryOp {
  use hir::BinaryOp::*;

  match_token! {
    match cst {
      plus_token(_) => Add,
      minus_token(_) => Sub,
      star_token(_) => Mul,
      slash_token(_) => Div,
      percent_token(_) => Mod,
      eq_eq_token(_) => Eq,
      not_eq_token(_) => Neq,
      less_token(_) => Lt,
      less_eq_token(_) => Lte,
      greater_token(_) => Gt,
      greater_eq_token(_) => Gte,
      and_token(_) => And,
      or_token(_) => Or,
      bit_and_token(_) => BitAnd,
      bit_or_token(_) => BitOr,
      bit_xor_token(_) => Xor,
      shift_left_token(_) => ShiftLeft,
      shift_right_token(_) => ShiftRight,
    }
  }
}

fn unary_op_from_cst(cst: &cst::PrefixOp) -> hir::UnaryOp {
  use hir::UnaryOp::*;

  match_token! {
    match cst {
      minus_token(_) => Neg,
      bang_token(_) => Not,
    }
  }
}
