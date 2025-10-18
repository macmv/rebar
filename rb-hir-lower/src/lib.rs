//! Lowers the AST from rb_syntax into an HIR tree. Performs no type inferrence,
//! and only validates syntax.

use rb_diagnostic::{emit, SourceId, Span};
use rb_hir::{
  ast::{self as hir, StringInterp},
  SpanMap,
};
use rb_syntax::{cst, AstNode};

pub fn lower_source(cst: cst::SourceFile, source: SourceId) -> (hir::SourceFile, Vec<SpanMap>) {
  let mut out = hir::SourceFile::default();
  let mut span_maps = vec![];

  let mut lower = SourceLower { source, out: &mut out, span_maps: &mut span_maps };
  let main = lower.source(&cst);

  out.main_function = Some(main);
  (out, span_maps)
}

struct SourceLower<'a> {
  source:    SourceId,
  span_maps: &'a mut Vec<SpanMap>,
  out:       &'a mut hir::SourceFile,
}

impl SourceLower<'_> {
  fn source(&mut self, cst: &cst::SourceFile) -> hir::FunctionId {
    let mut func = hir::Function::default();
    let mut span_map = SpanMap::default();
    let mut lower = FunctionLower { source: self, f: &mut func, span_map: &mut span_map };

    for stmt in cst.stmts() {
      let item = lower.stmt(stmt);
      lower.f.items.push(item);
    }

    self.span_maps.push(span_map);
    self.out.functions.alloc(func)
  }

  fn function(&mut self, cst: &cst::FunctionDef) -> hir::FunctionId {
    let mut f = hir::Function::default();
    let mut span_map = SpanMap::default();
    let mut lower = FunctionLower { source: self, f: &mut f, span_map: &mut span_map };

    lower.f.name = cst.ident_token().unwrap().to_string();

    for arg in cst.params().unwrap().params() {
      let name = arg.ident_token().unwrap().to_string();
      let ty = type_expr(lower.source.source, &arg.ty().unwrap());

      lower.f.args.push((name, ty));
    }

    if let Some(block) = cst.block() {
      for stmt in block.stmts() {
        let item = lower.stmt(stmt);
        lower.f.items.push(item);
      }
    }

    self.span_maps.push(span_map);
    self.out.functions.alloc(f)
  }

  fn strct(&mut self, cst: &cst::Struct) -> hir::StructId {
    let mut s = hir::Struct::default();

    s.name = cst.ident_token().unwrap().to_string();

    for item in cst.struct_block().unwrap().struct_items() {
      match item {
        cst::StructItem::Field(ref field) => {
          let name = field.ident_token().unwrap().to_string();
          let ty = type_expr(self.source, &field.ty().unwrap());

          s.fields.push((name, ty));
        }
        _ => {}
      }
    }

    self.out.structs.alloc(s)
  }
}

struct FunctionLower<'a, 'b> {
  source:   &'a mut SourceLower<'b>,
  f:        &'a mut hir::Function,
  span_map: &'a mut SpanMap,
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

        hir::Stmt::Let(name, expr)
      }

      // TODO: Allow inner defs to capture local variables.
      cst::Stmt::FunctionDef(ref def) => {
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

        hir::Stmt::FunctionDef(hir::FunctionDef { name, args, ret: None })
      }

      cst::Stmt::Struct(ref strct) => {
        self.source.strct(strct);

        hir::Stmt::Struct
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    self.span_map.stmts.push(Span { file: self.source.source, range: cst.syntax().text_range() });
    let id = self.f.stmts.alloc(stmt);

    match cst {
      cst::Stmt::Let(ref let_stmt) => {
        let span =
          Span { file: self.source.source, range: let_stmt.let_token().unwrap().text_range() };

        self.span_map.let_stmts.insert(id, span);
      }

      _ => {}
    }

    id
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
            nil_token(_) => hir::Expr::Literal(hir::Literal::Nil),
          }
        }
      }

      cst::Expr::String(ref lit) => {
        let start = lit.syntax().text_range().start();
        let text = lit.syntax().text().to_string();

        let mut segments = vec![];
        let mut prev = 1;

        for escape in lit.interpolations() {
          let left = u32::from(escape.syntax().text_range().start() - start) as usize;

          if left != prev {
            segments.push(StringInterp::Literal(text[prev..left].to_string()));
          }

          let expr = self.expr(escape.expr().unwrap());
          segments.push(StringInterp::Expr(expr));

          prev = u32::from(escape.syntax().text_range().end() - start) as usize;
        }

        segments.push(StringInterp::Literal(text[prev..text.len() - 1].to_string()));

        hir::Expr::String(segments)
      }

      cst::Expr::ArrayExpr(ref arr) => {
        let mut items = vec![];

        for expr in arr.exprs() {
          items.push(self.expr(expr));
        }

        hir::Expr::Array(items)
      }

      cst::Expr::Name(ref name) => {
        let name = name.ident_token().unwrap().to_string();

        hir::Expr::Name(name)
      }

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

      cst::Expr::IndexExpr(ref expr) => {
        let lhs = self.expr_opt(expr.lhs());
        let rhs = self.expr_opt(expr.rhs());

        hir::Expr::Index(lhs, rhs)
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

      cst::Expr::StructExpr(ref expr) => {
        // TODO: Names should get resolved here.
        let name = match expr.expr().unwrap() {
          cst::Expr::Name(ref name) => name.ident_token().unwrap().to_string(),
          _ => unreachable!(),
        };

        let mut fields = Vec::with_capacity(expr.field_inits().size_hint().0);
        for field in expr.field_inits() {
          let name = field.ident_token().unwrap().to_string();
          let expr = self.expr(field.expr().unwrap());

          fields.push((name, expr));
        }

        hir::Expr::StructInit(name, fields)
      }

      _ => unimplemented!("lowering for {:?}", cst),
    };

    self.span_map.exprs.push(Span { file: self.source.source, range: cst.syntax().text_range() });
    let id = self.f.exprs.alloc(expr);

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

fn type_expr(source: SourceId, cst: &cst::Type) -> hir::TypeExpr {
  match cst {
    cst::Type::NameType(cst) => {
      if let Some(_) = cst.nil_token() {
        hir::TypeExpr::Nil
      } else {
        let name = cst.ident_token().unwrap().text().to_string();

        match name.as_str() {
          "nil" => hir::TypeExpr::Nil,
          "bool" => hir::TypeExpr::Bool,
          "int" => hir::TypeExpr::Int,
          "str" => hir::TypeExpr::Str,
          _ => {
            emit!(
              format!("unknown type {name}"),
              Span { file: source, range: cst.ident_token().unwrap().text_range() }
            );
            hir::TypeExpr::Nil
          }
        }
      }
    }

    cst::Type::BinaryType(cst) => {
      let lhs = type_expr(source, &cst.lhs().unwrap());
      let rhs = type_expr(source, &cst.rhs().unwrap());

      hir::TypeExpr::Union(vec![lhs, rhs])
    }
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
