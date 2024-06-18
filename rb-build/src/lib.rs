mod ast_src;
mod sourcegen;
mod sourcegen_ast;

pub fn build_parser() { sourcegen_ast::sourcegen_kinds(); }
pub fn build_syntax() { sourcegen_ast::sourcegen_ast(); }
