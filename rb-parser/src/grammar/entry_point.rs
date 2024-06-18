use super::*;

pub fn source_file(p: &mut Parser) {
  let m = p.start();

  while !p.at(EOF) {
    super::stmt::stmt(p);
  }

  m.complete(p, SOURCE_FILE);
}

pub fn expr(p: &mut Parser) { super::expr::expr(p); }
