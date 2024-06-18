use crate::{Parser, T};

pub fn stmt(p: &mut Parser) {
  match p.current() {
    _ => super::expr::expr(p),
  }

  // test err
  // foo bar
  if p.current() != T![nl] {
    p.error("expected end of statement");
  }
  while p.current() != T![nl] {
    p.bump();
  }
  p.eat(T![nl]);
}
