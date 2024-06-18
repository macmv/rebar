use crate::{CompletedMarker, Marker, T};

use super::*;

// test ok
// print("hello")
pub fn expr(p: &mut Parser) {
  let m = p.start();
  let Some(lhs) = atom_expr(p, m) else { return };

  lhs.pos;
}

fn atom_expr(p: &mut Parser, m: Marker) -> Option<CompletedMarker> {
  match p.current() {
    // test ok
    // 2.345
    t @ (T![ident] | T![integer] | T![float]) => {
      p.bump();
      Some(m.complete(p, t))
    }

    _ => {
      m.abandon(p);
      p.error(format!("expected expression, got {:?}", p.current()));
      None
    }
  }
}
