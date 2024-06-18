use crate::{CompletedMarker, Marker, T};

use super::*;

// test ok
// 2 + 3
// print("hello")
pub fn expr(p: &mut Parser) {
  let m = p.start();
  let Some(lhs) = atom_expr(p, m) else { return };

  lhs.pos;
}

fn atom_expr(p: &mut Parser, m: Marker) -> Option<CompletedMarker> {
  match p.current() {
    INT_NUMBER => {
      p.eat(INT_NUMBER);
      Some(m.complete(p, INT_NUMBER))
    }

    _ => {
      m.abandon(p);
      p.error(format!("expected expression, got {:?}", p.current()));
      None
    }
  }
}
