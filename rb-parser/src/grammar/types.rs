use crate::{
  CompletedMarker, Marker, Parser,
  SyntaxKind::{self, *},
  T,
};

pub fn ty(p: &mut Parser) { ty_bp(p, 0); }

fn op_bp(t: SyntaxKind) -> Option<(u8, u8)> {
  // test ok
  // fn foo(a: int | str) {}
  let prec = match t {
    T![|] => 1,

    _ => return None,
  };

  let is_right_assoc = false;

  if is_right_assoc { Some((prec, prec)) } else { Some((prec, prec + 1)) }
}

fn ty_bp(p: &mut Parser, min_bp: u8) {
  let m = p.start();
  let Some(mut lhs) = atom_type(p, m) else { return };

  loop {
    if let Some((l_bp, r_bp)) = op_bp(p.current()) {
      if l_bp < min_bp {
        return;
      }

      let m = lhs.precede(p);

      {
        let m = p.start();
        p.bump(); // eat the operator
        m.complete(p, TYPE_OP);
      }

      ty_bp(p, r_bp);
      lhs = m.complete(p, BINARY_TYPE);
    } else {
      match p.current() {
        T![nl] | T![for] | T![=] | T![,] | T!['{'] | T![')'] | T!['}'] | EOF => return,
        _ => {
          p.error(format!("expected type, got {}", p.current()));
          return;
        }
      }
    }
  }
}

fn atom_type(p: &mut Parser, m: Marker) -> Option<CompletedMarker> {
  match p.current() {
    // test ok
    // fn foo(a: int) {}
    // fn foo(a: nil) {}
    T![ident] => {
      p.bump();
      Some(m.complete(p, NAME_TYPE))
    }

    // test ok
    // fn bar() -> ! {}
    T![!] => {
      p.eat(T![!]);
      Some(m.complete(p, NEVER_TYPE))
    }

    // test ok
    // fn foo(a: &i32) {}
    T![&] => {
      p.eat(T![&]);
      // test ok
      // fn bar(a: &mut i32) {}
      if p.at(T![mut]) {
        p.eat(T![mut]);
      }

      {
        let m = p.start();
        atom_type(p, m)?;
      }
      Some(m.complete(p, REF_TYPE))
    }

    _ => {
      m.abandon(p);
      p.error("expected type");

      None
    }
  }
}
