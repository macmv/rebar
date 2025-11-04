use crate::{CompletedMarker, Marker, SyntaxKind, T};

use super::*;

pub fn expr(p: &mut Parser) { expr_bp(p, 0, false); }

fn expr_cond(p: &mut Parser) { expr_bp(p, 0, true); }

fn op_bp(t: SyntaxKind) -> Option<(u8, u8)> {
  // test ok
  // 1 + 2 - 3 * 4 / 5 % 0 == 6 != 7 < 8 > 9 <= 10 >= 11 && 12 || 13 << 14 >> 15
  let prec = match t {
    T![||] | T![&&] => 1,
    T![|] => 2,
    T![^] => 3,
    T![&] => 4,
    T![==] | T![!=] => 5,
    T![<] | T![>] | T![<=] | T![>=] => 6,
    T![<<] | T![>>] => 7,
    T![+] | T![-] => 8,
    T![*] | T![/] | T![%] => 9,

    _ => return None,
  };

  let is_right_assoc = false;

  if is_right_assoc { Some((prec, prec)) } else { Some((prec, prec + 1)) }
}

fn expr_bp(p: &mut Parser, min_bp: u8, cond: bool) {
  let m = p.start();
  let Some(mut lhs) = atom_expr(p, m, cond) else { return };
  lhs = postfix_expr(p, lhs);

  loop {
    if let Some((l_bp, r_bp)) = op_bp(p.current()) {
      if l_bp < min_bp {
        return;
      }

      let m = lhs.precede(p);

      {
        let m = p.start();
        p.bump(); // eat the operator
        m.complete(p, BINARY_OP);
      }

      expr_bp(p, r_bp, cond);
      lhs = m.complete(p, BINARY_EXPR);
    } else {
      match p.current() {
        T![nl] | T![,] | T![')'] | T![']'] | T!['}'] | EOF => return,
        T!['{'] if cond => return,
        _ => {
          p.error(format!("expected operator, got {}", p.current()));
          return;
        }
      }
    }
  }
}

pub fn path(p: &mut Parser) -> (CompletedMarker, bool) {
  if p.at(T![<]) {
    let m = p.start();
    p.eat(T![<]);
    // test ok
    // <foo::bar as std::op::Add>::foo
    simple_path(p);
    p.expect(T![as]);
    simple_path(p);
    p.expect(T![>]);
    p.expect(T![::]);
    p.expect(T![ident]);
    (m.complete(p, FULLY_QUALIFIED_PATH), false)
  } else {
    (simple_path(p), true)
  }
}

fn simple_path(p: &mut Parser) -> CompletedMarker {
  let m = p.start();
  p.expect(T![ident]);

  while p.at(T![::]) {
    p.eat(T![::]);
    p.expect(T![ident]);
  }

  m.complete(p, SIMPLE_PATH)
}

fn atom_expr(p: &mut Parser, m: Marker, cond: bool) -> Option<CompletedMarker> {
  match p.current() {
    // test ok
    // 2
    // 2.345
    T![integer] | T![float] | T![true] | T![false] => {
      p.bump();
      Some(m.complete(p, LITERAL))
    }

    // test ok
    // hello
    T![ident] => {
      let (_, is_simple) = path(p);
      let lhs = m.complete(p, PATH_EXPR);

      // Special case for struct literals.
      if is_simple && p.current() == T!['{'] && !cond {
        // test ok
        // Foo { a: 2 }
        // if a { println() }
        let strct = lhs.precede(p);

        arg_list(p, T!['{'], T!['}'], |p| {
          let m = p.start();
          p.expect(T![ident]);
          p.expect(T![:]);
          expr(p);
          m.complete(p, FIELD_INIT);
        });

        Some(strct.complete(p, STRUCT_EXPR))
      } else {
        Some(lhs)
      }
    }

    // test ok
    // <i32 as std::op::Add>::add(3)
    T![<] => {
      path(p);
      Some(m.complete(p, PATH_EXPR))
    }

    // test ok
    // print("hello world!")
    T!['"'] => {
      string(p);
      Some(m.complete(p, STRING))
    }

    // test ok
    // !!false
    // -true
    T![!] | T![-] => {
      {
        let m = p.start();
        p.bump();
        m.complete(p, PREFIX_OP);
      }
      // if !foo { println() }
      expr_bp(p, 0, cond);
      Some(m.complete(p, PREFIX_EXPR))
    }

    // test ok
    // (2 + 3)
    // -(4 - 5)
    T!['('] => {
      p.eat(T!['(']);
      expr(p);
      p.expect(T![')']);
      Some(m.complete(p, PAREN_EXPR))
    }

    // test ok
    // []
    // [1, 2, 3]
    T!['['] => {
      arg_list(p, T!['['], T![']'], expr);
      Some(m.complete(p, ARRAY_EXPR))
    }

    // test ok
    // {
    //   print("hello")
    //   print("goodbye")
    // }
    T!['{'] => {
      m.abandon(p);
      Some(super::stmt::block(p))
    }

    T![if] => {
      p.eat(T![if]);
      expr_cond(p);

      // test ok
      // if 1 { print("hello") }
      super::stmt::block(p);

      while p.at(T![else]) {
        p.eat(T![else]);

        if p.at(T![if]) {
          p.eat(T![if]);
          // test ok
          // if 1 { print("hello") } else if 2 { print("bye") }
          // if 1 { print("hello") } else if 2 { print("bye") } else { print("ok") }
          expr_cond(p);
          super::stmt::block(p);
        } else {
          // test ok
          // if 1 { print("hello") } else { print("bye") }
          super::stmt::block(p);
          break;
        }
      }

      Some(m.complete(p, IF_EXPR))
    }

    _ => {
      m.abandon(p);
      p.error(format!("expected expression, got {}", p.current()));

      // Advance to avoid infinite loop.
      p.bump();

      None
    }
  }
}

pub fn string(p: &mut Parser) {
  p.eat(T!['"']);

  // TODO: Escapes and such.
  while !p.at(EOF) && !p.at(T!['"']) {
    if p.at(T![#]) && p.peek() == T!['{'] {
      let m = p.start();
      p.eat(T![#]);
      p.eat(T!['{']);
      expr(p);
      p.expect(T!['}']);
      m.complete(p, INTERPOLATION);
    } else {
      p.bump();
    }
  }

  p.eat(T!['"']);
}

fn postfix_expr(p: &mut Parser, mut lhs: CompletedMarker) -> CompletedMarker {
  loop {
    lhs = match p.current() {
      // test ok
      // foo.bar()
      // foo.baz[3]
      T![.] => {
        let m = lhs.precede(p);
        p.eat(T![.]);
        p.expect(T![ident]);
        m.complete(p, FIELD_EXPR)
      }

      // test ok
      // hi(3)
      // hello(2, 3)(4)
      T!['('] => {
        let call = lhs.precede(p);

        let m = p.start();
        arg_list(p, T!['('], T![')'], expr);
        m.complete(p, ARG_LIST);

        call.complete(p, CALL_EXPR)
      }

      // test ok
      // foo[4]
      // bar(3)[4][5](6)[7]
      T!['['] => {
        let call = lhs.precede(p);

        p.eat(T!['[']);

        // test ok
        // foo[
        //   2]
        while p.at(T![nl]) {
          p.eat(T![nl]);
        }

        expr(p);

        // test ok
        // foo[
        //   2
        // ]
        while p.at(T![nl]) {
          p.eat(T![nl]);
        }

        p.expect(T![']']);

        call.complete(p, INDEX_EXPR)
      }

      // test ok
      // 3 as i32
      T![as] => {
        let m = lhs.precede(p);
        p.eat(T![as]);
        super::types::ty(p);
        m.complete(p, AS_EXPR)
      }

      _ => break,
    };
  }
  lhs
}

fn arg_list(p: &mut Parser, open: SyntaxKind, close: SyntaxKind, elem: impl Fn(&mut Parser)) {
  p.eat(open);

  while !p.at(EOF) && !p.at(close) {
    // test ok
    // foo(
    //   2)
    while p.at(T![nl]) {
      p.eat(T![nl]);
    }

    elem(p);

    // test ok
    // foo(
    //   2
    //   ,
    //   3
    // )
    while p.at(T![nl]) {
      p.eat(T![nl]);
    }

    if p.at(T![,]) {
      p.eat(T![,]);

      // test ok
      // foo(2
      // )
      // foo(
      //   2
      // )
      while p.at(T![nl]) {
        p.eat(T![nl]);
      }
      if p.at(close) {
        break;
      }
    } else {
      break;
    }
  }

  p.expect(close);
}

#[cfg(test)]
mod tests {
  use crate::tests::{check, check_expr};

  #[test]
  fn it_works() {
    check(
      r#"
        print("hello world!")
        print(2 + 3)
      "#,
      expect![@r#"
        SOURCE_FILE
          NL_KW '\n'
          WHITESPACE '        '
          EXPR_STMT
            CALL_EXPR
              PATH_EXPR
                SIMPLE_PATH
                  IDENT 'print'
              ARG_LIST
                OPEN_PAREN '('
                STRING
                  DOUBLE_QUOTE '"'
                  IDENT 'hello'
                  WHITESPACE ' '
                  IDENT 'world'
                  BANG '!'
                  DOUBLE_QUOTE '"'
                CLOSE_PAREN ')'
          NL_KW '\n'
          WHITESPACE '        '
          EXPR_STMT
            CALL_EXPR
              PATH_EXPR
                SIMPLE_PATH
                  IDENT 'print'
              ARG_LIST
                OPEN_PAREN '('
                BINARY_EXPR
                  LITERAL
                    INTEGER_KW '2'
                  WHITESPACE ' '
                  BINARY_OP
                    PLUS '+'
                  WHITESPACE ' '
                  LITERAL
                    INTEGER_KW '3'
                CLOSE_PAREN ')'
          NL_KW '\n'
          WHITESPACE '      '
      "#],
    );
  }

  #[test]
  fn literals() {
    check_expr(
      "1",
      expect![@r#"
        LITERAL
          INTEGER_KW '1'
      "#],
    );

    check_expr(
      "2.234",
      expect![@r#"
        LITERAL
          FLOAT_KW '2.234'
      "#],
    );

    check_expr(
      "true",
      expect![@r#"
        LITERAL
          TRUE_KW 'true'
      "#],
    );

    check_expr(
      "false",
      expect![@r#"
        LITERAL
          FALSE_KW 'false'
      "#],
    );
  }

  #[test]
  fn string_interpolation() {
    check(
      r#"
        "hello #{world}"
      "#,
      expect![@r#"
        SOURCE_FILE
          NL_KW '\n'
          WHITESPACE '        '
          EXPR_STMT
            STRING
              DOUBLE_QUOTE '"'
              IDENT 'hello'
              WHITESPACE ' '
              INTERPOLATION
                POUND '#'
                OPEN_CURLY '{'
                PATH_EXPR
                  SIMPLE_PATH
                    IDENT 'world'
                CLOSE_CURLY '}'
              DOUBLE_QUOTE '"'
          NL_KW '\n'
          WHITESPACE '      '
      "#],
    );
  }

  #[test]
  fn fully_qualified_path() {
    check(
      r#"
        <foo::bar as std::op::Add>::add(3)
      "#,
      expect![@r#"
        SOURCE_FILE
          NL_KW '\n'
          WHITESPACE '        '
          EXPR_STMT
            CALL_EXPR
              PATH_EXPR
                FULLY_QUALIFIED_PATH
                  LESS '<'
                  SIMPLE_PATH
                    IDENT 'foo'
                    COLON_COLON '::'
                    IDENT 'bar'
                  WHITESPACE ' '
                  AS_KW 'as'
                  WHITESPACE ' '
                  SIMPLE_PATH
                    IDENT 'std'
                    COLON_COLON '::'
                    IDENT 'op'
                    COLON_COLON '::'
                    IDENT 'Add'
                  GREATER '>'
                  COLON_COLON '::'
                  IDENT 'add'
              ARG_LIST
                OPEN_PAREN '('
                LITERAL
                  INTEGER_KW '3'
                CLOSE_PAREN ')'
          NL_KW '\n'
          WHITESPACE '      '
      "#],
    );
  }
}
