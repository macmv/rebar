use crate::{CompletedMarker, Parser, SyntaxKind::*, T};

pub fn block(p: &mut Parser) -> CompletedMarker {
  let m = p.start();
  p.expect(T!['{']);

  while !p.at(EOF) && !p.at(T!['}']) {
    stmt(p);
    while p.at(T![nl]) {
      p.eat(T![nl]);
    }
  }

  p.expect(T!['}']);
  m.complete(p, BLOCK)
}

pub fn stmt(p: &mut Parser) {
  // FIXME: This is a dumb hack to work around the lexer not consuming whitespace
  // correctly.
  while p.at(T![ws]) {
    p.eat(T![ws]);
  }

  while p.at(T![nl]) {
    p.eat(T![nl]);
  }

  // Trailing newlines can cause this to happen.
  if p.at(EOF) {
    return;
  }

  match p.current() {
    // test ok
    // let foo = 2 + 3
    // let bar: int = 4
    T![let] => {
      let m = p.start();
      p.eat(T![let]);
      p.expect(T![ident]);

      if p.at(T![:]) {
        p.eat(T![:]);
        super::types::ty(p);
      }

      p.expect(T![=]);
      super::expr::expr(p);

      m.complete(p, LET);
    }

    // test ok
    // fn foo(bar: int, baz: float) -> string {
    //   bar + baz
    // }
    T![extern] | T![fn] => {
      let m = p.start();

      // test ok
      // extern fn foo()
      // extern "syscall" fn foo()
      if p.at(T![extern]) {
        p.eat(T![extern]);
        if p.at(T!['"']) {
          let m = p.start();
          super::expr::string(p);
          m.complete(p, STRING);
        }
      }

      p.eat(T![fn]);
      p.expect(T![ident]);

      params(p);

      if p.at(T!['{']) {
        block(p);
      }

      m.complete(p, FUNCTION_DEF);
    }

    // test ok
    // struct Foo {
    //   a: int
    //   b: int
    // }
    T![struct] => {
      let m = p.start();
      p.eat(T![struct]);
      p.expect(T![ident]);

      struct_def(p);

      m.complete(p, STRUCT);
    }

    _ => {
      let m = p.start();
      super::expr::expr(p);
      m.complete(p, EXPR_STMT);
    }
  }

  match p.current() {
    T![nl] => p.eat(T![nl]),
    T!['}'] => {}
    _ => {
      // test err
      // foo bar
      p.error("expected end of statement");

      while !p.at(EOF) && !p.at(T![nl]) && !p.at(T!['}']) {
        p.bump();
      }

      match p.current() {
        T![nl] => p.eat(T![nl]),
        T!['}'] => {}
        _ => {}
      }
    }
  }
}

fn params(p: &mut Parser) {
  let m = p.start();

  p.expect(T!['(']);

  while !p.at(EOF) && !p.at(T![')']) {
    let m = p.start();
    p.expect(T![ident]);
    p.expect(T![:]);
    super::types::ty(p);

    if p.at(T![,]) {
      p.eat(T![,]);
      m.complete(p, PARAM);
      if p.at(T![')']) {
        break;
      }
    } else {
      m.complete(p, PARAM);
      break;
    }
  }

  p.expect(T![')']);

  if p.at(T![->]) {
    p.eat(T![->]);
    super::types::ty(p);
  }

  m.complete(p, PARAMS);
}

fn struct_def(p: &mut Parser) -> CompletedMarker {
  let m = p.start();
  p.expect(T!['{']);

  while !p.at(EOF) && !p.at(T!['}']) {
    struct_item(p);
    while p.at(T![nl]) {
      p.eat(T![nl]);
    }
  }

  p.expect(T!['}']);
  m.complete(p, STRUCT_BLOCK)
}

fn struct_item(p: &mut Parser) {
  while p.at(T![nl]) {
    p.eat(T![nl]);
  }

  match p.current() {
    // test ok
    // struct Foo {
    //   fn bar() {}
    // }
    T![fn] => {
      let m = p.start();
      p.eat(T![fn]);
      p.expect(T![ident]);

      params(p);
      block(p);

      m.complete(p, FUNCTION_DEF);
    }

    // test ok
    // struct Foo {
    //   a: int
    // }
    T![ident] => {
      let m = p.start();
      p.eat(T![ident]);
      p.expect(T![:]);
      super::types::ty(p);
      m.complete(p, FIELD);
    }

    _ => {
      p.error("expected a definition");
    }
  }

  match p.current() {
    T![nl] => p.eat(T![nl]),
    T!['}'] => {}
    _ => {
      // test err
      // struct Foo {
      //   a: int foo
      // }
      p.error("expected end of statement");

      while !p.at(EOF) && !p.at(T![nl]) && !p.at(T!['}']) {
        p.bump();
      }

      match p.current() {
        T![nl] => p.eat(T![nl]),
        T!['}'] => {}
        _ => {}
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::tests::check;

  #[test]
  fn handles_newlines_in_blocks() {
    check(
      r#"
        {

          1

        }
      "#,
      expect![@r#"
        SOURCE_FILE
          NL_KW '\n'
          WHITESPACE '        '
          EXPR_STMT
            BLOCK
              OPEN_CURLY '{'
              NL_KW '\n'
              NL_KW '\n'
              WHITESPACE '          '
              EXPR_STMT
                LITERAL
                  INTEGER_KW '1'
              NL_KW '\n'
              NL_KW '\n'
              WHITESPACE '        '
              CLOSE_CURLY '}'
          NL_KW '\n'
          WHITESPACE '      '
      "#],
    );
  }

  #[test]
  fn extern_fns() {
    check(
      r#"
        extern "syscall" fn foo(fd: int)
      "#,
      expect![@r#"
        SOURCE_FILE
          NL_KW '\n'
          WHITESPACE '        '
          FUNCTION_DEF
            EXTERN_KW 'extern'
            WHITESPACE ' '
            STRING
              DOUBLE_QUOTE '"'
              IDENT 'syscall'
              DOUBLE_QUOTE '"'
            WHITESPACE ' '
            FN_KW 'fn'
            WHITESPACE ' '
            IDENT 'foo'
            PARAMS
              OPEN_PAREN '('
              PARAM
                IDENT 'fd'
                COLON ':'
                WHITESPACE ' '
                NAME_TYPE
                  IDENT 'int'
              CLOSE_PAREN ')'
          NL_KW '\n'
          WHITESPACE '      '
      "#],
    );
  }
}
