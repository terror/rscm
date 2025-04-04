use super::*;

pub(crate) struct Lexer<'src> {
  chars: Chars<'src>,
  current: Option<char>,
  src: &'src str,
  position: Position,
  start_position: Position,
}

impl<'src> Lexer<'src> {
  pub fn new(src: &'src str) -> Self {
    let mut chars = src.chars();

    let current = chars.next();

    Lexer {
      chars,
      current,
      src,
      position: Position::new(),
      start_position: Position::new(),
    }
  }

  fn advance(&mut self) -> Option<char> {
    if let Some(c) = self.current {
      self.position.advance(c);
    }

    let next = self.chars.next();

    self.current = next;

    next
  }

  fn eof(&self) -> Token<'src> {
    Token {
      kind: TokenKind::Eof,
      lexeme: "",
      column: self.position.column,
      line: self.position.line,
      offset: self.position.offset,
      length: 0,
    }
  }

  fn error(&self, message: &'src str) -> Token<'src> {
    let length = self.position.offset - self.start_position.offset;

    let start = self.start_position.offset;

    let lexeme = if length > 0 {
      &self.src[start..start + length]
    } else {
      message
    };

    Token {
      kind: TokenKind::Error,
      lexeme,
      column: self.start_position.column,
      line: self.start_position.line,
      offset: self.start_position.offset,
      length: if length > 0 { length } else { message.len() },
    }
  }

  fn expect(&mut self, expected: char) -> bool {
    if self.current == Some(expected) {
      self.advance();
      true
    } else {
      false
    }
  }

  fn hash(&mut self) -> Token<'src> {
    self.advance();

    if let Some(c) = self.current {
      match c {
        't' | 'f' => {
          self.advance();

          if let Some(next) = self.current {
            if Self::is_symbol_char(next) {
              return self.error("Invalid boolean literal");
            }
          }

          self.token(TokenKind::Boolean)
        }
        '\\' => {
          self.advance();

          while let Some(c) = self.current {
            if c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']'
            {
              break;
            }

            self.advance();
          }

          self.token(TokenKind::Character)
        }
        'b' | 'o' | 'd' | 'x' => {
          let radix = match c {
            'b' => 2,
            'o' => 8,
            'd' => 10,
            'x' => 16,
            _ => unreachable!(),
          };

          self.advance();

          let has_digits = if let Some(d) = self.current {
            Self::is_digit_in_radix(d, radix)
          } else {
            false
          };

          if !has_digits {
            return self.error("Invalid number in radix");
          }

          while let Some(c) = self.current {
            if Self::is_digit_in_radix(c, radix) {
              self.advance();
            } else {
              break;
            }
          }

          self.token(TokenKind::Number)
        }
        'e' | 'i' => {
          self.advance();

          if let Some(r) = self.current {
            if r == 'b' || r == 'o' || r == 'd' || r == 'x' {
              return self.hash();
            }
          }

          return self.number();
        }
        _ => self.error("Invalid hash prefix"),
      }
    } else {
      self.error("Unexpected end of file after '#'")
    }
  }

  fn is_digit(c: char) -> bool {
    c.is_digit(10)
  }

  fn is_digit_in_radix(c: char, radix: u32) -> bool {
    c.is_digit(radix)
  }

  fn is_number_start(&self, c: char) -> bool {
    Self::is_digit(c)
      || (c == '-' || c == '+') && self.peek().map_or(false, Self::is_digit)
  }

  fn is_symbol_char(c: char) -> bool {
    Self::is_symbol_start(c) || Self::is_digit(c)
  }

  fn is_symbol_start(c: char) -> bool {
    c.is_alphabetic() || "!$%&*+-./:<=>?@^_~".contains(c)
  }

  pub fn next_token(&mut self) -> Token<'src> {
    self.skip_whitespace();

    self.start_position = self.position;

    if let Some(c) = self.current {
      match c {
        '(' => {
          self.advance();
          self.token(TokenKind::ParenL)
        }
        ')' => {
          self.advance();
          self.token(TokenKind::ParenR)
        }
        '[' => {
          self.advance();
          self.token(TokenKind::BracketL)
        }
        ']' => {
          self.advance();
          self.token(TokenKind::BracketR)
        }
        '\'' => {
          self.advance();
          self.token(TokenKind::Quote)
        }
        '`' => {
          self.advance();
          self.token(TokenKind::Quasiquote)
        }
        ',' => {
          self.advance();

          if self.expect('@') {
            self.token(TokenKind::UnquoteSplicing)
          } else {
            self.token(TokenKind::Unquote)
          }
        }
        ';' => {
          self.skip_comment();
          self.next_token()
        }
        '"' => self.string(),
        '#' => self.hash(),
        c if self.is_number_start(c) => self.number(),
        c if Self::is_symbol_start(c) => self.symbol(),
        _ => self.error("Unexpected character"),
      }
    } else {
      self.eof()
    }
  }

  fn number(&mut self) -> Token<'src> {
    if self.current == Some('-') || self.current == Some('+') {
      self.advance();
    }

    let has_digits = if let Some(c) = self.current {
      Self::is_digit(c)
    } else {
      false
    };

    if !has_digits {
      return self.error("Expected digits");
    }

    while let Some(c) = self.current {
      if Self::is_digit(c) {
        self.advance();
      } else {
        break;
      }
    }

    if self.current == Some('/') {
      self.advance();

      let has_denominator = if let Some(c) = self.current {
        Self::is_digit(c)
      } else {
        false
      };

      if !has_denominator {
        return self.error("Expected denominator");
      }

      while let Some(c) = self.current {
        if Self::is_digit(c) {
          self.advance();
        } else {
          break;
        }
      }

      return self.token(TokenKind::Number);
    }

    if self.current == Some('.') {
      self.advance();

      let has_decimal_digits = if let Some(c) = self.current {
        Self::is_digit(c)
      } else {
        false
      };

      if has_decimal_digits {
        while let Some(c) = self.current {
          if Self::is_digit(c) {
            self.advance();
          } else {
            break;
          }
        }
      }
    }

    if let Some('e' | 'E') = self.current {
      self.advance();

      if let Some('+' | '-') = self.current {
        self.advance();
      }

      let has_exponent_digits = if let Some(c) = self.current {
        Self::is_digit(c)
      } else {
        false
      };

      if has_exponent_digits {
        while let Some(c) = self.current {
          if Self::is_digit(c) {
            self.advance();
          } else {
            break;
          }
        }
      } else {
        return self.error("Expected exponent digits");
      }
    }

    if let Some('+' | '-') = self.current {
      let sign = self.current.unwrap();

      self.advance();

      let has_imaginary_part = if let Some(c) = self.current {
        Self::is_digit(c)
      } else {
        false
      };

      if has_imaginary_part {
        while let Some(c) = self.current {
          if Self::is_digit(c) {
            self.advance();
          } else {
            break;
          }
        }

        if self.current == Some('.') {
          self.advance();

          while let Some(c) = self.current {
            if Self::is_digit(c) {
              self.advance();
            } else {
              break;
            }
          }
        }

        if self.current == Some('i') {
          self.advance();
        } else {
          return self.error("Expected 'i' for complex number");
        }
      } else if sign == '+' {
        return self.error("Invalid number format");
      }
    }

    self.token(TokenKind::Number)
  }

  fn peek(&self) -> Option<char> {
    self.chars.clone().next()
  }

  fn skip_comment(&mut self) {
    self.advance();

    while let Some(c) = self.current {
      if c == '\n' {
        self.advance();
        break;
      }

      self.advance();
    }
  }

  fn skip_whitespace(&mut self) {
    while let Some(c) = self.current {
      if c.is_whitespace() {
        self.advance();
      } else {
        break;
      }
    }
  }

  fn string(&mut self) -> Token<'src> {
    self.advance();

    while let Some(c) = self.current {
      if c == '"' {
        break;
      } else if c == '\\' {
        self.advance();

        if self.current.is_none() {
          return self.error("Unterminated string literal");
        }

        match self.current {
          Some('n') | Some('t') | Some('r') | Some('\\') | Some('"') => {
            self.advance();
          }
          Some(_) => {
            self.advance();
          }
          None => return self.error("Unterminated string literal"),
        }
      } else {
        self.advance();
      }
    }

    if self.current.is_none() {
      return self.error("Unterminated string literal");
    }

    self.advance();

    self.token(TokenKind::String)
  }

  fn symbol(&mut self) -> Token<'src> {
    while let Some(c) = self.current {
      if Self::is_symbol_char(c) {
        self.advance();
      } else {
        break;
      }
    }

    self.token(TokenKind::Symbol)
  }

  fn token(&self, kind: TokenKind) -> Token<'src> {
    let length = self.position.offset - self.start_position.offset;

    let start = self.start_position.offset;

    let lexeme = &self.src[start..start + length];

    Token {
      kind,
      lexeme,
      column: self.start_position.column,
      line: self.start_position.line,
      offset: self.start_position.offset,
      length,
    }
  }
}

#[cfg(test)]
mod tests {
  use {super::*, TokenKind::*, indoc::indoc, pretty_assertions::assert_eq};

  struct Test<'src> {
    expected: Vec<TokenKind>,
    src: &'src str,
  }

  impl<'src> Test<'src> {
    fn new() -> Self {
      Self {
        src: "",
        expected: vec![],
      }
    }

    fn expected(self, expected: &[TokenKind]) -> Self {
      Self {
        expected: expected.to_owned(),
        ..self
      }
    }

    fn src(self, src: &'src str) -> Self {
      Self { src, ..self }
    }

    fn run(self) {
      let mut lexer = Lexer::new(self.src);

      for (i, expected_kind) in self.expected.iter().enumerate() {
        let token = lexer.next_token();

        assert_eq!(
          token.kind, *expected_kind,
          "Token {} - expected kind {:?}, got {:?}",
          i, expected_kind, token.kind
        );
      }

      let next = lexer.next_token();

      assert_eq!(
        next.kind,
        Eof,
        "Expected end of file after {} tokens, but found: {:?} '{}'",
        self.expected.len(),
        next.kind,
        next.lexeme
      );
    }
  }

  #[test]
  fn basic_tokens() {
    Test::new()
      .src("()[] 123 3.14 hello define + \"hello\" #t #f #\\a ' ` , ,@")
      .expected(&[
        ParenL,
        ParenR,
        BracketL,
        BracketR,
        Number,
        Number,
        Symbol,
        Symbol,
        Symbol,
        String,
        Boolean,
        Boolean,
        Character,
        Quote,
        Quasiquote,
        Unquote,
        UnquoteSplicing,
      ])
      .run();
  }

  #[test]
  fn numbers() {
    Test::new()
      .src("123 3.14 1e10 2.5e-3 1+2i 3.14-2.718i 1/2 3/4")
      .expected(&[
        Number, Number, Number, Number, Number, Number, Number, Number,
      ])
      .run();
  }

  #[test]
  fn invalid_numbers() {
    Test::new()
      .src("1/ 1/0 -")
      .expected(&[Error, Number, Symbol])
      .run();
  }

  #[test]
  fn symbols() {
    Test::new()
      .src("hello define hello-world + <= <=? . !")
      .expected(&[
        Symbol, Symbol, Symbol, Symbol, Symbol, Symbol, Symbol, Symbol,
      ])
      .run();
  }

  #[test]
  fn strings() {
    Test::new()
      .src(r#""hello" "hello\"world" "Line 1\nLine 2" "Tab\tcharacter" "Double quote \" inside string""#)
      .expected(&[String, String, String, String, String])
      .run();
  }

  #[test]
  fn boolean_and_character_literals() {
    Test::new()
      .src("#t #f #\\a #\\z #\\space #\\newline")
      .expected(&[Boolean, Boolean, Character, Character, Character, Character])
      .run();
  }

  #[test]
  fn invalid_hash_literals() {
    Test::new()
      .src("#txyz #fx #b #b2 #o9 #xg # #a")
      .expected(&[
        Error, Symbol, Error, Symbol, Error, Error, Number, Error, Number,
        Error, Symbol, Error, Error, Symbol,
      ])
      .run();
  }

  #[test]
  fn quotes() {
    Test::new()
      .src("' ` , ,@ '(1 2 3) `(1 ,(+ 2 3) ,@(list 4 5))")
      .expected(&[
        Quote,
        Quasiquote,
        Unquote,
        UnquoteSplicing,
        Quote,
        ParenL,
        Number,
        Number,
        Number,
        ParenR,
        Quasiquote,
        ParenL,
        Number,
        Unquote,
        ParenL,
        Symbol,
        Number,
        Number,
        ParenR,
        UnquoteSplicing,
        ParenL,
        Symbol,
        Number,
        Number,
        ParenR,
        ParenR,
      ])
      .run();
  }

  #[test]
  fn comments() {
    Test::new()
      .src(indoc! {
        "
        ; This is a comment

        (define x ; inline comment
          10) ; end comment
        "
      })
      .expected(&[ParenL, Symbol, Symbol, Number, ParenR])
      .run();
  }

  #[test]
  fn whitespace_handling() {
    Test::new()
      .src("  (  define    x   10   )  ")
      .expected(&[ParenL, Symbol, Symbol, Number, ParenR])
      .run();
  }

  #[test]
  fn complete_expressions() {
    Test::new()
      .src(indoc! {
        "
        (define (square x) (* x x))

        (define (factorial n)
          (if (= n 0) 1 (* n (factorial (- n 1)))))

        (define pi 3.14159)

        (define greeting \"Hello, world!\")
          (if #t (display greeting) '()) (cons 1 . 2)
        "
      })
      .expected(&[
        ParenL, Symbol, ParenL, Symbol, Symbol, ParenR, ParenL, Symbol, Symbol,
        Symbol, ParenR, ParenR, ParenL, Symbol, ParenL, Symbol, Symbol, ParenR,
        ParenL, Symbol, ParenL, Symbol, Symbol, Number, ParenR, Number, ParenL,
        Symbol, Symbol, ParenL, Symbol, ParenL, Symbol, Symbol, Number, ParenR,
        ParenR, ParenR, ParenR, ParenR, ParenL, Symbol, Symbol, Number, ParenR,
        ParenL, Symbol, Symbol, String, ParenR, ParenL, Symbol, Boolean,
        ParenL, Symbol, Symbol, ParenR, Quote, ParenL, ParenR, ParenR, ParenL,
        Symbol, Number, Symbol, Number, ParenR,
      ])
      .run();
  }
}
