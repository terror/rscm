use super::*;

#[derive(Debug)]
pub(crate) struct Parser<'src> {
  lexer: Lexer<'src>,
  current: Token<'src>,
}

#[derive(Debug)]
#[allow(unused)]
pub(crate) enum ParseError<'src> {
  UnexpectedToken {
    expected: &'static str,
    found: Token<'src>,
  },
  InvalidNumber(Token<'src>),
  UnterminatedList(Token<'src>),
  UnterminatedVector(Token<'src>),
  EmptyDottedList(Token<'src>),
  MultipleDots(Token<'src>),
  EndOfFile,
}

impl Display for ParseError<'_> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      ParseError::UnexpectedToken { expected, found } => {
        write!(
          f,
          "Unexpected token at line {}, column {}: expected {}, found {:?} '{}'",
          found.line, found.column, expected, found.kind, found.lexeme
        )
      }
      ParseError::InvalidNumber(token) => {
        write!(
          f,
          "Invalid number at line {}, column {}: '{}'",
          token.line, token.column, token.lexeme
        )
      }
      ParseError::UnterminatedList(token) => {
        write!(
          f,
          "Unterminated list starting at line {}, column {}",
          token.line, token.column
        )
      }
      ParseError::UnterminatedVector(token) => {
        write!(
          f,
          "Unterminated vector starting at line {}, column {}",
          token.line, token.column
        )
      }
      ParseError::EmptyDottedList(token) => {
        write!(
          f,
          "Empty list before dot at line {}, column {}",
          token.line, token.column
        )
      }
      ParseError::MultipleDots(token) => {
        write!(
          f,
          "Multiple dots in list at line {}, column {}",
          token.line, token.column
        )
      }
      ParseError::EndOfFile => {
        write!(f, "Unexpected end of file")
      }
    }
  }
}

impl<'src> Parser<'src> {
  pub fn new(src: &'src str) -> Self {
    let mut lexer = Lexer::new(src);

    let current = lexer.next_token();

    Parser { lexer, current }
  }

  pub fn parse(&mut self) -> Result<Vec<Expression<'src>>, ParseError<'src>> {
    let mut expressions = Vec::new();

    while self.current.kind != TokenKind::Eof {
      expressions.push(self.expression()?);
    }

    Ok(expressions)
  }

  pub fn expression(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    match self.current.kind {
      TokenKind::Boolean => self.boolean(),
      TokenKind::Number => self.number(),
      TokenKind::String => self.string(),
      TokenKind::Character => self.character(),
      TokenKind::Symbol => self.symbol(),
      TokenKind::ParenL => self.list(),
      TokenKind::BracketL => self.vector(),
      TokenKind::Quote => self.quoted(),
      TokenKind::Quasiquote => self.quasiquoted(),
      TokenKind::Unquote => self.unquoted(),
      TokenKind::UnquoteSplicing => self.unquote_splicing(),
      TokenKind::Eof => Err(ParseError::EndOfFile),
      _ => Err(ParseError::UnexpectedToken {
        expected: "expression",
        found: self.current.clone(),
      }),
    }
  }

  fn advance(&mut self) -> Token<'src> {
    let old = self.current.clone();
    self.current = self.lexer.next_token();
    old
  }

  fn consume(
    &mut self,
    kind: TokenKind,
  ) -> Result<Token<'src>, ParseError<'src>> {
    if self.current.kind == kind {
      Ok(self.advance())
    } else {
      Err(ParseError::UnexpectedToken {
        expected: "Unexpected token",
        found: self.current.clone(),
      })
    }
  }

  fn boolean(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    let token = self.advance();

    let value = match token.lexeme {
      "#t" => true,
      "#f" => false,
      _ => {
        return Err(ParseError::UnexpectedToken {
          expected: "#t or #f",
          found: token,
        });
      }
    };

    Ok(Expression::Atom(Atom::Boolean(value)))
  }

  fn number(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    let token = self.advance();

    let lexeme = token.lexeme;

    if lexeme.contains('/') {
      let parts: Vec<&str> = lexeme.split('/').collect();
      if parts.len() == 2 {
        if let (Ok(num), Ok(denom)) =
          (parts[0].parse::<i64>(), parts[1].parse::<i64>())
        {
          if denom != 0 {
            return Ok(Expression::Atom(Atom::Number(Number::Rational(
              num, denom,
            ))));
          }
        }
      }
    } else if lexeme.contains('+')
      && lexeme.contains('i')
      && !lexeme.starts_with('+')
    {
      let parts: Vec<&str> = lexeme.split('+').collect();
      if parts.len() == 2 {
        let imag_part = parts[1].trim_end_matches('i');
        if let (Ok(real), Ok(imag)) =
          (parts[0].parse::<i64>(), imag_part.parse::<i64>())
        {
          return Ok(Expression::Atom(Atom::Number(Number::Complex(
            Box::new(Number::Integer(real)),
            Box::new(Number::Integer(imag)),
          ))));
        } else if let (Ok(real), Ok(imag)) =
          (parts[0].parse::<f64>(), imag_part.parse::<f64>())
        {
          return Ok(Expression::Atom(Atom::Number(Number::Complex(
            Box::new(Number::Float(real)),
            Box::new(Number::Float(imag)),
          ))));
        }
      }
    } else if lexeme.contains('-')
      && lexeme.contains('i')
      && !lexeme.starts_with('-')
    {
      if let Some(idx) = lexeme.rfind('-') {
        let (real_part, imag_part) = lexeme.split_at(idx);

        let imag_part = imag_part.trim_end_matches('i');

        if let (Ok(real), Ok(imag)) =
          (real_part.parse::<i64>(), imag_part.parse::<i64>())
        {
          return Ok(Expression::Atom(Atom::Number(Number::Complex(
            Box::new(Number::Integer(real)),
            Box::new(Number::Integer(imag)),
          ))));
        } else if let (Ok(real), Ok(imag)) =
          (real_part.parse::<f64>(), imag_part.parse::<f64>())
        {
          return Ok(Expression::Atom(Atom::Number(Number::Complex(
            Box::new(Number::Float(real)),
            Box::new(Number::Float(imag)),
          ))));
        }
      }
    } else if lexeme.contains('.')
      || lexeme.contains('e')
      || lexeme.contains('E')
    {
      if let Ok(value) = lexeme.parse::<f64>() {
        return Ok(Expression::Atom(Atom::Number(Number::Float(value))));
      }
    } else if let Ok(value) = lexeme.parse::<i64>() {
      return Ok(Expression::Atom(Atom::Number(Number::Integer(value))));
    }

    Ok(Expression::Atom(Atom::Number(Number::Unparsed(lexeme))))
  }

  fn string(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    let token = self.advance();
    let value = &token.lexeme[1..token.lexeme.len() - 1];
    Ok(Expression::Atom(Atom::String(value)))
  }

  fn character(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    let token = self.advance();
    let lexeme = token.lexeme;

    let char_spec = &lexeme[2..];

    let ch = match char_spec {
      "space" => ' ',
      "newline" => '\n',
      "tab" => '\t',
      "return" => '\r',
      s if s.chars().count() == 1 => s.chars().next().unwrap(),
      _ => {
        return Err(ParseError::UnexpectedToken {
          expected: "valid character",
          found: token,
        });
      }
    };

    Ok(Expression::Atom(Atom::Character(ch)))
  }

  fn symbol(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    let token = self.advance();
    Ok(Expression::Atom(Atom::Symbol(token.lexeme)))
  }

  fn list(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    let open_paren = self.advance();

    let mut elements = Vec::new();

    if self.current.kind == TokenKind::ParenR {
      self.advance();
      return Ok(Expression::List(Vec::new()));
    }

    while self.current.kind != TokenKind::ParenR {
      if self.current.kind == TokenKind::Eof {
        return Err(ParseError::UnterminatedList(open_paren));
      }

      if self.current.kind == TokenKind::Symbol && self.current.lexeme == "." {
        self.advance();

        if elements.is_empty() {
          return Err(ParseError::EmptyDottedList(self.current.clone()));
        }

        let tail = self.expression()?;

        self.consume(TokenKind::ParenR)?;

        return Ok(Expression::DottedList(elements, Box::new(tail)));
      }

      elements.push(self.expression()?);
    }

    self.advance();

    Ok(Expression::List(elements))
  }

  fn vector(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    let open_bracket = self.advance();

    let mut elements = Vec::new();

    while self.current.kind != TokenKind::BracketR {
      if self.current.kind == TokenKind::Eof {
        return Err(ParseError::UnterminatedVector(open_bracket));
      }

      elements.push(self.expression()?);
    }

    self.advance();

    Ok(Expression::Vector(elements))
  }

  fn quoted(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    self.advance();
    let expr = self.expression()?;
    Ok(Expression::Quoted(Box::new(expr)))
  }

  fn quasiquoted(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    self.advance();
    let expr = self.expression()?;
    Ok(Expression::Quasiquoted(Box::new(expr)))
  }

  fn unquoted(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    self.advance();
    let expr = self.expression()?;
    Ok(Expression::Unquoted(Box::new(expr)))
  }

  fn unquote_splicing(&mut self) -> Result<Expression<'src>, ParseError<'src>> {
    self.advance();
    let expr = self.expression()?;
    Ok(Expression::UnquoteSpliced(Box::new(expr)))
  }
}

#[cfg(test)]
mod tests {
  use {super::*, pretty_assertions::assert_eq};

  struct Test<'src> {
    src: &'src str,
    expected: Option<Vec<Expression<'src>>>,
    expect_error: bool,
  }

  impl<'src> Test<'src> {
    fn new() -> Self {
      Self {
        src: "",
        expected: None,
        expect_error: false,
      }
    }

    fn src(self, src: &'src str) -> Self {
      Self { src, ..self }
    }

    fn expected(self, expected: &[Expression<'src>]) -> Self {
      Self {
        expected: Some(expected.to_owned()),
        ..self
      }
    }

    fn expect_error(self) -> Self {
      Self {
        expect_error: true,
        ..self
      }
    }

    fn run(self) {
      let mut parser = Parser::new(self.src);

      let result = parser.parse();

      if self.expect_error {
        assert!(
          result.is_err(),
          "Expected parse error, but parsing succeeded"
        );

        return;
      }

      assert!(result.is_ok(), "Parse error: {:?}", result.err());

      let parsed = result.unwrap();

      if let Some(expected) = self.expected {
        assert_eq!(
          parsed, expected,
          "Parsed AST doesn't match expected AST\nParsed: {:?}\nExpected: {:?}",
          parsed, expected
        );
      }
    }
  }

  #[test]
  fn atoms() {
    Test::new()
      .src("42 3.15 \"hello\" #t #f #\\a")
      .expected(&[
        Expression::Atom(Atom::Number(Number::Integer(42))),
        Expression::Atom(Atom::Number(Number::Float(3.15))),
        Expression::Atom(Atom::String("hello")),
        Expression::Atom(Atom::Boolean(true)),
        Expression::Atom(Atom::Boolean(false)),
        Expression::Atom(Atom::Character('a')),
      ])
      .run();
  }

  #[test]
  fn lists() {
    Test::new()
      .src("() (1 2 3) (a b c)")
      .expected(&[
        Expression::List(vec![]),
        Expression::List(vec![
          Expression::Atom(Atom::Number(Number::Integer(1))),
          Expression::Atom(Atom::Number(Number::Integer(2))),
          Expression::Atom(Atom::Number(Number::Integer(3))),
        ]),
        Expression::List(vec![
          Expression::Atom(Atom::Symbol("a")),
          Expression::Atom(Atom::Symbol("b")),
          Expression::Atom(Atom::Symbol("c")),
        ]),
      ])
      .run();
  }

  #[test]
  fn dotted_lists() {
    Test::new()
      .src("(1 . 2) (a b . c)")
      .expected(&[
        Expression::DottedList(
          vec![Expression::Atom(Atom::Number(Number::Integer(1)))],
          Box::new(Expression::Atom(Atom::Number(Number::Integer(2)))),
        ),
        Expression::DottedList(
          vec![
            Expression::Atom(Atom::Symbol("a")),
            Expression::Atom(Atom::Symbol("b")),
          ],
          Box::new(Expression::Atom(Atom::Symbol("c"))),
        ),
      ])
      .run();
  }

  #[test]
  fn vectors() {
    Test::new()
      .src("[] [1 2 3] [a b c]")
      .expected(&[
        Expression::Vector(vec![]),
        Expression::Vector(vec![
          Expression::Atom(Atom::Number(Number::Integer(1))),
          Expression::Atom(Atom::Number(Number::Integer(2))),
          Expression::Atom(Atom::Number(Number::Integer(3))),
        ]),
        Expression::Vector(vec![
          Expression::Atom(Atom::Symbol("a")),
          Expression::Atom(Atom::Symbol("b")),
          Expression::Atom(Atom::Symbol("c")),
        ]),
      ])
      .run();
  }

  #[test]
  fn quotes() {
    Test::new()
      .src("'a `(1 2) ,(+ 1 2) ,@(list 1 2)")
      .expected(&[
        Expression::Quoted(Box::new(Expression::Atom(Atom::Symbol("a")))),
        Expression::Quasiquoted(Box::new(Expression::List(vec![
          Expression::Atom(Atom::Number(Number::Integer(1))),
          Expression::Atom(Atom::Number(Number::Integer(2))),
        ]))),
        Expression::Unquoted(Box::new(Expression::List(vec![
          Expression::Atom(Atom::Symbol("+")),
          Expression::Atom(Atom::Number(Number::Integer(1))),
          Expression::Atom(Atom::Number(Number::Integer(2))),
        ]))),
        Expression::UnquoteSpliced(Box::new(Expression::List(vec![
          Expression::Atom(Atom::Symbol("list")),
          Expression::Atom(Atom::Number(Number::Integer(1))),
          Expression::Atom(Atom::Number(Number::Integer(2))),
        ]))),
      ])
      .run();
  }

  #[test]
  fn nested_expressions() {
    Test::new()
      .src("(define (factorial n) (if (= n 0) 1 (* n (factorial (- n 1)))))")
      .expected(&[Expression::List(vec![
        Expression::Atom(Atom::Symbol("define")),
        Expression::List(vec![
          Expression::Atom(Atom::Symbol("factorial")),
          Expression::Atom(Atom::Symbol("n")),
        ]),
        Expression::List(vec![
          Expression::Atom(Atom::Symbol("if")),
          Expression::List(vec![
            Expression::Atom(Atom::Symbol("=")),
            Expression::Atom(Atom::Symbol("n")),
            Expression::Atom(Atom::Number(Number::Integer(0))),
          ]),
          Expression::Atom(Atom::Number(Number::Integer(1))),
          Expression::List(vec![
            Expression::Atom(Atom::Symbol("*")),
            Expression::Atom(Atom::Symbol("n")),
            Expression::List(vec![
              Expression::Atom(Atom::Symbol("factorial")),
              Expression::List(vec![
                Expression::Atom(Atom::Symbol("-")),
                Expression::Atom(Atom::Symbol("n")),
                Expression::Atom(Atom::Number(Number::Integer(1))),
              ]),
            ]),
          ]),
        ]),
      ])])
      .run();
  }

  #[test]
  fn unterminated_list() {
    Test::new().src("(1 2 3").expect_error().run();
  }

  #[test]
  fn unterminated_vector() {
    Test::new().src("[1 2 3").expect_error().run();
  }

  #[test]
  fn empty_dotted_list() {
    Test::new().src("(. 1)").expect_error().run();
  }

  #[test]
  fn multiple_dots() {
    Test::new().src("(1 . 2 . 3)").expect_error().run();
  }
}
