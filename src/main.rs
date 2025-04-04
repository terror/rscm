use {
  lexer::Lexer, position::Position, std::str::Chars, token::Token,
  token_kind::TokenKind,
};

mod lexer;
mod position;
mod token;
mod token_kind;

fn main() {
  let input = "(define (factorial n) (if (= n 0) 1 (* n (factorial (- n 1))))) (display (factorial 5)) ";

  let mut lexer = Lexer::new(&input);

  loop {
    let token = lexer.next_token();

    println!("{:?}", token.kind);

    if token.kind == TokenKind::Eof || token.kind == TokenKind::Error {
      break;
    }
  }
}
