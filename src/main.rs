use {
  ast::{Atom, Expression, Number},
  lexer::Lexer,
  parser::Parser,
  position::Position,
  std::{
    fmt::{self, Display, Formatter},
    str::Chars,
  },
  token::Token,
  token_kind::TokenKind,
};

mod ast;
mod lexer;
mod parser;
mod position;
mod token;
mod token_kind;

fn main() {
  let input = "(define (factorial n) (if (= n 0) 1 (* n (factorial (- n 1))))) (display (factorial 5))";

  println!("{:?}", Parser::new(input).parse().unwrap());
}
