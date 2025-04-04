use {
  ast::{Atom, Expression, Number},
  compiler::Compiler,
  inkwell::context::Context,
  lexer::Lexer,
  parser::Parser,
  position::Position,
  std::{
    fmt::{self, Display, Formatter},
    fs::File,
    io::Write,
    str::Chars,
  },
  token::Token,
  token_kind::TokenKind,
};

mod ast;
mod compiler;
mod lexer;
mod parser;
mod position;
mod token;
mod token_kind;

fn main() {
  let input = "#t";

  let ast = Parser::new(input).parse();

  match ast {
    Ok(ast) => {
      let context = Context::create();

      let mut compiler = Compiler::new(&context, "scheme_module");

      match compiler.compile(&ast) {
        Ok(()) => {
          let ir = compiler.get_ir();

          println!("{}", ir.trim());

          let mut file =
            File::create("output.ll").expect("Could not create output file");
          file
            .write_all(ir.as_bytes())
            .expect("Could not write to output file");
        }
        Err(error) => {
          eprintln!("Failed to compile program: {error}");
        }
      }
    }
    Err(error) => {
      eprintln!("Failed to parse program: {error}");
    }
  }
}
