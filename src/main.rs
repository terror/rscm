use {
  ast::{Atom, Expression, Number},
  clap::Parser as Clap,
  compiler::Compiler,
  inkwell::context::Context,
  lexer::Lexer,
  parser::Parser,
  position::Position,
  std::{
    fmt::{self, Display, Formatter},
    fs,
    process::{self, Command, Output},
    str::{self, Chars},
  },
  tempfile::tempdir,
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

#[derive(Clap)]
#[clap(author, version, about)]
struct Arguments {
  filename: String,
}

impl Arguments {
  fn run(self) -> Result {
    let tempdir = tempdir()?;

    let input = fs::read_to_string(&self.filename)?;

    let ast = match Parser::new(&input).parse() {
      Ok(ast) => ast,
      Err(error) => {
        eprintln!("error: {error}");
        process::exit(1);
      }
    };

    let context = Context::create();

    let mut compiler = Compiler::new(&context, env!("CARGO_PKG_NAME"));
    compiler.compile(&ast)?;

    let output_ir = tempdir
      .path()
      .join(format!("{}-output.ll", env!("CARGO_PKG_NAME")));

    fs::write(&output_ir, &compiler.get_ir())?;

    let output_s = tempdir
      .path()
      .join(format!("{}-output.s", env!("CARGO_PKG_NAME")));

    Self::command(
      "llc",
      &[
        output_ir.to_str().unwrap(),
        "-o",
        output_s.to_str().unwrap(),
      ],
    )?;

    let binary = tempdir
      .path()
      .join(format!("{}.out", env!("CARGO_PKG_NAME")));

    Self::command(
      "clang",
      &[
        output_s.to_str().unwrap(),
        "-o",
        binary.to_str().ok_or("Path isn't valid unicode")?,
      ],
    )?;

    println!(
      "{}",
      str::from_utf8(&Self::command(binary.to_str().unwrap(), &[])?.stdout)?
    );

    Ok(())
  }

  fn command(cmd: &str, args: &[&str]) -> Result<Output> {
    Ok(Command::new(cmd).args(args).output()?)
  }
}

type Result<T = (), E = Box<dyn std::error::Error>> = std::result::Result<T, E>;

fn main() {
  if let Err(error) = Arguments::parse().run() {
    eprintln!("error: {error}");
    process::exit(1);
  }
}
