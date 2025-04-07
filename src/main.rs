use {
  ast::{Atom, Expression, Number},
  clap::Parser as Clap,
  compiler::Compiler,
  inkwell::{
    OptimizationLevel, context::Context, execution_engine::JitFunction,
  },
  lexer::Lexer,
  parser::Parser,
  position::Position,
  std::{
    fmt::{self, Display, Formatter},
    fs, process,
    str::{self, Chars},
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

type Main = unsafe extern "C" fn() -> i32;

#[derive(Clap)]
#[clap(author, version, about)]
struct Arguments {
  filename: String,
}

impl Arguments {
  fn run(self) -> Result {
    let input = fs::read_to_string(&self.filename)?;

    let ast = match Parser::new(&input).parse() {
      Ok(ast) => ast,
      Err(error) => {
        eprintln!("error: {error}");
        process::exit(1);
      }
    };

    let context = Context::create();

    let mut compiler = Compiler::new(&context);

    let module = compiler.compile(&ast)?;

    let execution_engine =
      module.create_jit_execution_engine(OptimizationLevel::Default)?;

    let main: JitFunction<Main> =
      unsafe { execution_engine.get_function("main")? };

    unsafe {
      main.call();
    }

    Ok(())
  }
}

type Result<T = (), E = Box<dyn std::error::Error>> = std::result::Result<T, E>;

fn main() {
  if let Err(error) = Arguments::parse().run() {
    eprintln!("error: {error}");
    process::exit(1);
  }
}
