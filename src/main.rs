use {
  ast::{Atom, Expression, Number},
  clap::Parser,
  compiler::Compiler,
  inkwell::context::Context,
  lexer::Lexer,
  parser::Parser as SchemeParser,
  position::Position,
  std::{
    fmt::{self, Display, Formatter},
    fs,
    process::Command,
    str::Chars,
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

#[derive(Parser)]
#[clap(author, version, about)]
struct Args {
  filename: String,
}

fn run_command(cmd: &str, args: &[&str]) -> Result<String, String> {
  let output = Command::new(cmd)
    .args(args)
    .output()
    .map_err(|e| format!("Failed to execute {}: {}", cmd, e))?;

  Ok(String::from_utf8_lossy(&output.stdout).to_string())
}

fn main() {
  let args = Args::parse();

  let input = fs::read_to_string(&args.filename).unwrap_or_else(|err| {
    eprintln!("Failed to read file '{}': {}", &args.filename, err);
    std::process::exit(1);
  });

  let ast = match SchemeParser::new(&input).parse() {
    Ok(ast) => ast,
    Err(err) => {
      eprintln!("Failed to parse program: {}", err);
      std::process::exit(1);
    }
  };

  let temp_dir = tempdir().expect("Failed to create temporary directory");

  let output_ll = temp_dir.path().join("output.ll");
  let output_s = temp_dir.path().join("output.s");
  let output_exe = temp_dir.path().join("output");

  let context = Context::create();

  let mut compiler = Compiler::new(&context, "scheme_module");

  if let Err(err) = compiler.compile(&ast) {
    eprintln!("Failed to compile program: {}", err);
    std::process::exit(1);
  }

  let ir = compiler.get_ir();

  if let Err(err) = fs::write(&output_ll, &ir) {
    eprintln!("Could not write to {}: {}", output_ll.display(), err);
    std::process::exit(1);
  }

  if let Err(err) = run_command(
    "llc",
    &[
      output_ll.to_str().unwrap(),
      "-o",
      output_s.to_str().unwrap(),
    ],
  ) {
    eprintln!("{}", err);
    std::process::exit(1);
  }

  if let Err(err) = run_command(
    "clang",
    &[
      output_s.to_str().unwrap(),
      "-o",
      output_exe.to_str().unwrap(),
    ],
  ) {
    eprintln!("{}", err);
    std::process::exit(1);
  }

  match run_command(output_exe.to_str().unwrap(), &[]) {
    Ok(output) => {
      println!("{output}");
    }
    Err(err) => {
      eprintln!("{}", err);
      std::process::exit(1);
    }
  }
}
