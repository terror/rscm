use super::*;

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Token<'src> {
  pub(crate) kind: TokenKind,
  pub(crate) lexeme: &'src str,
  pub(crate) column: usize,
  pub(crate) line: usize,
  pub(crate) offset: usize,
  pub(crate) length: usize,
}
