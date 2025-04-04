#[derive(Debug, PartialEq, Clone, Copy, Ord, PartialOrd, Eq)]
pub(crate) enum TokenKind {
  Boolean,
  BracketL,
  BracketR,
  Character,
  Eof,
  Error,
  Number,
  ParenL,
  ParenR,
  Quasiquote,
  Quote,
  String,
  Symbol,
  Unquote,
  UnquoteSplicing,
}
