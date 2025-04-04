use super::*;

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Expression<'src> {
  Atom(Atom<'src>),
  List(Vec<Expression<'src>>),
  DottedList(Vec<Expression<'src>>, Box<Expression<'src>>),
  Vector(Vec<Expression<'src>>),
  Quoted(Box<Expression<'src>>),
  Quasiquoted(Box<Expression<'src>>),
  Unquoted(Box<Expression<'src>>),
  UnquoteSpliced(Box<Expression<'src>>),
}

impl Display for Expression<'_> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Expression::Atom(atom) => write!(f, "{}", atom),
      Expression::List(list) => {
        write!(f, "(")?;
        for (i, expr) in list.iter().enumerate() {
          if i > 0 {
            write!(f, " ")?;
          }
          write!(f, "{}", expr)?;
        }
        write!(f, ")")
      }
      Expression::DottedList(list, tail) => {
        write!(f, "(")?;
        for (i, expr) in list.iter().enumerate() {
          if i > 0 {
            write!(f, " ")?;
          }
          write!(f, "{}", expr)?;
        }
        write!(f, " . {})", tail)
      }
      Expression::Vector(vector) => {
        write!(f, "[")?;
        for (i, expr) in vector.iter().enumerate() {
          if i > 0 {
            write!(f, " ")?;
          }
          write!(f, "{}", expr)?;
        }
        write!(f, "]")
      }
      Expression::Quoted(expr) => write!(f, "'{}", expr),
      Expression::Quasiquoted(expr) => write!(f, "`{}", expr),
      Expression::Unquoted(expr) => write!(f, ",{}", expr),
      Expression::UnquoteSpliced(expr) => write!(f, ",@{}", expr),
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Atom<'src> {
  Boolean(bool),
  Number(Number<'src>),
  String(&'src str),
  Character(char),
  Symbol(&'src str),
}

impl Display for Atom<'_> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Atom::Boolean(true) => write!(f, "#t"),
      Atom::Boolean(false) => write!(f, "#f"),
      Atom::Number(num) => write!(f, "{}", num),
      Atom::String(s) => write!(f, "\"{}\"", s),
      Atom::Character(c) => write!(f, "#\\{}", c),
      Atom::Symbol(s) => write!(f, "{}", s),
    }
  }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum Number<'src> {
  Integer(i64),
  Float(f64),
  Rational(i64, i64),
  Complex(Box<Number<'src>>, Box<Number<'src>>),
  Unparsed(&'src str),
}

impl Display for Number<'_> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      Number::Integer(i) => write!(f, "{}", i),
      Number::Float(n) => write!(f, "{}", n),
      Number::Rational(num, denom) => write!(f, "{}/{}", num, denom),
      Number::Complex(real, imag) => {
        if let Number::Integer(imag_val) = **imag {
          if imag_val >= 0 {
            write!(f, "{}+{}i", real, imag_val)
          } else {
            write!(f, "{}{}i", real, imag_val)
          }
        } else {
          write!(f, "{}+{}i", real, imag)
        }
      }
      Number::Unparsed(s) => write!(f, "{}", s),
    }
  }
}
