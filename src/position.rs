#[derive(Copy, Clone, PartialEq, Debug)]
pub(crate) struct Position {
  pub(crate) column: usize,
  pub(crate) line: usize,
  pub(crate) offset: usize,
}

impl Position {
  pub fn new() -> Self {
    Position {
      column: 1,
      line: 1,
      offset: 0,
    }
  }

  pub fn advance(&mut self, c: char) {
    self.offset += c.len_utf8();

    if c == '\n' {
      self.line += 1;
      self.column = 1;
    } else {
      self.column += 1;
    }
  }
}
