use std::fmt;

// Loc(line, column), counting from 1
// so 0 is invalid for both, and Loc(0, 0) means NO_LOC
// (of course we can use Option<Loc>, but I think NO_LOC is also convenient to use, and it saves space)
#[derive(Copy, Clone, Eq, PartialEq, Default, Ord, PartialOrd)]
pub struct Loc(pub u32, pub u32);

pub const NO_LOC: Loc = Loc(0, 0);

impl Loc {
  pub fn next_line(&mut self) {
    self.0 += 1;
    self.1 = 1;
  }

  pub fn next_col(&mut self) { self.1 += 1; }
}

impl fmt::Debug for Loc {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "({},{})", self.0, self.1)
  }
}