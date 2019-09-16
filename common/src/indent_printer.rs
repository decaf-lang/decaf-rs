use crate::{INDENT, INDENT_STR};
use std::fmt;

#[derive(Default)]
pub struct IndentPrinter {
  indent: String,
  content: String,
}

impl IndentPrinter {
  #[inline(always)]
  pub fn indent(&mut self, f: impl FnOnce(&mut IndentPrinter)) {
    self.inc();
    f(self);
    self.dec();
  }

  // in the most cases you don't need to use inc and dec directly
  pub fn inc(&mut self) { self.indent += INDENT_STR; }

  pub fn dec(&mut self) { for _ in 0..INDENT { self.indent.pop(); } }

  pub fn finish(self) -> String { self.content }
}

// this implementation add '\n' to content by default, so use write!(...) for a normal new line text
// for an empty new line, still need writeln!(p) or write!(p, "\n")
impl fmt::Write for IndentPrinter {
  fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
    for l in s.lines() {
      self.content += self.indent.as_ref();
      self.content += l;
      self.content.push('\n');
    }
    Ok(())
  }

  // args need to be formatted with the default formatter instead of IndentPrinter
  fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> Result<(), fmt::Error> {
    self.write_str(&format!("{}", args))
  }
}