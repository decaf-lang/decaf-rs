#![feature(proc_macro_hygiene)] // allow proc macro output macro definition

pub mod ast;
pub mod parser;
pub mod parser_ll;
pub mod ty;
pub mod symbol;

pub use ast::*;
pub use ty::*;
pub use symbol::*;

// below are some helper functions for parser

use common::{Loc, Errors, ErrorKind, NO_LOC};

// save a little typing than writing "Default::default()"
pub(crate) fn dft<T: Default>() -> T { T::default() }

pub(crate) fn mk_stmt(loc: Loc, kind: StmtKind) -> Stmt { Stmt { loc, kind } }

pub(crate) fn mk_expr(loc: Loc, kind: ExprKind) -> Expr { Expr { loc, ty: dft(), kind } }

pub(crate) fn mk_int_lit<'a, T>(loc: Loc, s: &'a str, error: &mut Errors<'a, T>) -> Expr<'a> {
  let val = if s.starts_with("0x") { i32::from_str_radix(&s[2..], 16) } else { s.parse() }
    .unwrap_or_else(|_| error.issue(loc, ErrorKind::IntTooLarge(s)));
  mk_expr(loc, val.into())
}

// make a block from a single statement(which may already be a block)
fn mk_block(s: Stmt) -> Block {
  if let StmtKind::Block(b) = s.kind { b } else { Block { loc: s.loc, stmt: vec![s], scope: dft() } }
}

pub(crate) trait VecExt: Sized {
  type Item;

  fn pushed(self, i: <Self as VecExt>::Item) -> Self;

  fn reversed(self) -> Self;
}

impl<T> VecExt for Vec<T> {
  type Item = T;

  fn pushed(mut self, i: Self::Item) -> Self { (self.push(i), self).1 }

  fn reversed(mut self) -> Self { (self.reverse(), self).1 }
}

// assume s begin with ", this is not checked
pub(crate) fn check_str<'a, T>(s: &'a str, error: &mut Errors<'a, T>, mut loc: Loc) {
  if s.len() <= 1 || !s.ends_with('"') {
    error.issue(loc, ErrorKind::UnclosedStr(&s[1..]))
  }
  let s = &s[1..s.len() - 1];
  loc.next_col();
  let mut escape = NO_LOC;
  let mut idx = 0;
  for ch in s.chars() {
    idx += ch.len_utf8();
    match ch {
      '\\' => escape = if escape == NO_LOC { loc } else { NO_LOC },
      'n' | 'r' | 't' | '"' => escape = NO_LOC,
      '\r' => continue, // just ignore
      _ => {
        if escape != NO_LOC {
          error.issue::<()>(escape, ErrorKind::InvalidEscape);
          escape = NO_LOC;
        }
        // for NewlineInStr error, the reported string segment is from beginning to(including) this '\n'
        // (though I don't think it is very sensible, I think reporting the whole string will be better)
        if ch == '\n' { error.issue(loc, ErrorKind::NewlineInStr(&s[0..idx])) }
      }
    }
    if ch == '\n' { loc.next_line(); } else { loc.next_col(); }
  }
  if escape != NO_LOC {
    error.issue(escape, ErrorKind::InvalidEscape)
  }
}