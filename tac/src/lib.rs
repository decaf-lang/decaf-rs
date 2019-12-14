pub mod iter;

pub use iter::TacIter;

use common::{BinOp, UnOp, IndexSet};
use std::{cell::Cell, fmt::{self, Debug}};
use typed_arena::Arena;

#[derive(Default)]
pub struct TacProgram<'a> {
  pub vtbl: Vec<VTbl<'a>>,
  pub func: Vec<TacFunc<'a>>,
  pub str_pool: IndexSet<&'a str>,
}

pub struct VTbl<'a> {
  // parent is index in Program::vtbl
  pub parent: Option<u32>,
  pub class: &'a str,
  // element in `func` is index in Program::func
  pub func: Vec<u32>,
}

pub struct TacFunc<'a> {
  pub param_num: u32,
  pub reg_num: u32,
  // we don't store the number of tac here, so we can't use TacIter
  // TacIter has more functions than we need to iterate over a function, but such functions are unnecessary
  pub first: Option<&'a TacNode<'a>>,
  pub last: Option<&'a TacNode<'a>>,
  pub alloc: &'a Arena<TacNode<'a>>,
  pub name: String,
}

impl<'a> TacFunc<'a> {
  pub fn empty(alloc: &'a Arena<TacNode<'a>>, name: String, param_num: u32) -> TacFunc<'a> {
    TacFunc { param_num, reg_num: 0, first: None, last: None, alloc, name }
  }

  pub fn push(&mut self, t: Tac) -> &mut Self {
    let tac = self.alloc.alloc(TacNode { tac: t.into(), prev: None.into(), next: None.into() });
    if let Some(last) = &mut self.last {
      tac.prev.set(Some(last));
      last.next.set(Some(tac));
      *last = tac;
    } else {
      self.first = Some(tac);
      self.last = Some(tac);
    }
    self
  }
}

pub struct TacNode<'a> {
  pub tac: Cell<Tac>,
  pub prev: Cell<Option<&'a TacNode<'a>>>,
  pub next: Cell<Option<&'a TacNode<'a>>>,
}

// `u32` can either mean register number or label id, its meaning is easy to distinguish according to the context
// use array to allow function `rw(_mut)` return a slice
#[derive(Copy, Clone)]
pub enum Tac {
  Bin { op: BinOp, dst: u32, lr: [Operand; 2] },
  Un { op: UnOp, dst: u32, r: [Operand; 1] },
  Assign { dst: u32, src: [Operand; 1] },
  Param { src: [Operand; 1] },
  // if there is CallHint in `kind`: obj == true => it can change result of Load Obj, arr == true => like Obj
  // else (now only intrinsic call) => it doesn't affect any Load result
  Call { dst: Option<u32>, kind: CallKind },
  Ret { src: Option<[Operand; 1]> },
  // label in Jmp & Je & Jne & Label
  Jmp { label: u32 },
  // Jif stands for Jz and Jnz, determined by `z`
  Jif { label: u32, z: bool, cond: [Operand; 1] },
  Label { label: u32 },
  // `hint` can help common expression elimination since we don't have alias analysis yet
  // for Load: Immutable => result only depends on base + off, Obj => Store to Obj can change result, Arr => like Obj
  // for Store: Immutable => it doesn't affect any Load result, Obj => correspond to Obj in Load, Arr => like Obj
  Load { dst: u32, base: [Operand; 1], off: i32, hint: MemHint },
  Store { src_base: [Operand; 2], off: i32, hint: MemHint },
  // s: the index in TacProgram::str_pool
  LoadStr { dst: u32, s: u32 },
  // v: the index in TacProgram::vtbl
  LoadVTbl { dst: u32, v: u32 },
  // v: the index in TacProgram::func
  LoadFunc { dst: u32, f: u32 },
}

impl Tac {
  // r can be Operand, but w can only be reg, and there is at most 1 w
  pub fn rw(&self) -> (&[Operand], Option<u32>) {
    use Tac::*;
    match self {
      Bin { dst, lr, .. } => (lr, Some(*dst)),
      Un { dst, r, .. } | Assign { dst, src: r } | Load { dst, base: r, .. } => (r, Some(*dst)),
      Param { src } => (src, None),
      Call { dst, kind } => (if let CallKind::Virtual(fp, _) = kind { fp } else { &[] }, *dst),
      Ret { src } => (src.as_ref().map(|src| src.as_ref()).unwrap_or(&[]), None),
      Jmp { .. } | Label { .. } => (&[], None),
      Jif { cond, .. } => (cond, None),
      Store { src_base, .. } => (src_base, None),
      LoadStr { dst, .. } | LoadVTbl { dst, .. } | LoadFunc { dst, .. } => (&[], Some(*dst)),
    }
  }

  // basically copied from `rw`, there is no better way in rust to write two functions, one is &self -> &result, another is &mut self -> &mut result
  // for example, the implementation of Iter and IterMut in many std collections are almost duplicate codes
  pub fn rw_mut(&mut self) -> (&mut [Operand], Option<&mut u32>) {
    use Tac::*;
    match self {
      Bin { dst, lr, .. } => (lr, Some(dst)),
      Un { dst, r, .. } | Assign { dst, src: r } | Load { dst, base: r, .. } => (r, Some(dst)),
      Param { src } => (src, None),
      Call { dst, kind } =>
        (if let CallKind::Virtual(fp, _) = kind { fp } else { &mut [] }, dst.as_mut()),
      Ret { src } => (src.as_mut().map(|src| src.as_mut()).unwrap_or(&mut []), None),
      Jmp { .. } | Label { .. } => (&mut [], None),
      Jif { cond, .. } => (cond, None),
      Store { src_base, .. } => (src_base, None),
      LoadStr { dst, .. } | LoadVTbl { dst, .. } | LoadFunc { dst, .. } => (&mut [], Some(dst)),
    }
  }
}

#[derive(Copy, Clone)]
pub enum CallKind {
  Virtual([Operand; 1], CallHint),
  // the index of func in TacProgram, can be static OR NEW
  Static(u32, CallHint),
  Intrinsic(Intrinsic),
}

#[derive(Copy, Clone, Hash, Eq, PartialEq)]
pub enum Operand { Reg(u32), Const(i32) }

impl Debug for Operand {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self { Operand::Reg(r) => write!(f, "%{}", r), Operand::Const(c) => write!(f, "{}", c) }
  }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Intrinsic { _Alloc, _ReadLine, _ReadInt, _StringEqual, _PrintInt, _PrintString, _PrintBool, _Halt }

impl Intrinsic {
  pub fn has_ret(self) -> bool {
    use Intrinsic::*;
    match self { _Alloc | _ReadLine | _ReadInt | _StringEqual => true, _PrintInt | _PrintString | _PrintBool | _Halt => false }
  }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum MemHint { Immutable, Obj, Arr }

#[derive(Copy, Clone)]
pub struct CallHint {
  pub arg_obj: bool,
  pub arg_arr: bool,
}

pub const INT_SIZE: i32 = 4;

pub const INDEX_OUT_OF_BOUND: &str = r#"Decaf runtime error: Array subscript out of bounds\n"#;
pub const NEW_ARR_NEG: &str = r#"Decaf runtime error: Cannot create negative-sized array\n"#;
pub const BAD_CAST1: &str = r#"Decaf runtime error: "#;
pub const BAD_CAST2: &str = r#" cannot be cast to "#;
pub const BAD_CAST3: &str = r#"\n"#;