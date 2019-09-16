pub mod iter;

pub use iter::TacIter;

use common::{BinOp, UnOp, IndexSet};
use std::{fmt, cell::{Cell, RefCell}};
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
  pub max_reg: u32,
  // check validity of this function, whether it returns without returning a value
  pub has_ret: bool,
  pub tac_len: u32,
  // though normally we use first and last separately, if we write it as `first: Option<...>, last: Option<...>`
  // we will lose the information that they can only be both Some or both None
  pub first_last: Option<(&'a Tac<'a>, &'a Tac<'a>)>,
  pub alloc: &'a Arena<Tac<'a>>,
  pub name: FuncNameKind<'a>,
}

impl<'a> TacFunc<'a> {
  pub fn empty(alloc: &'a Arena<Tac<'a>>, name: FuncNameKind<'a>, param_num: u32, has_ret: bool) -> TacFunc<'a> {
    TacFunc { param_num, max_reg: 0, has_ret, tac_len: 0, first_last: None, alloc, name }
  }

  pub fn push(&mut self, t: TacKind) -> &mut Self {
    let tac = self.alloc.alloc(Tac { payload: TacPayload { kind: t }.into(), prev: None.into(), next: None.into() });
    self.tac_len += 1;
    match &mut self.first_last {
      None => self.first_last = Some((tac, tac)),
      Some((_, last)) => {
        tac.prev.set(Some(last));
        last.next.set(Some(tac));
        *last = tac;
      }
    }
    self
  }

  pub fn iter(&self) -> TacIter<'a> {
    TacIter::new(self.first_last.map(|(f, _)| f), self.first_last.map(|(_, l)| l), self.tac_len as usize)
  }
}

pub struct Tac<'a> {
  pub payload: RefCell<TacPayload>,
  pub prev: Cell<Option<&'a Tac<'a>>>,
  pub next: Cell<Option<&'a Tac<'a>>>,
}

// for compatibility, use a wrapper struct here instead of just using TacKind
pub struct TacPayload {
  pub kind: TacKind,
}

// unless specially noted, all u32 are register numbers
// use array to help function `rw(_mut)` return a slice
#[derive(Copy, Clone)]
pub enum TacKind {
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
  // Jif stands for Jz and Jnz, determined by z
  Jif { label: u32, z: bool, cond: [Operand; 1] },
  Label { label: u32 },
  // `hint` can help common expression elimination since we don't have alias analysis yet
  // for Load: Immutable => result only depends on base + off, Obj => Store to Obj can change result, Arr => like Obj
  // for Store: Immutable => it doesn't affect any Load result, Obj => correspond to Obj in Load, Arr => like Obj
  Load { dst: u32, base: [Operand; 1], off: i32, hint: MemHint },
  Store { src_base: [Operand; 2], off: i32, hint: MemHint },
  LoadInt { dst: u32, i: i32 },
  // s: the index in TacProgram::str_pool
  LoadStr { dst: u32, s: u32 },
  // v: the index in TacProgram::vtbl
  LoadVTbl { dst: u32, v: u32 },
}

impl TacKind {
  // r can be Operand, but w can only be reg, and there is at most 1 w
  pub fn rw(&self) -> (&[Operand], Option<u32>) {
    use TacKind::*;
    match self {
      Bin { dst, lr, .. } => (lr, Some(*dst)),
      Un { dst, r, .. } | Assign { dst, src: r } | Load { dst, base: r, .. } => (r, Some(*dst)),
      Param { src } => (src, None),
      Call { dst, kind } => (if let CallKind::Virtual(fp, _) = kind { fp } else { &[] }, *dst),
      Ret { src } => (src.as_ref().map(|src| src.as_ref()).unwrap_or(&[]), None),
      Jmp { .. } | Label { .. } => (&[], None),
      Jif { cond, .. } => (cond, None),
      Store { src_base, .. } => (src_base, None),
      LoadInt { dst, .. } | LoadStr { dst, .. } | LoadVTbl { dst, .. } => (&[], Some(*dst)),
    }
  }

  // basically copied from `rw`, there is no better way in rust to write two functions, one is &self -> &result, another is &mut self -> &mut result
  // for example, the implementation of Iter and IterMut in many std collections are almost duplicate codes
  pub fn rw_mut(&mut self) -> (&mut [Operand], Option<&mut u32>) {
    use TacKind::*;
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
      LoadInt { dst, .. } | LoadStr { dst, .. } | LoadVTbl { dst, .. } => (&mut [], Some(dst)),
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

#[derive(Copy, Clone, Eq, PartialEq, Debug, strum_macros::IntoStaticStr)]
pub enum Intrinsic { _Alloc, _ReadLine, _ReadInt, _StringEqual, _PrintInt, _PrintString, _PrintBool, _Halt }

impl Intrinsic {
  pub fn name(self) -> &'static str { self.into() } // `into` provided by strum_macros::IntoStaticStr

  pub fn has_ret(self) -> bool {
    use Intrinsic::*;
    match self {
      _Alloc | _ReadLine | _ReadInt | _StringEqual => true, _PrintInt | _PrintString | _PrintBool | _Halt => false
    }
  }
}

#[derive(Copy, Clone)]
pub enum FuncNameKind<'a> {
  Main,
  New { class: &'a str },
  Member { class: &'a str, func: &'a str },
}

impl fmt::Debug for FuncNameKind<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match self {
      FuncNameKind::Main => write!(f, "main"),
      FuncNameKind::New { class } => write!(f, "_{}_New", class),
      FuncNameKind::Member { class, func } => write!(f, "_{}.{}", class, func),
    }
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