use crate::{ClassDef, FuncDef};
use common::{Loc, Ref};
use std::fmt;

#[derive(Eq, PartialEq)]
pub enum SynTyKind<'a> {
  Int,
  Bool,
  String,
  Void,
  Named(&'a str),
}

#[derive(Eq, PartialEq)]
pub struct SynTy<'a> {
  pub loc: Loc,
  pub arr: u32,
  pub kind: SynTyKind<'a>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum TyKind<'a> {
  Int,
  Bool,
  String,
  Void,
  Error,
  Null,
  // `Object` is `class A a` <- this `a`
  Object(Ref<'a, ClassDef<'a>>),
  // `Class` is `Class A { }` <- this `A`
  Class(Ref<'a, ClassDef<'a>>),
  // [0] = ret, [1..] = param
  Func(&'a [Ty<'a>]),
}

impl Default for TyKind<'_> {
  fn default() -> Self { TyKind::Error }
}

// arr > 0 <-> is array, for error/void type, arr can only be 0
#[derive(Clone, Copy, Eq, PartialEq, Default)]
pub struct Ty<'a> {
  pub arr: u32,
  pub kind: TyKind<'a>,
}

impl<'a> Ty<'a> {
  // make a type with array dimension = 0
  pub const fn new(kind: TyKind<'a>) -> Ty<'a> { Ty { arr: 0, kind } }

  // like Errors::issue, it can save some typing by returning a default value
  pub fn error_or<T: Default>(self, mut f: impl FnMut() -> T) -> T {
    if self == Ty::error() { T::default() } else { f() }
  }

  pub fn assignable_to(&self, rhs: Ty<'a>) -> bool {
    use TyKind::*;
    match (self.kind, rhs.kind) {
      (Error, _) | (_, Error) => true,
      _ if self.arr == rhs.arr => if self.arr == 0 {
        match (self.kind, rhs.kind) {
          (Int, Int) | (Bool, Bool) | (String, String) | (Void, Void) => true,
          (Object(c1), Object(Ref(c2))) => c1.extends(c2),
          (Null, Object(_)) => true,
          (Func(rp1), Func(rp2)) => {
            let (r1, p1, r2, p2) = (&rp1[0], &rp1[1..], &rp2[0], &rp2[1..]);
            r1.assignable_to(*r2) && p1.len() == p2.len() && p1.iter().zip(p2.iter()).all(|(p1, p2)| p2.assignable_to(*p1))
          }
          _ => false,
        }
      } else { *self == rhs }
      _ => false,
    }
  }

  // why don't use const items?
  // it seems that const items can only have type Ty<'static>, which can NOT be casted to Ty<'a>
  pub const fn error() -> Ty<'a> { Ty::new(TyKind::Error) }
  pub const fn null() -> Ty<'a> { Ty::new(TyKind::Null) }
  pub const fn int() -> Ty<'a> { Ty::new(TyKind::Int) }
  pub const fn bool() -> Ty<'a> { Ty::new(TyKind::Bool) }
  pub const fn void() -> Ty<'a> { Ty::new(TyKind::Void) }
  pub const fn string() -> Ty<'a> { Ty::new(TyKind::String) }

  pub fn mk_obj(c: &'a ClassDef<'a>) -> Ty<'a> { Ty::new(TyKind::Object(Ref(c))) }
  pub fn mk_class(c: &'a ClassDef<'a>) -> Ty<'a> { Ty::new(TyKind::Class(Ref(c))) }
  pub fn mk_func(f: &'a FuncDef<'a>) -> Ty<'a> { Ty::new(TyKind::Func(f.ret_param_ty.get().unwrap())) }

  // if you want something like `is_void()`, just use `== Ty::void()`
  pub fn is_arr(&self) -> bool { self.arr > 0 }
  pub fn is_func(&self) -> bool { self.arr == 0 && if let TyKind::Func(_) = self.kind { true } else { false } }
  pub fn is_class(&self) -> bool { self.arr == 0 && if let TyKind::Class(_) = self.kind { true } else { false } }
  pub fn is_object(&self) -> bool { self.arr == 0 && if let TyKind::Object(_) = self.kind { true } else { false } }
}

impl fmt::Debug for Ty<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match &self.kind {
      TyKind::Int => write!(f, "int"),
      TyKind::Bool => write!(f, "bool"),
      TyKind::String => write!(f, "string"),
      TyKind::Void => write!(f, "void"),
      TyKind::Error => write!(f, "error"), // we don't expect to reach this case in printing scope info
      TyKind::Null => write!(f, "null"),
      TyKind::Object(c) | TyKind::Class(c) => write!(f, "class {}", c.name),
      // the printing format may be different from other experiment framework's
      // it is not because their format is hard to implement in rust, but because I simply don't like their format,
      // which introduces unnecessary complexity, and doesn't increase readability
      TyKind::Func(ret_param) => {
        let (ret, param) = (ret_param[0], &ret_param[1..]);
        write!(f, "{:?}(", ret)?;
        for (idx, p) in param.iter().enumerate() {
          write!(f, "{:?}{}", p, if idx + 1 == param.len() { "" } else { ", " })?;
        }
        write!(f, ")")
      }
    }?;
    for _ in 0..self.arr { write!(f, "[]")?; }
    Ok(())
  }
}