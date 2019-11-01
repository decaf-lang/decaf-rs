mod scope_stack;
mod symbol_pass;
mod type_pass;

use common::{Errors, ErrorKind::*, Ref};
use syntax::{FuncDef, ClassDef, SynTy, SynTyKind, ScopeOwner, Ty, TyKind, Program, VarDef};
use typed_arena::Arena;
use std::ops::{Deref, DerefMut};
use crate::{symbol_pass::SymbolPass, type_pass::TypePass, scope_stack::ScopeStack};

// if you want to alloc other types, you can add them to TypeCkAlloc
#[derive(Default)]
pub struct TypeCkAlloc<'a> {
  pub ty: Arena<Ty<'a>>,
}

pub fn work<'a>(p: &'a Program<'a>, alloc: &'a TypeCkAlloc<'a>) -> Result<(), Errors<'a, Ty<'a>>> {
  let mut s = SymbolPass(TypeCk { errors: Errors(vec![]), scopes: ScopeStack::new(p), loop_cnt: 0, cur_used: false, cur_func: None, cur_class: None, cur_var_def: None, alloc });
  s.program(p);
  if !s.errors.0.is_empty() { return Err(s.0.errors.sorted()); }
  let mut t = TypePass(s.0);
  t.program(p);
  if !t.errors.0.is_empty() { return Err(t.0.errors.sorted()); }
  Ok(())
}

struct TypeCk<'a> {
  errors: Errors<'a, Ty<'a>>,
  scopes: ScopeStack<'a>,
  loop_cnt: u32,
  // `cur_used` is only used to determine 2 kinds of errors:
  // Class.var (cur_used == true) => BadFieldAssess; Class (cur_used == false) => UndeclaredVar
  cur_used: bool,
  cur_func: Option<&'a FuncDef<'a>>,
  cur_class: Option<&'a ClassDef<'a>>,
  // actually only use cur_var_def's loc
  // if cur_var_def is Some, will use it's loc to search for symbol in TypePass::var_sel
  // this can reject code like `int a = a;`
  cur_var_def: Option<&'a VarDef<'a>>,
  alloc: &'a TypeCkAlloc<'a>,
}

impl<'a> TypeCk<'a> {
  // is_arr can be helpful if you want the type of array while only having its element type (to avoid cloning other fields)
  fn ty(&mut self, s: &SynTy<'a>, is_arr: bool) -> Ty<'a> {
    let kind = match &s.kind {
      SynTyKind::Int => TyKind::Int,
      SynTyKind::Bool => TyKind::Bool,
      SynTyKind::String => TyKind::String,
      SynTyKind::Void => TyKind::Void,
      SynTyKind::Named(name) => if let Some(c) = self.scopes.lookup_class(name) {
        TyKind::Object(Ref(c))
      } else { self.issue(s.loc, NoSuchClass(name)) },
    };
    match kind {
      TyKind::Error => Ty::error(),
      TyKind::Void if s.arr != 0 => self.issue(s.loc, VoidArrayElement),
      _ => Ty { arr: s.arr + (is_arr as u32), kind }
    }
  }
}

impl<'a> Deref for TypeCk<'a> {
  type Target = Errors<'a, Ty<'a>>;
  fn deref(&self) -> &Self::Target { &self.errors }
}

impl<'a> DerefMut for TypeCk<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.errors }
}

trait TypeCkTrait<'a> {
  fn scoped<F: FnMut(&mut Self) -> R, R>(&mut self, s: ScopeOwner<'a>, f: F) -> R;
}

impl<'a, T: DerefMut<Target=TypeCk<'a>>> TypeCkTrait<'a> for T {
  fn scoped<F: FnMut(&mut Self) -> R, R>(&mut self, s: ScopeOwner<'a>, mut f: F) -> R {
    self.deref_mut().scopes.open(s);
    let ret = f(self);
    self.deref_mut().scopes.close();
    ret
  }
}