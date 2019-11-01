use crate::{Block, ClassDef, FuncDef, VarDef, Program, Ty, show_func_ty};
use common::{Loc, HashMap};
use std::{cell::{RefMut, Ref}, fmt};

pub type Scope<'a> = HashMap<&'a str, Symbol<'a>>;

#[derive(Copy, Clone)]
pub enum Symbol<'a> {
  Var(&'a VarDef<'a>),
  Func(&'a FuncDef<'a>),
  This(&'a FuncDef<'a>),
  Class(&'a ClassDef<'a>),
}

impl<'a> Symbol<'a> {
  pub fn name(&self) -> &'a str {
    match self {
      Symbol::Var(v) => v.name,
      Symbol::Func(f) => f.name,
      Symbol::This(_) => "this",
      Symbol::Class(c) => c.name,
    }
  }

  pub fn loc(&self) -> Loc {
    match self {
      Symbol::Var(v) => v.loc,
      Symbol::Func(f) | Symbol::This(f) => f.loc,
      Symbol::Class(c) => c.loc,
    }
  }

  // for symbol This & Class, will return the type of their class object
  pub fn ty(&self) -> Ty<'a> {
    match self {
      Symbol::Var(v) => v.ty.get(),
      Symbol::Func(f) => Ty::mk_func(f),
      Symbol::This(f) => Ty::mk_obj(f.class.get().unwrap()),
      Symbol::Class(c) => Ty::mk_obj(c),
    }
  }

  pub fn is_var(&self) -> bool { if let Symbol::Var(_) = self { true } else { false } }
  pub fn is_func(&self) -> bool { if let Symbol::Func(_) = self { true } else { false } }
  pub fn is_this(&self) -> bool { if let Symbol::This(_) = self { true } else { false } }
  pub fn is_class(&self) -> bool { if let Symbol::Class(_) = self { true } else { false } }
}

#[derive(Copy, Clone)]
pub enum ScopeOwner<'a> {
  Local(&'a Block<'a>),
  Param(&'a FuncDef<'a>),
  Class(&'a ClassDef<'a>),
  Global(&'a Program<'a>),
}

impl<'a> ScopeOwner<'a> {
  // boilerplate code...
  pub fn scope(&self) -> Ref<'a, Scope<'a>> {
    use ScopeOwner::*;
    match self { Local(x) => x.scope.borrow(), Param(x) => x.scope.borrow(), Class(x) => x.scope.borrow(), Global(x) => x.scope.borrow(), }
  }

  pub fn scope_mut(&self) -> RefMut<'a, Scope<'a>> {
    use ScopeOwner::*;
    match self { Local(x) => x.scope.borrow_mut(), Param(x) => x.scope.borrow_mut(), Class(x) => x.scope.borrow_mut(), Global(x) => x.scope.borrow_mut(), }
  }

  pub fn is_local(&self) -> bool { if let ScopeOwner::Local(_) = self { true } else { false } }
  pub fn is_param(&self) -> bool { if let ScopeOwner::Param(_) = self { true } else { false } }
  pub fn is_class(&self) -> bool { if let ScopeOwner::Class(_) = self { true } else { false } }
  pub fn is_global(&self) -> bool { if let ScopeOwner::Global(_) = self { true } else { false } }
}

impl fmt::Debug for Symbol<'_> {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match self {
      Symbol::Var(v) => write!(f, "{:?} -> variable {}{} : {:?}", v.loc,
                               if v.owner.get().unwrap().is_param() { "@" } else { "" }, v.name, v.ty.get()),
      Symbol::Func(fu) => {
        write!(f, "{:?} -> {}function {} : ", fu.loc, if fu.static_ { "STATIC " } else { "" }, fu.name)?;
        show_func_ty(fu.param.iter().map(|v|v.ty.get()), fu.ret_ty(), false, f)
      }
      Symbol::This(fu) => write!(f, "{:?} -> variable @this : class {}", fu.loc, fu.class.get().unwrap().name),
      Symbol::Class(c) => {
        write!(f, "{:?} -> class {}", c.loc, c.name)?;
        if let Some(p) = c.parent_ref.get() { write!(f, " : {}", p.name) } else { Ok(()) }
      }
    }
  }
}