use crate::{TypeCk, TypeCkTrait};
use common::{ErrorKind::*, Ref, MAIN_CLASS, MAIN_METHOD, NO_LOC, HashMap, HashSet};
use syntax::{ast::*, ScopeOwner, Symbol, Ty};
use std::{mem::discriminant, ops::{Deref, DerefMut}, iter};

pub(crate) struct SymbolPass<'a>(pub TypeCk<'a>);

// some boilerplate code...
impl<'a> Deref for SymbolPass<'a> {
  type Target = TypeCk<'a>;
  fn deref(&self) -> &Self::Target { &self.0 }
}

impl<'a> DerefMut for SymbolPass<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl<'a> SymbolPass<'a> {
  pub fn program(&mut self, p: &'a Program<'a>) {
    self.scoped(ScopeOwner::Global(p), |s| {
      for c in &p.class {
        if let Some(prev) = s.scopes.lookup_class(c.name) {
          s.errors.issue(c.loc, ConflictDeclaration { prev: prev.loc, name: c.name })
        } else {
          s.scopes.declare(Symbol::Class(c));
        }
      }
      // detect cyclic inheritance
      let mut inherit_order = HashMap::new();
      fn calc_order<'a>(c: &'a ClassDef<'a>, inherit_order: &mut HashMap<Ref<'a, ClassDef<'a>>, u32>) -> u32 {
        match inherit_order.get(&Ref(c)) {
          Some(&o) => o,
          None => {
            let o = match c.parent_ref.get() {
              Some(p) => calc_order(p, inherit_order) + 1,
              None => 0,
            };
            inherit_order.insert(Ref(c), o);
            o
          }
        }
      }
      // errors related to inheritance are considered as fatal errors, return at once if occurred
      for c in &p.class {
        if let Some(p) = c.parent {
          match s.scopes.lookup_class(p) {
            Some(p) => {
              c.parent_ref.set(Some(p));
              if calc_order(c, &mut inherit_order) <= calc_order(p, &mut inherit_order) {
                return s.errors.issue(c.loc, CyclicInheritance);
              }
            }
            None => { return s.errors.issue(c.loc, NoSuchClass(p)); }
          }
        }
      }
      for c in &p.class {
        s.class_def(c);
        if c.name == MAIN_CLASS {
          p.main.set(Some(c));
        }
      }
      let mut checked = HashSet::new();
      for c in &p.class { s.check_override(c, &mut checked); }
      s.check_main(p);
    });
  }

  fn class_def(&mut self, c: &'a ClassDef<'a>) {
    self.cur_class = Some(c);
    self.scoped(ScopeOwner::Class(c), |s| for f in &c.field {
      match f { FieldDef::FuncDef(f) => s.func_def(f), FieldDef::VarDef(v) => s.var_def(v) };
    });
  }

  fn func_def(&mut self, f: &'a FuncDef<'a>) {
    let ret_ty = self.ty(&f.ret, false);
    if let Some((prev, _)) = self.scopes.lookup(f.name, false) {
      self.errors.issue(f.loc, ConflictDeclaration { prev: prev.loc(), name: f.name })
    } else {
      self.scopes.declare(Symbol::Func(f));
    }
    self.scoped(ScopeOwner::Param(f), |s| {
      if !f.static_ {
        s.scopes.declare(Symbol::This(f));
      }
      for v in &f.param { s.var_def(v); }
      s.block(&f.body);
    });
    let ret_param_ty = iter::once(ret_ty)
      .chain(f.param.iter().map(|v| v.ty.get()));
    let ret_param_ty = self.alloc.ty.alloc_extend(ret_param_ty);
    f.ret_param_ty.set(Some(ret_param_ty));
    f.class.set(self.cur_class);
  }

  fn var_def(&mut self, v: &'a VarDef<'a>) {
    v.ty.set(self.ty(&v.syn_ty, false));
    if v.ty.get() == Ty::void() {
      return self.errors.issue(v.loc, VoidVar(v.name));
    }
    // whether it is ok to declare this var
    let ok = if let Some((symbol, owner)) = self.scopes.lookup(v.name, true) {
      // discriminant(..) == discriminant(..): conflict if they are of the same category, the value doesn't matter
      // for example, `scopes` cannot contain a symbol belonging to another class, so if they are both Class, this must be a conflict
      // owner.is_param(): `owner` belongs to the previously defined symbol, if it is param, it implies that cur symbol can only be param or local
      if discriminant(&self.scopes.cur_owner()) == discriminant(&owner) || owner.is_param() {
        self.errors.issue(v.loc, ConflictDeclaration { prev: symbol.loc(), name: v.name })
      } else { true }
    } else { true };
    if ok {
      v.owner.set(Some(self.scopes.cur_owner()));
      self.scopes.declare(Symbol::Var(v));
    }
  }

  fn block(&mut self, b: &'a Block<'a>) {
    self.scoped(ScopeOwner::Local(b), |s| for st in &b.stmt { s.stmt(st); });
  }

  fn stmt(&mut self, s: &'a Stmt<'a>) {
    match &s.kind {
      StmtKind::LocalVarDef(v) => self.var_def(v),
      StmtKind::If(i) => {
        self.block(&i.on_true);
        if let Some(of) = &i.on_false { self.block(of); }
      }
      StmtKind::While(w) => self.block(&w.body),
      StmtKind::For(f) => self.scoped(ScopeOwner::Local(&f.body), |s| {
        if let StmtKind::LocalVarDef(v) = &f.init.kind { s.var_def(v); }
        for st in &f.body.stmt { s.stmt(st); }
      }),
      StmtKind::Block(b) => self.block(b),
      _ => {}
    };
  }
}

impl<'a> SymbolPass<'a> {
  fn check_override(&mut self, c: &'a ClassDef<'a>, checked: &mut HashSet<Ref<'a, ClassDef<'a>>>) {
    if checked.contains(&Ref(c)) { return; }
    if let Some(p) = c.parent_ref.get() {
      self.scoped(ScopeOwner::Class(p), |s| {
        c.scope.borrow_mut().retain(|name, sym| {
          let sym = &*sym; // transform a mut ref to a ref, so it can be copied
          if let Some((p_sym, _)) = s.scopes.lookup(name, true) {
            match (sym, p_sym) {
              (Symbol::Func(_), Symbol::Var(_)) | (Symbol::Var(_), Symbol::Func(_)) => {
                s.errors.issue(sym.loc(), ConflictDeclaration { prev: p_sym.loc(), name })
              }
              (Symbol::Func(f), Symbol::Func(pf)) => {
                if f.static_ || pf.static_ {
                  s.errors.issue(f.loc, ConflictDeclaration { prev: pf.loc, name })
                } else if !f.ret_ty().assignable_to(pf.ret_ty()) || f.param.len() != pf.param.len() ||
                  !f.param.iter().zip(pf.param.iter()).all(|(f, pf)| pf.ty.get().assignable_to(f.ty.get())) {
                  s.errors.issue(f.loc, OverrideMismatch { func: name, p: p.name })
                } else { true }
              }
              (Symbol::Var(_), Symbol::Var(_)) => s.errors.issue(sym.loc(), OverrideVar(name)),
              _ => true, // maybe find another class, not concerning
            }
          } else { true }
        });
      });
    }
  }

  fn check_main(&mut self, p: &Program) {
    match p.main.get() {
      Some(main) if match main.scope.borrow().get(MAIN_METHOD) {
        Some(Symbol::Func(main)) if main.static_ && main.param.is_empty() && main.ret_ty() == Ty::void() => true,
        _ => false
      } => {}
      _ => { self.errors.issue(NO_LOC, NoMainClass) }
    };
  }
}
