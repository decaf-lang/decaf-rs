use crate::{TypeCk, TypeCkTrait};
use common::{ErrorKind::*, Loc, LENGTH, BinOp, UnOp, ErrorKind, Ref};
use syntax::ast::*;
use syntax::{ScopeOwner, Symbol, ty::*};
use std::ops::{Deref, DerefMut};

pub(crate) struct TypePass<'a>(pub TypeCk<'a>);

impl<'a> Deref for TypePass<'a> {
  type Target = TypeCk<'a>;
  fn deref(&self) -> &Self::Target { &self.0 }
}

impl<'a> DerefMut for TypePass<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl<'a> TypePass<'a> {
  pub fn program(&mut self, p: &'a Program<'a>) {
    for c in &p.class { self.class_def(c); }
  }

  fn class_def(&mut self, c: &'a ClassDef<'a>) {
    self.cur_class = Some(c);
    self.scoped(ScopeOwner::Class(c), |s| for f in &c.field {
      if let FieldDef::FuncDef(f) = f {
        s.cur_func = Some(f);
        let ret = s.scoped(ScopeOwner::Param(f), |s| s.block(&f.body));
        if !ret && f.ret_ty() != Ty::void() { s.issue(f.body.loc, ErrorKind::NoReturn) }
      };
    });
  }

  fn block(&mut self, b: &'a Block<'a>) -> bool {
    let mut ret = false;
    self.scoped(ScopeOwner::Local(b), |s| for st in &b.stmt { ret = s.stmt(st); });
    ret
  }

  // return whether this stmt has a return value
  fn stmt(&mut self, s: &'a Stmt<'a>) -> bool {
    match &s.kind {
      StmtKind::Assign(a) => {
        let (l, r) = (self.expr(&a.dst), self.expr(&a.src));
        if !r.assignable_to(l) { self.issue(s.loc, IncompatibleBinary { l, op: "=", r }) }
        false
      }
      StmtKind::LocalVarDef(v) => {
        self.cur_var_def = Some(v);
        if let Some((loc, e)) = &v.init {
          let (l, r) = (v.ty.get(), self.expr(e));
          if !r.assignable_to(l) { self.issue(*loc, IncompatibleBinary { l, op: "=", r }) }
        }
        self.cur_var_def = None;
        false
      }
      StmtKind::ExprEval(e) => {
        self.expr(e);
        false
      }
      StmtKind::Skip(_) => false,
      StmtKind::If(i) => {
        self.check_bool(&i.cond);
        // `&` is not short-circuit evaluated
        self.block(&i.on_true) & i.on_false.as_ref().map(|b| self.block(b)).unwrap_or(false)
      }
      StmtKind::While(w) => {
        self.check_bool(&w.cond);
        self.loop_cnt += 1;
        self.block(&w.body);
        self.loop_cnt -= 1;
        false
      }
      StmtKind::For(f) => self.scoped(ScopeOwner::Local(&f.body), |s| {
        s.stmt(&f.init);
        s.check_bool(&f.cond);
        s.stmt(&f.update);
        for st in &f.body.stmt { s.stmt(st); } // not calling block(), because the scope is already opened
        false
      }),
      StmtKind::Return(r) => {
        let expect = self.cur_func.unwrap().ret_ty();
        let actual = r.as_ref().map(|e| self.expr(e)).unwrap_or(Ty::void());
        if !actual.assignable_to(expect) { self.issue(s.loc, ReturnMismatch { actual, expect }) }
        actual != Ty::void()
      }
      StmtKind::Print(p) => {
        for (i, e) in p.iter().enumerate() {
          let ty = self.expr(e);
          if ty != Ty::bool() && ty != Ty::int() && ty != Ty::string() {
            ty.error_or(|| self.issue(e.loc, BadPrintArg { loc: i as u32 + 1, ty }))
          }
        }
        false
      }
      StmtKind::Break(_) => {
        if self.loop_cnt == 0 { self.issue(s.loc, BreakOutOfLoop) }
        false
      }
      StmtKind::Block(b) => self.block(b),
    }
  }

  // e.ty is set to the return value
  fn expr(&mut self, e: &'a Expr<'a>) -> Ty<'a> {
    use ExprKind::*;
    let ty = match &e.kind {
      VarSel(v) => self.var_sel(v, e.loc),
      IndexSel(i) => {
        let (arr, idx) = (self.expr(&i.arr), self.expr(&i.idx));
        if idx != Ty::int() { idx.error_or(|| self.issue(e.loc, IndexNotInt)) }
        match arr {
          Ty { arr, kind } if arr > 0 => Ty { arr: arr - 1, kind },
          e => e.error_or(|| self.issue(i.arr.loc, IndexNotArray)),
        }
      }
      IntLit(_) | ReadInt(_) => Ty::int(), BoolLit(_) => Ty::bool(), StringLit(_) | ReadLine(_) => Ty::string(), NullLit(_) => Ty::null(),
      Call(c) => self.call(c, e.loc),
      Unary(u) => {
        let r = self.expr(&u.r);
        let (ty, op) = match u.op { UnOp::Neg => (Ty::int(), "-"), UnOp::Not => (Ty::bool(), "!"), };
        if r != ty { r.error_or(|| self.issue(e.loc, IncompatibleUnary { op, r })) }
        ty
      }
      Binary(b) => {
        use BinOp::*;
        let (l, r) = (self.expr(&b.l), self.expr(&b.r));
        if l == Ty::error() || r == Ty::error() {
          // not using wildcard match, so that if we add new operators in the future, compiler can tell us
          match b.op { Add | Sub | Mul | Div | Mod => Ty::int(), And | Or | Eq | Ne | Lt | Le | Gt | Ge => Ty::bool() }
        } else {
          let (ret, ok) = match b.op {
            Add | Sub | Mul | Div | Mod => (Ty::int(), l == Ty::int() && r == Ty::int()),
            Lt | Le | Gt | Ge => (Ty::bool(), l == Ty::int() && r == Ty::int()),
            Eq | Ne => (Ty::bool(), l.assignable_to(r) || r.assignable_to(l)),
            And | Or => (Ty::bool(), l == Ty::bool() && r == Ty::bool())
          };
          if !ok { self.issue(e.loc, IncompatibleBinary { l, op: b.op.to_op_str(), r }) }
          ret
        }
      }
      This(_) => {
        if self.cur_func.unwrap().static_ { self.issue(e.loc, ThisInStatic) }
        Ty::mk_obj(self.cur_class.unwrap())
      }
      NewClass(n) => if let Some(c) = self.scopes.lookup_class(n.name) {
        n.class.set(Some(c));
        Ty::mk_obj(c)
      } else { self.issue(e.loc, NoSuchClass(n.name)) },
      NewArray(n) => {
        let len = self.expr(&n.len);
        if len != Ty::int() { len.error_or(|| self.issue(n.len.loc, NewArrayNotInt)) }
        self.ty(&n.elem, true)
      }
      ClassTest(c) => {
        let src = self.expr(&c.expr);
        if !src.is_object() { src.error_or(|| self.issue(e.loc, NotObject(src))) }
        if let Some(cl) = self.scopes.lookup_class(c.name) {
          c.class.set(Some(cl));
          Ty::bool()
        } else { self.issue(e.loc, NoSuchClass(c.name)) }
      }
      ClassCast(c) => {
        let src = self.expr(&c.expr);
        if !src.is_object() { src.error_or(|| self.issue(e.loc, NotObject(src))) }
        if let Some(cl) = self.scopes.lookup_class(c.name) {
          c.class.set(Some(cl));
          Ty::mk_obj(cl)
        } else { self.issue(e.loc, NoSuchClass(c.name)) }
      }
    };
    e.ty.set(ty);
    ty
  }

  fn var_sel(&mut self, v: &'a VarSel<'a>, loc: Loc) -> Ty<'a> {
    // (no owner)not_found_var / ClassName(no field) / (no owner)method => UndeclaredVar
    // object.not_found_var => NoSuchField
    // (no owner)field_var && cur function is static => RefInStatic
    // <not object>.a (e.g.: Class.a, 1.a) / object.method => BadFieldAccess
    // object.field_var, where object's class is not self or any of ancestors => PrivateFieldAccess

    if let Some(owner) = &v.owner {
      self.cur_used = true;
      let owner = self.expr(owner);
      self.cur_used = false;
      match owner {
        Ty { arr: 0, kind: TyKind::Object(Ref(c)) } => if let Some(sym) = c.lookup(v.name) {
          match sym {
            Symbol::Var(var) => {
              v.var.set(Some(var));
              // only allow self & descendents to access field
              if !self.cur_class.unwrap().extends(c) {
                self.issue(loc, PrivateFieldAccess { name: v.name, owner })
              }
              var.ty.get()
            }
            _ => self.issue(loc, BadFieldAccess { name: v.name, owner }),
          }
        } else { self.issue(loc, NoSuchField { name: v.name, owner }) },
        e => e.error_or(|| self.issue(loc, BadFieldAccess { name: v.name, owner })),
      }
    } else {
      // if this stmt is in an VarDef, it cannot access the variable that is being declared
      if let Some(sym) = self.scopes.lookup_before(v.name, self.cur_var_def.map(|v| v.loc).unwrap_or(loc)) {
        match sym {
          Symbol::Var(var) => {
            v.var.set(Some(var));
            if var.owner.get().unwrap().is_class() {
              let cur = self.cur_func.unwrap();
              if cur.static_ {
                self.issue(loc, RefInStatic { field: v.name, func: cur.name })
              }
            }
            var.ty.get()
          }
          Symbol::Class(c) if self.cur_used => { Ty::mk_class(c) }
          _ => self.issue(loc, UndeclaredVar(v.name)),
        }
      } else { self.issue(loc, UndeclaredVar(v.name)) }
    }
  }

  fn call(&mut self, c: &'a Call<'a>, loc: Loc) -> Ty<'a> {
    let v = if let ExprKind::VarSel(v) = &c.func.kind { v } else { unimplemented!() };
    let owner = if let Some(owner) = &v.owner {
      self.cur_used = true;
      let owner = self.expr(owner);
      self.cur_used = false;
      if owner == Ty::error() { return Ty::error(); }
      if v.name == LENGTH && owner.is_arr() {
        if !c.arg.is_empty() {
          self.issue(loc, LengthWithArgument(c.arg.len() as u32))
        }
        return Ty::int();
      }
      owner
    } else { Ty::mk_obj(self.cur_class.unwrap()) };
    match owner {
      Ty { arr: 0, kind: TyKind::Object(Ref(cl)) } | Ty { arr: 0, kind: TyKind::Class(Ref(cl)) } => {
        if let Some(sym) = cl.lookup(v.name) {
          match sym {
            Symbol::Func(f) => {
              c.func_ref.set(Some(f));
              if owner.is_class() && !f.static_ {
                // Class.not_static_method()
                self.issue(loc, BadFieldAccess { name: v.name, owner })
              }
              if v.owner.is_none() {
                let cur = self.cur_func.unwrap();
                if cur.static_ && !f.static_ {
                  self.issue(loc, RefInStatic { field: f.name, func: cur.name })
                }
              }
              self.check_arg_param(&c.arg, f.ret_param_ty.get().unwrap(), f.name, loc)
            }
            _ => self.issue(loc, NotFunc { name: v.name, owner }),
          }
        } else { self.issue(loc, NoSuchField { name: v.name, owner }) }
      }
      _ => self.issue(loc, BadFieldAccess { name: v.name, owner }),
    }
  }
}

impl<'a> TypePass<'a> {
  fn check_bool(&mut self, e: &'a Expr<'a>) {
    let ty = self.expr(e);
    if ty != Ty::bool() { ty.error_or(|| self.issue(e.loc, TestNotBool)) }
  }

  fn check_arg_param(&mut self, arg: &'a [Expr<'a>], ret_param: &[Ty<'a>], name: &'a str, loc: Loc) -> Ty<'a> {
    let (ret, param) = (ret_param[0], &ret_param[1..]);
    if param.len() != arg.len() {
      self.issue(loc, ArgcMismatch { name, expect: param.len() as u32, actual: arg.len() as u32 })
    }
    for (idx, arg0) in arg.iter().enumerate() {
      let arg = self.expr(arg0);
      if let Some(&param) = param.get(idx) {
        if !arg.assignable_to(param) {
          self.issue(arg0.loc, ArgMismatch { loc: idx as u32 + 1, arg, param })
        }
      }
    }
    ret
  }
}