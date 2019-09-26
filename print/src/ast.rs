use common::{IndentPrinter, IgnoreResult};
use syntax::*;
use std::fmt::Write;

pub fn program(pr: &Program, p: &mut IndentPrinter) { pr.print(p); }

trait Printable {
  fn print(&self, p: &mut IndentPrinter);
}

// generate a impl block for Display types
macro_rules! print_basic {
  ($($t: ty)*) => {$(
    impl Printable for $t {
      fn print(&self, p: &mut IndentPrinter) { write!(p, "{}", self).ignore() }
    }
  )*};
}

print_basic!(i32 bool str);

impl<T: Printable> Printable for [T] {
  fn print(&self, p: &mut IndentPrinter) {
    write!(p, "List").ignore();
    p.indent(|p| if self.is_empty() { write!(p, "<empty>").ignore(); } else { for x in self { x.print(p); } })
  }
}

impl<T: Printable> Printable for Option<T> {
  fn print(&self, p: &mut IndentPrinter) {
    if let Some(x) = self { x.print(p); } else { write!(p, "<none>").ignore(); }
  }
}

impl<T: Printable> Printable for Box<T> {
  fn print(&self, p: &mut IndentPrinter) { self.as_ref().print(p); }
}

impl<T: Printable + ?Sized> Printable for &T {
  fn print(&self, p: &mut IndentPrinter) { (*self).print(p); }
}

impl Printable for SynTy<'_> {
  fn print(&self, p: &mut IndentPrinter) {
    for _ in 0..self.arr {
      write!(p, "TArray @ {:?}", self.loc).ignore();
      p.inc();
    }
    match &self.kind {
      SynTyKind::Int => write!(p, "TInt @ {:?}", self.loc).ignore(),
      SynTyKind::Bool => write!(p, "TBool @ {:?}", self.loc).ignore(),
      SynTyKind::String => write!(p, "TString @ {:?}", self.loc).ignore(),
      SynTyKind::Void => write!(p, "TVoid @ {:?}", self.loc).ignore(),
      SynTyKind::Named(c) => {
        write!(p, "TClass @ {:?}", self.loc).ignore();
        p.indent(|p| c.print(p));
      }
    }
    for _ in 0..self.arr { p.dec(); }
  }
}

// generate a impl block for struct, $name is the struct's name IN AST (which may be different or the same with struct's name)
// $field are expressions separated by spaces, they can access self's field, they will be printed sequentially
macro_rules! print_struct {
  ($t: ty, $self_: ident, $loc: expr, $name: ident, $($field: expr)*) => {
    impl Printable for $t {
      fn print(&$self_, p: &mut IndentPrinter) {
        write!(p, "{} @ {:?}", stringify!($name), $loc).ignore();
        p.indent(|p| { $($field.print(p);)* });
      }
    }
  };
}

// generate a match block for enum
// $variant is both the name of variant in enum and in ast, so the must have the same name
macro_rules! print_enum {
  ($e: expr, $loc: expr, $p: expr, $name: ident, $($variant: ident => $($field: expr)*),*) => {
    match &$e {
      $($variant($name) => {
        write!($p, "{} @ {:?}", stringify!($variant), $loc).ignore();
        $p.indent(|p| { $($field.print(p);)* });
      })*
    }
  };
}

// self.class[0] must be valid, because parser requires their are at least one class
print_struct!(Program<'_>, self, self.class[0].loc, TopLevel, self.class);
print_struct!(ClassDef<'_>, self, self.loc, ClassDef, self.name self.parent self.field);
print_struct!(VarDef<'_>, self, self.loc, LocalVarDef, self.syn_ty self.name self.init());
print_struct!(Block<'_>, self, self.loc, Block, self.stmt);

impl Printable for FieldDef<'_> {
  fn print(&self, p: &mut IndentPrinter) {
    match self {
      FieldDef::VarDef(v) => {
        write!(p, "VarDef @ {:?}", v.loc).ignore();
        p.indent(|p| {
          v.syn_ty.print(p);
          v.name.print(p);
          v.init().print(p);
        });
      }
      FieldDef::FuncDef(f) => {
        write!(p, "MethodDef @ {:?}", f.loc).ignore();
        p.indent(|p| {
          if f.static_ { "STATIC".print(p); }
          f.name.print(p);
          f.ret.print(p);
          f.param.print(p);
          f.body.print(p);
        });
      }
    }
  }
}

impl Printable for Stmt<'_> {
  #[allow(unused_variables)]
  fn print(&self, p: &mut IndentPrinter) {
    use StmtKind::*;
    print_enum!(self.kind, self.loc, p, x,
      Assign => x.dst x.src, LocalVarDef => x.syn_ty x.name x.init(), ExprEval => x, Skip => , If => x.cond x.on_true x.on_false,
      While => x.cond x.body, For => x.init x.cond x.update x.body, Return => x, Print => x, Break => , Block => x.stmt
    );
  }
}

impl Printable for Expr<'_> {
  #[allow(unused_variables)]
  fn print(&self, p: &mut IndentPrinter) {
    use ExprKind::*;
    print_enum!(self.kind, self.loc, p, x,
      VarSel => x.owner x.name, IndexSel => x.arr x.idx, IntLit => x, BoolLit => x, StringLit => "\"".to_owned() + x + "\"",
      NullLit => , Call => x.func x.arg, Unary => x.op.to_word_str() x.r, Binary => x.op.to_word_str() x.l x.r,
      This => , ReadInt => , ReadLine => , NewClass => x.name, NewArray => x.elem x.len, ClassTest => x.expr x.name,
      ClassCast => x.expr x.name
    );
  }
}
