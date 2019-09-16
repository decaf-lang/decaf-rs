use common::Loc;
use syntax::{ScopeOwner, Symbol, ClassDef};

pub(crate) struct ScopeStack<'a> {
  pub stack: Vec<ScopeOwner<'a>>,
}

impl<'a> ScopeStack<'a> {
  pub fn lookup(&self, name: &'a str, recursive: bool) -> Option<(Symbol<'a>, ScopeOwner<'a>)> {
    if recursive {
      for owner in self.stack.iter().rev() {
        if let Some(&symbol) = owner.scope().get(name) {
          return Some((symbol, *owner));
        }
      }
      None
    } else {
      self.stack.last().unwrap().scope().get(name)
        .map(|&symbol| (symbol, *self.stack.last().unwrap()))
    }
  }

  pub fn lookup_before(&self, name: &'a str, loc: Loc) -> Option<Symbol<'a>> {
    for owner in self.stack.iter().rev() {
      let symbols = owner.scope();
      if let Some(&symbol) = symbols.get(name) {
        if owner.is_local() && symbol.loc() >= loc {
          continue;
        }
        return Some(symbol);
      }
    }
    None
  }

  pub fn declare(&mut self, symbol: Symbol<'a>) {
    self.stack.last().unwrap().scope_mut().insert(symbol.name(), symbol);
  }

  pub fn open(&mut self, owner: ScopeOwner<'a>) {
    if let ScopeOwner::Class(c) = owner {
      if let Some(p) = c.parent_ref.get() {
        self.open(ScopeOwner::Class(p));
      }
    }
    self.stack.push(owner);
  }

  pub fn close(&mut self) {
    let owner = self.stack.pop().unwrap();
    if let ScopeOwner::Class(_) = owner {
      // all stack in the stack except the bottom are parent of the class
      for _ in 1..self.stack.len() { self.stack.pop(); }
    }
  }

  pub fn cur_owner(&self) -> ScopeOwner<'a> {
    *self.stack.last().unwrap()
  }

  pub fn lookup_class(&self, name: &'a str) -> Option<&'a ClassDef<'a>> {
    self.stack[0].scope().get(name).map(|class| match class {
      Symbol::Class(c) => *c,
      _ => unreachable!("Global scope should only contain classes."),
    })
  }
}