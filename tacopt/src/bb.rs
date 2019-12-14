use tac::{TacNode, Tac, TacFunc, Operand, TacIter, CallKind, Intrinsic::_Halt};
use common::Ref;
use typed_arena::Arena;

pub struct BB<'a> {
  pub len: u32,
  // the ret/jmp/jif/label is NOT included in the link list defined by first -> last
  // don't forget that ret/jif may read a register in data flow analysis
  pub first: Option<&'a TacNode<'a>>,
  pub last: Option<&'a TacNode<'a>>,
  pub next: NextKind,
  pub prev: Vec<u32>,
}

#[derive(Copy, Clone)]
pub enum NextKind {
  Ret(Option<Operand>),
  Jmp(u32),
  // `cond` can only be Reg, if input tac's cond is a Const, it will be transformed into Jmp
  Jif { cond: u32, z: bool, fail: u32, jump: u32 },
  Halt,
}

impl BB<'_> {
  // return the out edges of this bb
  // there are 2 out edges in one bb at most, so the return value's type is `[Option<u32>; 2]`
  pub fn next(&self) -> [Option<u32>; 2] {
    match self.next {
      NextKind::Ret(_) | NextKind::Halt => [None, None],
      NextKind::Jmp(jump) => [Some(jump), None],
      NextKind::Jif { fail, jump, .. } => [Some(fail), Some(jump)],
    }
  }

  // returns the register id it reads(if any)
  pub fn next_r(&self) -> Option<u32> {
    match self.next {
      NextKind::Ret(r) => match r { Some(Operand::Reg(r)) => Some(r), _ => None }
      NextKind::Jif { cond, .. } => Some(cond),
      _ => None
    }
  }

  // returns mut ref to the register id it reads(if any)
  pub fn next_r_mut(&mut self) -> Option<&mut u32> {
    match &mut self.next {
      NextKind::Ret(r) => match r { Some(Operand::Reg(r)) => Some(r), _ => None }
      NextKind::Jif { cond, .. } => Some(cond),
      _ => None
    }
  }
}

impl<'a> BB<'a> {
  pub fn iter(&self) -> TacIter<'a> {
    TacIter::new(self.first, self.last, self.len as usize)
  }

  // delete `t` from the linked list in self
  // `t` should belong to that linked list, but it is not checked
  // the link on `t` is not cut down, so you can safely delete a tac while iterating over it
  pub fn del(&mut self, t: &'a TacNode<'a>) {
    self.len -= 1;
    match self.first {
      Some(first) if Ref(first) == Ref(t) => {
        first.prev.set(None);
        self.first = first.next.get();
      }
      _ => match self.last {
        Some(last) if Ref(last) == Ref(t) => {
          last.next.set(None);
          self.last = last.prev.get();
        }
        _ => {
          let (prev, next) = (t.prev.get().unwrap(), t.next.get().unwrap());
          next.prev.set(Some(prev));
          prev.next.set(Some(next));
        }
      }
    }
  }

  // insert `new` after `loc` in the linked list in self
  // `loc` should belong to that linked list, but it is not checked
  pub fn insert_after(&mut self, loc: &'a TacNode<'a>, new: &'a TacNode<'a>) {
    self.len += 1;
    match self.last {
      Some(last) if Ref(last) == Ref(loc) => {
        last.next.set(Some(new));
        new.prev.set(Some(last));
        self.last = Some(new);
      }
      _ => {
        let next = loc.next.get().unwrap();
        next.prev.set(Some(new));
        new.next.set(Some(next));
        loc.next.set(Some(new));
        new.prev.set(Some(loc));
      }
    }
  }

  // `prev_with_entry` means returning an iterator yielding `prev` list element
  // while adding an virtual entry node, which has an edge to the first node
  // `this` is self's index in FuncBB::bb + 1, so `this == 1` means that it is the first node
  pub fn prev_with_entry<'b>(&'b self, this: usize) -> (usize, impl IntoIterator<Item=usize> + Clone + 'b) {
    (this, self.prev.iter().map(|x| *x as usize + 1).chain(if this == 1 { Some(0) } else { None }))
  }
}

pub struct FuncBB<'a> {
  // some fields copied from TacFunc, they may change during optimization, so do copy rather than borrow
  pub param_num: u32,
  pub reg_num: u32,
  pub alloc: &'a Arena<TacNode<'a>>,
  pub bb: Vec<BB<'a>>,
  // I admit it is not perfect design, we need to clone func's name here for convenience
  // nevertheless, the affect on performance is very little
  pub name: String,
}

impl<'a> FuncBB<'a> {
  // construct control flow graph from `f`, the returned `FuncBB` contains such information
  // only `FuncBB` can be used for future optimization and codegen, and `TacFunc` cannot
  // `f` should returns or halts on every execution path, otherwise `simplify` will panic
  pub fn new(f: &TacFunc<'a>) -> FuncBB<'a> {
    let mut bb = Vec::new();
    let mut label2bb = Vec::new(); // label2bb[label id] = bb id of this label
    let mut labels = Vec::new(); // labels = {bb id | bb.next contains label id}
    let mut iter = f.first;
    while let Some(first) = iter {
      // is_next: 0 for this label belongs to this bb, 1 for this label belongs to the next bb
      let mut mark_label = |label: u32, is_next: u32| {
        let label = label as usize;
        if label2bb.len() <= label { label2bb.resize(label + 1, 0); }
        label2bb[label] = bb.len() as u32 + is_next;
      };
      let mut first = Some(first);
      while let Some(t) = first {
        if let Tac::Label { label } = t.tac.get() {
          mark_label(label, 0);
          first = t.next.get();
        } else { break; }
      }
      let (mut cur, mut first, mut last) = (first, None, None);
      let mut len = 0; // ret/jmp/jif/label are not counted
      // mark `has_label` as true if `next` contains `Some(label)`
      // label index should be remapped to bb index that the label belongs to
      let mut has_label = false;
      let next = loop {
        if let Some(cur1) = cur {
          match cur1.tac.get() {
            Tac::Label { label } => {
              mark_label(label, 1);
              break NextKind::Jmp(bb.len() as u32 + 1);
            }
            Tac::Jmp { label } => {
              has_label = true;
              break NextKind::Jmp(label);
            }
            Tac::Jif { label, z, cond } => break match cond[0] {
              Operand::Const(c) => if (c == 0) == z { // (Jz, and is z) or (Jnz and is not z), do the jump
                has_label = true;
                NextKind::Jmp(label)
              } else { NextKind::Jmp(bb.len() as u32 + 1) }
              Operand::Reg(r) => {
                has_label = true;
                NextKind::Jif { cond: r, z, fail: bb.len() as u32 + 1, jump: label }
              }
            },
            Tac::Ret { src } => break NextKind::Ret(src.map(|src| src[0])),
            Tac::Call { kind: CallKind::Intrinsic(_Halt), .. } => break NextKind::Halt,
            _ => {
              if first.is_none() { first = cur; }
              last = cur;
              len += 1;
            }
          }
          cur = cur1.next.get();
        } else {
          // reaching here means the last tac is not `return`, but we still don't add `return` here, instead we add `jmp`
          // in this way, if the last bb is reachable, it will be certain to cause panicking in `simplify`
          break NextKind::Jmp(bb.len() as u32 + 1);
        }
      };
      iter = cur.and_then(|cur| cur.next.get());
      if has_label { labels.push(bb.len() as u32); }
      if let Some(first) = first { first.prev.set(None); }
      if let Some(last) = last { last.next.set(None); }
      bb.push(BB { len, first, last, next, prev: vec![] });
    }
    for unfill in labels {
      match &mut bb[unfill as usize].next {
        NextKind::Jmp(jump) | NextKind::Jif { jump, .. } => *jump = label2bb[*jump as usize], _ => {}
      }
    }
    FuncBB { param_num: f.param_num, reg_num: f.reg_num, alloc: f.alloc, bb: simplify(bb), name: f.name.clone() }
  }

  pub fn optimize(&mut self) {
    crate::common_expr::work(self);
    crate::copy_prop::work(self);
    crate::const_prop::work(self);
    crate::aliveness::work(self);
  }

  pub fn optimizen(&mut self, n: u32) {
    for _ in 0..n { self.optimize(); }
  }

  pub fn new_reg(&mut self) -> u32 {
    (self.reg_num, self.reg_num += 1).0
  }

  // convert self back into a `TacFunc`, which can be used for execution
  pub fn to_tac_func(&self) -> TacFunc<'a> {
    let mut f = TacFunc::empty(self.alloc, self.name.clone(), self.param_num);
    f.reg_num = self.reg_num;
    for (idx, b) in self.bb.iter().enumerate() {
      // generate label and jump only when necessary
      if !(b.prev.is_empty() || (b.prev.len() == 1 && b.prev[0] + 1 == idx as u32)) {
        f.push(Tac::Label { label: idx as u32 });
      }
      // shouldn't have ret/... here
      for t in b.iter() { f.push(t.tac.get()); }
      match b.next {
        NextKind::Ret(src) => { f.push(Tac::Ret { src: src.map(|src| [src]) }); }
        NextKind::Jmp(jump) => if jump != idx as u32 + 1 { f.push(Tac::Jmp { label: jump }); }
        NextKind::Jif { cond, z, jump, .. } => { f.push(Tac::Jif { label: jump, z, cond: [Operand::Reg(cond)] }); }
        NextKind::Halt => { f.push(Tac::Call { dst: None, kind: CallKind::Intrinsic(_Halt) }); }
      };
    }
    f
  }
}

// `simplify` will remove all unreachable nodes, and set each node's `prev` to the proper value
// the old value of each node's `prev` is not used here
// it is possible to trigger `index out of bounds` here (if constraint is violated), see the comment in `FuncBB::new`
pub(crate) fn simplify(mut bb: Vec<BB>) -> Vec<BB> {
  fn dfs(x: usize, bb: &mut [BB], vis: &mut [bool]) {
    if vis[x] { return; }
    vis[x] = true;
    bb[x].next().iter().filter_map(|&x| x).for_each(|x| dfs(x as usize, bb, vis));
  }
  let mut vis = vec![false; bb.len()];
  dfs(0, &mut bb, &mut vis);
  let mut actual = vec![0; bb.len()]; // exclusive prefix sum of `vis`
  for i in 1..bb.len() {
    actual[i] += actual[i - 1] + vis[i - 1] as u32;
  }
  let mut new = Vec::with_capacity(bb.len());
  for (_, mut b) in bb.into_iter().enumerate().filter(|(idx, _)| vis[*idx]) {
    b.next = match b.next {
      NextKind::Jmp(jump) => NextKind::Jmp(actual[jump as usize]),
      NextKind::Jif { cond, z, fail, jump } =>
        NextKind::Jif { cond, z, fail: actual[fail as usize], jump: actual[jump as usize] },
      n => n
    };
    b.prev.clear();
    new.push(b);
  }
  for idx in 0..new.len() { // borrow checker...
    new[idx].next().iter().filter_map(|&x| x).for_each(|x| new[x as usize].prev.push(idx as u32));
  }
  new
}
