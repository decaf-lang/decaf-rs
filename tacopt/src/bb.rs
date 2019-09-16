use tac::{Tac, TacKind, TacFunc, Operand, FuncNameKind, TacIter, CallKind, Intrinsic::_Halt};
use common::Ref;
use typed_arena::Arena;

pub struct BB<'a> {
  pub len: u32,
  // the ret/jmp/jif/label is NOT contained in the link list defined by first -> last
  // don't forget ret/jif may contain a register in data flow analysis
  pub first: Option<&'a Tac<'a>>,
  pub last: Option<&'a Tac<'a>>,
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
  pub fn next(&self) -> [Option<u32>; 2] {
    match self.next {
      NextKind::Ret(_) | NextKind::Halt => [None, None],
      NextKind::Jmp(jump) => [Some(jump), None],
      NextKind::Jif { fail, jump, .. } => [Some(fail), Some(jump)],
    }
  }

  // return the register it reads(if any)
  pub fn next_r(&self) -> Option<u32> {
    match self.next {
      NextKind::Ret(r) => match r { Some(Operand::Reg(r)) => Some(r), _ => None }
      NextKind::Jif { cond, .. } => Some(cond),
      _ => None
    }
  }

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

  // the link on t is not cut down, so you can safely del a tac while iterating over it
  pub fn del(&mut self, t: &'a Tac<'a>) {
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

  pub fn insert_after(&mut self, loc: &'a Tac<'a>, new: &'a Tac<'a>) {
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
  // while adding an virtual entry node, which has an edge to the first reachable node
  // `this` is self's index + 1, noting that the first reachable node's index must be 0
  pub fn prev_with_entry<'b>(&'b self, this: usize) -> (usize, impl IntoIterator<Item=usize> + Clone + 'b) {
    (this, self.prev.iter().map(|x| *x as usize + 1).chain(if this == 1 { Some(0) } else { None }))
  }
}

pub struct FuncBB<'a> {
  // some fields copied from TacFunc, but they may change during optimization, so I decide not to borrow TacFunc
  pub param_num: u32,
  // max_reg and max_tac are actually the max id of reg/tac + 1, so if you need to allocate array for them, no need to + 1
  // during optimization, if they decrease, don't need to update FuncBB, but if they increase, do remember to update
  pub max_reg: u32,
  pub max_tac: u32,
  pub has_ret: bool,
  pub alloc: &'a Arena<Tac<'a>>,
  pub bb: Vec<BB<'a>>,
  pub name: FuncNameKind<'a>,
}

impl<'a> FuncBB<'a> {
  // will add a new inst(ret) to f, but will not inc f.tac_len; it is okay because future work is based on bb but not f, f.tac_len is no longer used
  // return None if f's return type is not void and control flow can reaches end of function
  pub fn new<'b>(f: &'b TacFunc<'a>) -> Option<FuncBB<'a>> {
    let mut bb = Vec::new();
    let mut label2bb = Vec::new();
    let mut label_to_map = Vec::new();
    let mut iter = f.first_last.map(|(f, _)| f);
    while let Some(first) = iter {
      let mut mark_label = |label: u32, is_next: u32| {
        let label = label as usize;
        if label2bb.len() <= label {
          label2bb.resize(label + 1, 0);
        }
        label2bb[label] = bb.len() as u32 + is_next;
      };
      let mut first = Some(first);
      while let Some(t) = first {
        if let TacKind::Label { label } = t.payload.borrow().kind {
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
        match cur {
          None => break NextKind::Ret(None),
          Some(cur1) => {
            match cur1.payload.borrow().kind {
              TacKind::Label { label } => {
                mark_label(label, 1);
                break NextKind::Jmp(bb.len() as u32 + 1);
              }
              TacKind::Jmp { label } => {
                has_label = true;
                break NextKind::Jmp(label);
              }
              TacKind::Jif { label, z, cond } => break match cond[0] {
                Operand::Const(c) => if (c == 0) == z { // (Jz, and is z) or (Jnz and is not z), do the jump
                  has_label = true;
                  NextKind::Jmp(label)
                } else { NextKind::Jmp(bb.len() as u32 + 1) }
                Operand::Reg(r) => {
                  has_label = true;
                  NextKind::Jif { cond: r, z, fail: bb.len() as u32 + 1, jump: label }
                }
              },
              TacKind::Ret { src } => break NextKind::Ret(src.map(|src| src[0])),
              TacKind::Call { kind: CallKind::Intrinsic(_Halt), .. } => break NextKind::Halt,
              _ => {
                if first.is_none() { first = cur; }
                last = cur;
                len += 1;
              }
            }
            cur = cur1.next.get();
          }
        }
      };
      iter = cur.and_then(|cur| cur.next.get());
      if has_label { label_to_map.push(bb.len() as u32); }
      if let Some(first) = first { first.prev.set(None); }
      if let Some(last) = last { last.next.set(None); }
      bb.push(BB { len, first, last, next, prev: vec![] });
    }
    bb.push(BB { len: 0, first: None, last: None, next: NextKind::Ret(None), prev: vec![] });
    for unfill in label_to_map {
      match &mut bb[unfill as usize].next {
        NextKind::Jmp(jump) | NextKind::Jif { jump, .. } => *jump = label2bb[*jump as usize], _ => {}
      }
    }
    checked_simplify(bb, Some(f)).map(|bb| {
      let (max_reg, max_tac) = (f.max_reg, f.tac_len);
      FuncBB { param_num: f.param_num, max_reg, max_tac, has_ret: f.has_ret, alloc: f.alloc, bb, name: f.name }
    })
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
    (self.max_reg, self.max_reg += 1).0
  }

  pub fn new_tac(&mut self) -> u32 {
    (self.max_tac, self.max_tac += 1).0
  }

  pub fn to_tac_func(&self) -> TacFunc<'a> {
    let mut f = TacFunc::empty(self.alloc, self.name, self.param_num, self.has_ret);
    f.max_reg = self.max_reg;
    for (idx, b) in self.bb.iter().enumerate() {
      // generate label and jump only when necessary
      if !(b.prev.is_empty() || (b.prev.len() == 1 && b.prev[0] + 1 == idx as u32)) {
        f.push(TacKind::Label { label: idx as u32 });
      }
      for t in b.iter() {
        f.push(t.payload.borrow().kind); // shouldn't have ret/... here
      }
      match b.next {
        NextKind::Ret(src) => { f.push(TacKind::Ret { src: src.map(|src| [src]) }); }
        NextKind::Jmp(jump) => if jump != idx as u32 + 1 { f.push(TacKind::Jmp { label: jump }); }
        NextKind::Jif { cond, z, jump, .. } => { f.push(TacKind::Jif { label: jump, z, cond: [Operand::Reg(cond)] }); }
        NextKind::Halt => { f.push(TacKind::Call { dst: None, kind: CallKind::Intrinsic(_Halt) }); }
      };
    }
    f
  }
}

// remove unreachable bb(next and prev is properly rewritten)
// return None for error, i.e, if this function returns without returning a value and f.has_ret == true
// if f is None, no check is performed, must return Some
pub(crate) fn checked_simplify<'a>(mut bb: Vec<BB<'a>>, f: Option<&TacFunc>) -> Option<Vec<BB<'a>>> {
  fn dfs(x: usize, bb: &mut [BB], vis: &mut [bool]) {
    if vis[x] { return; }
    vis[x] = true;
    bb[x].next().iter().filter_map(|&x| x).for_each(|x| dfs(x as usize, bb, vis));
  }

  let mut vis = vec![false; bb.len()];
  dfs(0, &mut bb, &mut vis);
  if f.map(|f| f.has_ret).unwrap_or(false) {
    for (idx, b) in bb.iter().enumerate() {
      if vis[idx] && match b.next { NextKind::Ret(None) => true, _ => false, } {
        return None;
      }
    }
  }

  let mut actual = vec![0; bb.len()];
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
    b.prev.clear(); // prev is filled afterwards, it's old value is not used in this function
    new.push(b);
  }

  for idx in 0..new.len() { // borrow checker...
    new[idx].next().iter().filter_map(|&x| x).for_each(|x| new[x as usize].prev.push(idx as u32));
  }

  Some(new)
}