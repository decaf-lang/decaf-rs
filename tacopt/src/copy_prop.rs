use crate::{bb::{FuncBB, BB}, flow::{FlowElem, Flow, And}};
use common::{HashSet, HashMap, IndexSet};
use tac::{Tac, Operand};
use bitset::traits::*;

pub fn work(f: &mut FuncBB) {
  let mut reg2copy = HashMap::new(); // x = y -> add the index of (x, y) in copy2id to reg2copy[x], reg2copy[y]
  let mut copy2id = IndexSet::default();
  for b in &mut f.bb {
    for t in b.iter() {
      if let Tac::Assign { dst, src } = t.tac.get() {
        if let Operand::Reg(src) = src[0] {
          if dst == src { // just delete it, doesn't even need propagation
            b.del(t);
          } else {
            let id = copy2id.insert_full((dst, src)).0 as u32;
            reg2copy.entry(dst).or_insert_with(HashSet::new).insert(id);
            reg2copy.entry(src).or_insert_with(HashSet::new).insert(id);
          }
        }
      }
    }
  }
  let reg2copy = reg2copy.iter().map(|(k, v)| (*k, iter2bs(v, copy2id.len()))).collect();
  // + 1 to let 0 be the virtual entry node, with `out` = empty
  let mut copy_prop_flow = Flow::<And>::new(f.bb.len() + 1, copy2id.len());
  let each = copy_prop_flow.each();
  let FlowElem { gen, kill, out, .. } = copy_prop_flow.split();
  for (off, b) in f.bb.iter().enumerate().map(|b| ((b.0 + 1) * each, b.1)) {
    compute_gen_kill(b, &mut gen[off..off + each], &mut kill[off..off + each], &reg2copy, &copy2id);
  }
  for x in out.iter_mut().skip(each) { *x = !0; } // initial value of out is U, except for entry node
  copy_prop_flow.solve(f.bb.iter().enumerate().map(|b| b.1.prev_with_entry(b.0 + 1)));
  let FlowElem { in_, .. } = copy_prop_flow.split();
  for (off, b) in f.bb.iter_mut().enumerate().map(|b| ((b.0 + 1) * each, b.1)) {
    do_optimize(b, &mut in_[off..off + each], &reg2copy, &copy2id);
  }
}

fn compute_gen_kill(b: &BB, gen: &mut [u32], kill: &mut [u32], reg2copy: &HashMap<u32, Box<[u32]>>, copy2id: &IndexSet<(u32, u32)>) {
  for t in b.iter() {
    let tac = t.tac.get();
    tac.rw().1.map(|w| reg2copy.get(&w).map(|copy| {
      kill.bsor(copy);
      gen.bsandn(copy);
    }));
    if let Tac::Assign { dst, src } = tac {
      if let Operand::Reg(src) = src[0] {
        gen.bsset(copy2id.get_full(&(dst, src)).unwrap().0);
      }
    }
  }
}

fn do_optimize(b: &mut BB, in_: &mut [u32], reg2copy: &HashMap<u32, Box<[u32]>>, copy2id: &IndexSet<(u32, u32)>) {
  fn lookup(reg: u32, in_: &[u32], copy2id: &IndexSet<(u32, u32)>) -> u32 {
    for (id, &(dst, src)) in copy2id.iter().enumerate() {
      if in_.bsget(id) && reg == dst { // propagate, allow cascading multi-level copy in one pass of optimization
        return lookup(src, in_, copy2id);
      }
    }
    reg // failed to find any further copy, just return reg
  }
  for t in b.iter() {
    let mut tac = t.tac.get();
    // modify the operand to do copy propagation
    tac.rw_mut().0.iter_mut().for_each(|r| if let Operand::Reg(reg) = r { *reg = lookup(*reg, in_, copy2id) });
    // compute in_ for the next tac
    tac.rw().1.map(|w| reg2copy.get(&w).map(|copy| in_.bsandn(copy)));
    if let Tac::Assign { dst, src: [Operand::Reg(src)] } = t.tac.get() { // old value
      in_.bsset(copy2id.get_full(&(dst, src)).unwrap().0)
    }
    t.tac.set(tac);
  }
  if let Some(r) = b.next_r_mut() { *r = lookup(*r, in_, copy2id); }
}