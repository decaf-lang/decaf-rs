use crate::bb::{FuncBB, NextKind, checked_simplify};
use tac::{TacKind, Operand};

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Value { Unk, Const(i32), Nac }

fn meet(x: Value, y: Value) -> Value {
  match (x, y) {
    (Value::Const(x), Value::Const(y)) if x == y => Value::Const(x),
    (v, Value::Unk) | (Value::Unk, v) => v,
    _ => Value::Nac,
  }
}

fn transfer(kind: TacKind, env: &mut [Value]) {
  use TacKind::*;
  use Operand::*;
  use Value::{Const as C, Nac, Unk};
  match kind {
    Bin { op, dst, lr } => {
      let lr = match lr {
        [Const(l), Const(r)] => (C(l), C(r)),
        [Reg(l), Const(r)] => (env[l as usize], C(r)),
        [Const(l), Reg(r)] => (C(l), env[r as usize]),
        [Reg(l), Reg(r)] => (env[l as usize], env[r as usize]),
      };
      env[dst as usize] = match lr {
        (C(l), C(r)) => C(op.eval(l, r)),
        (Nac, _) | (_, Nac) => Nac,
        _ => Unk, // neither is Nac and not both Const => Unk
      };
    }
    Un { op, dst, r } => env[dst as usize] = match r[0] {
      Const(r) => C(op.eval(r)),
      Reg(r) => match env[r as usize] { C(r) => C(op.eval(r)), r => r },
    },
    Assign { dst, src } => env[dst as usize] = match src[0] { Const(r) => C(r), Reg(r) => env[r as usize] },
    Call { dst, .. } => if let Some(dst) = dst { env[dst as usize] = Nac }
    LoadInt { dst, i } => env[dst as usize] = C(i),
    Load { dst, .. } => env[dst as usize] = Nac,
    // actually LoadStr and LoadVTbl won't give `dst` a Unk
    // but as long as the implementation is correct, `dst` can never be used in calculation, so giving them Unk is okay
    LoadStr { dst, .. } | LoadVTbl { dst, .. } => env[dst as usize] = Unk,
    Param { .. } | Ret { .. } | Jmp { .. } | Label { .. } | Jif { .. } | Store { .. } => {}
  }
}

pub fn work(f: &mut FuncBB) {
  let (n, each) = (f.bb.len(), f.max_reg as usize);
  let mut flow = vec![Value::Unk; n * each];
  for i in 0..f.param_num as usize {
    flow[i] = Value::Nac; // flow[i] is in the entry bb, and setting them is enough
  }
  let mut tmp = flow.clone(); // tmp is used to detect whether `flow` has changed
  loop {
    for (idx, b) in f.bb.iter().enumerate() {
      for next in b.next().iter().filter_map(|n| n.map(|n| n as usize)) {
        let (off, off1) = (idx * each, next * each);
        for i in 0..each {
          flow[off1 + i] = meet(flow[off1 + i], flow[off + i]);
        }
      }
    }
    for (idx, b) in f.bb.iter().enumerate() {
      let env = &mut flow[idx * each..(idx + 1) * each];
      for t in b.iter() { transfer(t.payload.borrow().kind, env); }
    }
    if flow != tmp { tmp.clone_from_slice(&flow); } else { break; }
  }
  let mut flow_changed = false; // whether the edges in flow graph have changed
  for (idx, b) in f.bb.iter_mut().enumerate() {
    let env = &mut flow[idx * each..(idx + 1) * each];
    for t in b.iter() {
      let mut payload = t.payload.borrow_mut();
      for r in payload.kind.rw_mut().0 {
        if let Operand::Reg(r1) = *r {
          if let Value::Const(r1) = env[r1 as usize] { *r = Operand::Const(r1); }
        }
      }
      transfer(payload.kind, env);
    }
    match &mut b.next {
      NextKind::Ret(Some(r)) => if let Operand::Reg(r1) = *r {
        if let Value::Const(r1) = env[r1 as usize] { *r = Operand::Const(r1); }
      }
      &mut NextKind::Jif { cond, z, fail, jump } => if let Value::Const(c) = env[cond as usize] {
        b.next = if (c == 0) == z { NextKind::Jmp(jump) } else { NextKind::Jmp(fail) };
        flow_changed = true;
      }
      _ => {}
    }
  }
  if flow_changed {
    f.bb = checked_simplify(std::mem::replace(&mut f.bb, Vec::new()), None).unwrap();
  }
}