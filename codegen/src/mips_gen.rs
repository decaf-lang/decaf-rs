use crate::{graph_alloc::*, mips::{*, regs::*}, Reg, AllocMethod};
use tacopt::{bb::{FuncBB, NextKind}, flow::{Flow, Or, FlowElem}};
use tac::{Tac, TacProgram, Operand, CallKind, Intrinsic};
use common::{HashSet, HashMap, BinOp};
use bitset::traits::*;

pub struct FuncGen<'a, 'b> {
  pub(crate) param_num: u32,
  pub(crate) reg_num: u32,
  // for functions that this function calls, not the parameter of this function (which is `param_num`)
  pub(crate) ch_param_num: u32,
  pub(crate) name: &'b str,
  pub(crate) program: &'b TacProgram<'a>,
  // we do need to insert in the SomeContainer<AsmTemplate>, but rust's LinkedList's api is so limited
  // and we do not need arbitrary insertion/deletion, so a Vec will be enough
  pub(crate) bb: Vec<(Vec<AsmTemplate>, [Option<u32>; 2])>,
  // map virtual reg's id to its offset from $sp
  pub(crate) spill2slot: HashMap<u32, i32>,
}

// all virtual register's id >= REG_N, all pre-colored or allocated register's id < REG_N, id can be the index in Allocator::nodes
// m for machine, v for virtual
fn mreg(r: Regs) -> Reg { Reg::PreColored(r as u32) }

fn vreg(r: u32) -> Reg { Reg::Virtual(r + REG_N) }

impl AllocCtx for FuncGen<'_, '_> {
  const K: u32 = ALLOC_N;

  fn initial(&self) -> (Vec<u32>, Vec<Node>) {
    // there are only ALLOC_N registers to allocate, but there are REG_N pre-colored nodes
    // (by definition, a machine register <=> a pre-colored node)
    ((REG_N..self.reg_num + REG_N).collect(), (0..self.reg_num + REG_N).map(|r| if r < REG_N {
      Node::new(Reg::PreColored(r))
    } else {
      Node::new(Reg::Virtual(r))
    }).collect())
  }

  fn build(&self, allocator: &mut Allocator<Self>) {
    let mut aliveness_flow = self.analyze();
    let each = aliveness_flow.each();
    let FlowElem { in_: out, .. } = aliveness_flow.split();
    let (mut r, mut w) = (Vec::new(), Vec::new());
    for (off, b) in self.bb.iter().enumerate().map(|b| (b.0 * each, &(b.1).0)) {
      let live = &mut out[off..off + each];
      for t in b.iter().rev() {
        if let &AsmTemplate::Mv(w1, r1) = t {
          let (w1, r1) = (w1.id(), r1.id());
          if Self::involved_in_alloc(w1) && Self::involved_in_alloc(r1) {
            live.bsdel(r1);
            allocator.nodes[w1 as usize].move_list.push((w1, r1));
            allocator.nodes[r1 as usize].move_list.push((w1, r1));
            allocator.work_list_moves.insert((w1, r1));
          }
        }
        t.rw(&mut r, &mut w);
        for w in w.iter().copied().map(Reg::id) {
          for l in live.bsones() {
            if Self::involved_in_alloc(w) && Self::involved_in_alloc(l) {
              allocator.add_edge(w, l);
            }
          }
        }
        w.iter().copied().map(Reg::id).for_each(|w| live.bsdel(w));
        r.iter().copied().map(Reg::id).for_each(|r| live.bsset(r));
      }
    }
  }

  fn rewrite(&mut self, spilled_nodes: &HashSet<u32>) {
    for idx in 0..self.bb.len() {
      let old = std::mem::replace(&mut self.bb[idx].0, Vec::new());
      let mut new = Vec::with_capacity(old.len() * 2);
      for t in old {
        match t {
          // if this inst is move, rewriting it can be simplified if at least one of the operands is not spilled
          AsmTemplate::Mv(w1, r1) => {
            let (w1, r1) = (w1.id(), r1.id());
            match (spilled_nodes.contains(&w1), spilled_nodes.contains(&r1)) {
              (true, true) => self.do_rewrite(t, spilled_nodes, &mut new),
              (false, true) => {
                let slot = self.find_spill_slot(r1);
                new.push(AsmTemplate::Lw(Reg::Virtual(w1), mreg(SP), slot));
              }
              (true, false) => {
                let slot = self.find_spill_slot(w1);
                new.push(AsmTemplate::Sw(Reg::Virtual(r1), mreg(SP), slot));
              }
              (false, false) => new.push(t),
            }
          }
          t => self.do_rewrite(t, spilled_nodes, &mut new),
        }
      }
      self.bb[idx].0 = new;
    }
  }

  fn finish(&mut self, result: &[Node]) {
    for (b, _) in &mut self.bb {
      for t in b {
        let (mut r, w) = t.rw_mut();
        for r in r.iter_mut() {
          if let Some(r) = r {
            if let Reg::Virtual(r1) = **r {
              **r = Reg::Allocated(result[r1 as usize].expect_colored());
            }
          }
        }
        if let Some(w) = w {
          if let Reg::Virtual(w1) = *w {
            *w = Reg::Allocated(result[w1 as usize].expect_colored());
          }
        }
      }
    }
  }
}

impl<'a: 'b, 'b> FuncGen<'a, 'b> {
  pub fn work(f: &'b FuncBB<'a>, p: &'b TacProgram<'a>, m: AllocMethod) -> Vec<AsmTemplate> {
    // reg_num is not inced by K, and new_reg() doesn't either, so all usage of virtual register id need to inc K
    // including those using f's inst and those generated to meet calling convention
    let mut fu = FuncGen { param_num: f.param_num, reg_num: f.reg_num, ch_param_num: 0, name: &f.name, program: p, bb: Vec::new(), spill2slot: HashMap::new() };
    fu.populate(f);
    match m { AllocMethod::Graph => Allocator::work(&mut fu), AllocMethod::Brute => fu.brute_alloc() }
    fu.fill_imm_tag();
    fu.bb.into_iter()
      .flat_map(|(b, _)| b.into_iter())
      .filter(|asm| !asm.useless())
      .collect()
  }

  // for all virtual registers in f, inc it by REG_N before adding to self
  fn populate(&mut self, f: &FuncBB<'a>) {
    let (pro, epi) = self.build_prologue_epilogue();
    self.bb = vec![(pro, [Some(1), None])];
    for (idx, b1) in f.bb.iter().enumerate() {
      let mut b2 = Vec::new();
      if !(b1.prev.is_empty() || (b1.prev.len() == 1 && b1.prev[0] + 1 == idx as u32)) {
        b2.push(AsmTemplate::Label(format!("{}_L{}:", self.name, idx + 1)));
      }
      let mut arg_num = 0;
      for t in b1.iter() {
        self.select_inst(t.tac.get(), &mut b2, &mut arg_num);
      }
      // generate ret/jmp/..., and return the `next` by the way
      let next = self.build_next(idx as u32, f.bb.len() as u32 + 1, b1.next, &mut b2);
      self.bb.push((b2, next));
    }
    self.bb.push((epi, [None, None]));
  }

  // prologue:
  //   1. adjust $sp to leave enough space for spilling
  //   2. move function arguments to virtual registers representing function arguments
  //   3. save all callee-saved registers ($sp is not included)
  // epilogue:
  //   1. restore all callee-saved registers ($sp is not included)
  //   2. adjust $sp back
  //   3. do return (jr $ra)
  fn build_prologue_epilogue(&mut self) -> (Vec<AsmTemplate>, Vec<AsmTemplate>) {
    use AsmTemplate::*;
    let (mut pro, mut epi) = (Vec::new(), Vec::new());
    pro.push(BinI(BinOp::Sub, mreg(SP), mreg(SP), Imm::Tag(0)));
    // f use %i for the ith argument
    for i in 0..self.param_num {
      match ARG.nth(i as usize) {
        Some(a) => pro.push(AsmTemplate::Mv(vreg(i), Reg::PreColored(a))),
        None => pro.push(AsmTemplate::Lw(vreg(i), mreg(SP), Imm::Tag(i))),
      }
    }
    // Tac::Ret should mv return value(if any) to v0 and jmp here
    epi.push(Label(format!("{}_Ret:", self.name)));
    for ces in CALLEE_SAVE {
      let tmp = self.new_reg();
      pro.push(Mv(vreg(tmp), Reg::PreColored(ces)));
      epi.push(Mv(Reg::PreColored(ces), vreg(tmp)));
    }
    epi.push(BinI(BinOp::Add, mreg(SP), mreg(SP), Imm::Tag(0)));
    epi.push(Ret);
    (pro, epi)
  }
}

impl<'a: 'b, 'b> FuncGen<'a, 'b> {
  // 0..Self::K : physical allocable registers
  // Self::K..REG_N : physical unallocable registers, though they are unallocable, they may still be used in some insts
  // REG_N : virtual registers
  fn involved_in_alloc(r: u32) -> bool {
    r < Self::K /* an allocatable machine register */ || r >= REG_N /* an virtual register */
  }

  fn new_reg(&mut self) -> u32 { (self.reg_num, self.reg_num += 1).0 }

  // find a unique slot on the stack for `vreg` to spill
  // assume `vreg` >= REG_N, i.e., it is a legal virtual register id
  pub(crate) fn find_spill_slot(&mut self, vreg: u32) -> Imm {
    let vreg = vreg - REG_N;
    if vreg < self.param_num { // function arguments already have places to spill
      Imm::Tag(vreg)
    } else {
      let new_slot = (self.spill2slot.len() as i32 + self.ch_param_num as i32) * WORD_SIZE;
      Imm::Int(*self.spill2slot.entry(vreg).or_insert(new_slot))
    }
  }

  fn fill_imm_tag(&mut self) {
    let self_stack = (self.spill2slot.len() as i32 + self.ch_param_num as i32) * WORD_SIZE;
    for (b, _) in &mut self.bb {
      for t in b {
        if let Some(imm) = t.imm_mut() {
          if let Imm::Tag(t) = *imm {
            // there are 3 places uses Imm::Tag, all can use the same way to compute
            // 1. $sp -= _ in prologue, tag = 0
            // 2. $sp += _ in epilogue, tag = 0
            // 3. the offset of arguments of this function on stack, where tag = t for t_th(0 based index) argument
            *imm = Imm::Int(self_stack + t as i32 * WORD_SIZE);
          }
        }
      }
    }
  }

  // do register spilling
  // add memory read before inst, add memory write after inst, if necessary
  fn do_rewrite(&mut self, mut t: AsmTemplate, spilled_nodes: &HashSet<u32>, new: &mut Vec<AsmTemplate>) {
    let (mut r, w) = t.rw_mut();
    for r in r.iter_mut() {
      if let Some(Reg::Virtual(r)) = r {
        if spilled_nodes.contains(r) {
          let slot = self.find_spill_slot(*r);
          *r = self.new_reg() + REG_N;
          new.push(AsmTemplate::Lw(Reg::Virtual(*r), mreg(SP), slot));
        }
      }
    }
    match w {
      Some(Reg::Virtual(w)) if spilled_nodes.contains(w) => {
        let slot = self.find_spill_slot(*w);
        *w = self.new_reg() + REG_N;
        let w = *w;
        new.push(t);
        new.push(AsmTemplate::Sw(Reg::Virtual(w), mreg(SP), slot));
      }
      _ => new.push(t),
    }
  }
}

impl FuncGen<'_, '_> {
  fn analyze(&self) -> Flow<Or> {
    let mut aliveness_flow = Flow::<Or>::new(self.bb.len(), (self.reg_num + REG_N) as usize);
    let each = aliveness_flow.each();
    let FlowElem { gen: use_, kill: def, .. } = aliveness_flow.split();
    for (idx, b) in self.bb.iter().enumerate() {
      let off = idx * each;
      Self::compute_use_def(&b.0, &mut use_[off..off + each], &mut def[off..off + each]);
    }
    aliveness_flow.solve(self.bb.iter().enumerate().map(|b| (b.0, (b.1).1.iter().filter(|n| n.is_some()).map(|n| n.unwrap() as usize))));
    aliveness_flow
  }

  fn compute_use_def(b: &[AsmTemplate], use_: &mut [u32], def: &mut [u32]) {
    let (mut r, mut w) = (Vec::new(), Vec::new());
    for t in b.iter().rev() {
      t.rw(&mut r, &mut w);
      w.iter().copied().map(Reg::id).for_each(|w| {
        def.bsset(w);
        use_.bsdel(w);
      });
      r.iter().copied().map(Reg::id).for_each(|r| {
        use_.bsset(r);
        def.bsdel(r);
      });
    }
  }
}

impl FuncGen<'_, '_> {
  fn select_inst(&mut self, t: Tac, b: &mut Vec<AsmTemplate>, arg_num: &mut u32) {
    use AsmTemplate::*;
    match t {
      Tac::Bin { op, dst, lr } => {
        match lr {
          [Operand::Const(l), Operand::Const(r)] => b.push(Li(vreg(dst), Imm::Int(op.eval(l, r)))),
          [Operand::Reg(l), Operand::Const(r)] => b.push(BinI(op, vreg(dst), vreg(l), Imm::Int(r))),
          [Operand::Const(l), Operand::Reg(r)] => if let Some(inv) = op.invert() {
            b.push(BinI(inv, vreg(dst), vreg(r), Imm::Int(l)))
          } else {
            let tmp = self.build_operand(Operand::Const(l), b);
            b.push(Bin(op, vreg(dst), tmp, vreg(r)));
          }
          [Operand::Reg(l), Operand::Reg(r)] => b.push(Bin(op, vreg(dst), vreg(l), vreg(r)))
        }
      }
      Tac::Un { op, dst, r } => match r[0] {
        Operand::Const(r) => b.push(Li(vreg(dst), Imm::Int(op.eval(r)))),
        Operand::Reg(r) => b.push(Un(op, vreg(dst), vreg(r))),
      }
      Tac::Assign { dst, src } => self.build_mv(vreg(dst), src[0], b),
      Tac::Param { src } => {
        let src = self.build_operand(src[0], b);
        match ARG.nth(*arg_num as usize) {
          Some(a) => b.push(Mv(Reg::PreColored(a), src)),
          None => b.push(Sw(src, mreg(SP), Imm::Int(*arg_num as i32 * WORD_SIZE))),
        }
        *arg_num += 1;
      }
      Tac::Call { dst, kind } => {
        let called = match kind {
          CallKind::Virtual(r, _) => {
            let r = self.build_operand(r[0], b);
            b.push(Jalr(r));
            true
          }
          CallKind::Static(f, _) => {
            b.push(Jal(self.program.func[f as usize].name.clone()));
            true
          }
          CallKind::Intrinsic(i) => self.build_intrinsic(i, b),
        };
        if called {
          // once it is really a function call, ch_param_num should grows from 4
          // because calling convention says the first 4 argument should have their slots on the stack
          self.ch_param_num = self.ch_param_num.max(*arg_num).max(4);
        }
        *arg_num = 0;
        if let Some(dst) = dst { b.push(Mv(vreg(dst), mreg(V0))); }
      }
      Tac::Load { dst, base, off, .. } => {
        let base = self.build_operand(base[0], b);
        b.push(Lw(vreg(dst), base, Imm::Int(off)));
      }
      Tac::Store { src_base, off, .. } => {
        let (src, base) = (self.build_operand(src_base[0], b), self.build_operand(src_base[1], b));
        b.push(Sw(src, base, Imm::Int(off)));
      }
      Tac::LoadStr { dst, s } => b.push(AsmTemplate::La(vreg(dst), format!("_STRING{}", s))),
      Tac::LoadVTbl { dst, v } => b.push(AsmTemplate::La(vreg(dst), format!("_{}", self.program.vtbl[v as usize].class))),
      Tac::LoadFunc { dst, f } => b.push(AsmTemplate::La(vreg(dst), self.program.func[f as usize].name.clone())),
      Tac::Label { .. } | Tac::Ret { .. } | Tac::Jmp { .. } | Tac::Jif { .. } => unreachable!("Shouldn't meet Ret/Jmp/Jif/Label in a tac bb."),
    }
  }

  // the returned reg can only be used for read
  fn build_operand(&mut self, src: Operand, b: &mut Vec<AsmTemplate>) -> Reg {
    match src {
      Operand::Reg(r) => vreg(r),
      Operand::Const(c) => if c == 0 { mreg(ZERO) } else {
        let new = vreg(self.new_reg());
        b.push(AsmTemplate::Li(new, Imm::Int(c)));
        new
      }
    }
  }

  fn build_mv(&self, dst: Reg, src: Operand, b: &mut Vec<AsmTemplate>) {
    match src {
      Operand::Reg(r) => b.push(AsmTemplate::Mv(dst, vreg(r))),
      Operand::Const(c) => b.push(AsmTemplate::Li(dst, Imm::Int(c))),
    }
  }

  // some intrinsic functions can be translated to syscall directly (of course it is not efficient, but it is easy to implement)
  // return true if a real function call is generated
  fn build_intrinsic(&self, i: Intrinsic, b: &mut Vec<AsmTemplate>) -> bool {
    use Intrinsic::*;
    match i {
      _Alloc => b.push(AsmTemplate::SysCall(SysCall::Sbrk)),
      _ReadInt => b.push(AsmTemplate::SysCall(SysCall::ReadInt)),
      _PrintInt => b.push(AsmTemplate::SysCall(SysCall::PrintInt)),
      _PrintString => b.push(AsmTemplate::SysCall(SysCall::PrintString)),
      _Halt => b.push(AsmTemplate::SysCall(SysCall::Exit)),
      _ReadLine | _StringEqual | _PrintBool => {
        b.push(AsmTemplate::Jal(format!("{:?}", i)));
        return true;
      }
    }
    false
  }

  // `epilogue` is the index of epilogue bb
  // note that all jump target should inc by 1, because prologue takes index 0
  fn build_next(&mut self, idx: u32, epilogue: u32, next: NextKind, b: &mut Vec<AsmTemplate>) -> [Option<u32>; 2] {
    match next {
      // turn ret into jmp to the last bb(epilogue)
      NextKind::Ret(src) => {
        if let Some(src) = src {
          self.build_mv(mreg(V0), src, b);
        }
        if idx + 2 != epilogue { // + 2, 1 for "prologue takes index 0", 1 for next bb should inc by 1 naturally
          b.push(AsmTemplate::J(format!("{}_Ret", self.name)));
        }
        [Some(epilogue), None]
      }
      NextKind::Jmp(jump) => {
        if idx + 1 != jump {
          b.push(AsmTemplate::J(format!("{}_L{}", self.name, jump + 1)));
        }
        [Some(jump + 1), None]
      }
      NextKind::Jif { cond, z, fail, jump } => {
        b.push(AsmTemplate::B(format!("{}_L{}", self.name, jump + 1), vreg(cond), z));
        // if we don't do any optimization on cfg, then `idx + 1 == fail` will always be true
        // because this is the situation when cfg is initially constructed
        if idx + 1 != fail {
          b.push(AsmTemplate::J(format!("{}_L{}", self.name, fail + 1)));
        }
        [Some(fail + 1), Some(jump + 1)]
      }
      NextKind::Halt => {
        self.build_intrinsic(Intrinsic::_Halt, b);
        [None, None]
      }
    }
  }
}