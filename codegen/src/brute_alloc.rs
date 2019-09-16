use crate::{mips_gen::FuncGen, mips::{regs::*, AsmTemplate::*}, Reg};

// the easiest way to do register allocation: no allocation at all
// all virtual registers are stored in stack, when actual registers are needed, they are loaded into at most 3 temporary registers
// note that calling convention is still followed, thanks to the design of PreColored register

impl FuncGen<'_, '_> {
  pub fn brute_alloc(&mut self) {
    const READ: [Regs; 3] = [T0, T1, T2]; // only allocate these 3 registers
    for idx in 0..self.bb.len() {
      let old = std::mem::replace(&mut self.bb[idx].0, Vec::new());
      let mut new = Vec::with_capacity(old.len() * 2);
      for mut t in old {
        let (mut r, w) = t.rw_mut();
        for (idx, r) in r.iter_mut().enumerate() {
          if let Some(r) = r {
            if let Reg::Virtual(r1) = r {
              let slot = self.find_spill_slot(*r1);
              **r = Reg::Allocated(READ[idx] as u32);
              new.push(Lw(**r, Reg::PreColored(SP as u32), slot));
            }
          }
        }
        let wb = if let Some(w) = w {
          if let Reg::Virtual(w1) = w {
            let slot = self.find_spill_slot(*w1);
            *w = Reg::Allocated(READ[2] as u32);
            Some(Sw(*w, Reg::PreColored(SP as u32), slot))
          } else { None }
        } else { None };
        new.push(t);
        if let Some(wb) = wb { new.push(wb); } // write back goes after this instruction
      }
      self.bb[idx].0 = new;
    }
  }
}