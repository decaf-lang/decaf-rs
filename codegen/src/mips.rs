use common::{BinOp, IgnoreResult, UnOp};
use std::fmt;
use crate::Reg;

pub mod regs {
  use std::ops::RangeInclusive;

  // some special registers:
  // $fp: we use it like other callee saved register
  // $ra: we use it like a mix of caller & callee saved register
  //   - a function may need to store/recover its value in prologue/epilogue(like callee saved)
  //   - it's value is not preserved during function call(like caller saved)
  // we choose to place it at CALLEE_SAVE, but mark it as `w` in function call inst
  // $zero, $at, $k0, $k1, $gp, $sp: we don't use them in register allocation

  // the order doesn't really matter, for convenience, the 26 registers for allocation are placed at 0..26
  #[derive(Copy, Clone, Eq, PartialEq)]
  pub enum Regs { V0, V1, A0, A1, A2, A3, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, S0, S1, S2, S3, S4, S5, S6, S7, FP, RA, /* <-allocable | unallocable-> */ ZERO, AT, K0, K1, GP, SP }

  pub use Regs::*;

  pub const REG_N: u32 = 32;
  pub const NAME: [&str; 32] = ["$v0", "$v1", "$a0", "$a1", "$a2", "$a3", "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9", "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7", "$fp", "$ra", "$zero", "$at", "$k0", "$k1", "$gp", "$sp", ];
  pub const ALLOC: RangeInclusive<u32> = V0 as u32..=RA as u32;
  pub const ALLOC_N: u32 = 26;
  pub const ARG: RangeInclusive<u32> = A0 as u32..=A3 as u32;
  pub const ARG_N: u32 = 4;
  pub const CALLER_SAVE: RangeInclusive<u32> = V0 as u32..=T9 as u32;
  pub const CALLEE_SAVE: RangeInclusive<u32> = S0 as u32..=RA as u32;
}

// only the syscalls that we used directly in codegen are listed here
// e.g.: ReadString is handled by a library function, so it not listed here
#[derive(Copy, Clone)]
pub enum SysCall { PrintInt = 1, PrintString = 4, ReadInt = 5, Sbrk = 9, Exit = 10 }

pub const WORD_SIZE: i32 = 4;

pub enum AsmTemplate {
  Bin(BinOp, Reg, Reg, Reg),
  BinI(BinOp, Reg, Reg, Imm),
  Un(UnOp, Reg, Reg),
  Mv(Reg, Reg),
  Jal(String),
  Jalr(Reg),
  J(String),
  // expanded to jr $ra, since we don't have any other usage of jr, I just use ret
  Ret,
  B(String, Reg, bool /* z */),
  Lw(Reg /* dst */, Reg /* base */, Imm),
  Sw(Reg /* src */, Reg /* base */, Imm),
  Li(Reg, Imm),
  La(Reg, String),
  Label(String),
  SysCall(SysCall),
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Imm {
  Int(i32),
  // `Tag` is used as a placeholder for undecided immediate value
  Tag(u32),
}

impl AsmTemplate {
  // clear `r` and `w`, put all registers it reads into `r`, put all registers it writes into `w`
  pub fn rw(&self, r: &mut Vec<Reg>, w: &mut Vec<Reg>) {
    use AsmTemplate::*;
    r.clear();
    w.clear();
    match *self {
      Bin(_, w1, r1, r2) => {
        r.push(r1);
        r.push(r2);
        w.push(w1);
      }
      BinI(_, w1, r1, _) | Un(_, w1, r1) | Mv(w1, r1) | Lw(w1, r1, _) => {
        r.push(r1);
        w.push(w1);
      }
      Jal(_) | Jalr(_) => {
        for a in regs::ARG { r.push(Reg::PreColored(a as u32)); }
        for crs in regs::CALLER_SAVE { w.push(Reg::PreColored(crs as u32)); }
        w.push(Reg::PreColored(regs::RA as u32));
        if let Jalr(r1) = *self { r.push(r1); }
      }
      J(_) | Label(_) => {}
      Ret => {
        for ces in regs::CALLEE_SAVE { r.push(Reg::PreColored(ces as u32)); }
        r.push(Reg::PreColored(regs::V0 as u32));
        r.push(Reg::PreColored(regs::V1 as u32)); // though we don't use v1 now, maybe we can extend it in the future?
      }
      B(_, r1, _) => r.push(r1),
      Sw(r1, r2, _) => {
        r.push(r1);
        r.push(r2);
      }
      Li(w1, _) | La(w1, _) => w.push(w1),
      SysCall(_) => {
        // syscall doesn't changed any (allocable) register except V0 for ret value
        r.push(Reg::PreColored(regs::A0 as u32)); // now we use A0 at most
        r.push(Reg::PreColored(regs::V0 as u32)); // syscall id
        w.push(Reg::PreColored(regs::V0 as u32)); // syscall ret value
      }
    };
  }

  // different from rw(), the pre-colored registers are not taken into consideration(because you can't spill them)
  // so the max size of the return value is fixed and doesn't need a Vec to store
  pub fn rw_mut(&mut self) -> ([Option<&mut Reg>; 2], Option<&mut Reg>) {
    use AsmTemplate::*;
    match self {
      Bin(_, w1, r1, r2) => ([Some(r1), Some(r2)], Some(w1)),
      BinI(_, w1, r1, _) | Un(_, w1, r1) | Mv(w1, r1) | Lw(w1, r1, _) =>
        ([Some(r1), None], Some(w1)),
      Jal(_) | J(_) | Label(_) | Ret => ([None, None], None),
      Jalr(r1) | B(_, r1, _) => ([Some(r1), None], None),
      Sw(r1, r2, _) => ([Some(r1), Some(r2)], None),
      Li(w1, _) | La(w1, _) => ([None, None], Some(w1)),
      SysCall(_) => ([None, None], None)
    }
  }

  pub fn imm_mut(&mut self) -> Option<&mut Imm> {
    use AsmTemplate::*;
    match self {
      BinI(_, _, _, i) | Lw(_, _, i) | Sw(_, _, i) | Li(_, i) => Some(i), _ => None
    }
  }

  // filter useless asm using some simple rules
  pub fn useless(&self) -> bool {
    match *self {
      AsmTemplate::BinI(op, d, l, r) if d.id() == l.id() => match op {
        // And is bitwise and, but it can only be applied to bool in decaf, so And 1 is nop
        BinOp::Add | BinOp::Sub | BinOp::Or if r == Imm::Int(0) => true,
        BinOp::Mul | BinOp::Div | BinOp::And if r == Imm::Int(1) => true,
        _ => false
      }
      AsmTemplate::Mv(w, r) if w.id() == r.id() => true,
      _ => false,
    }
  }
}


impl fmt::Debug for Imm {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match self { Imm::Int(i) => write!(f, "{}", i), Imm::Tag(i) => write!(f, "_I{}", i), }
  }
}

impl fmt::Debug for Reg {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    match self {
      Reg::PreColored(r) | Reg::Allocated(r) => write!(f, "{}", regs::NAME[*r as usize]),
      Reg::Virtual(r) => write!(f, "_R{}", r),
    }
  }
}

impl fmt::Debug for AsmTemplate {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    use AsmTemplate::*;
    match self {
      Bin(op, w1, r1, r2) => write!(f, "{} {:?}, {:?}, {:?}", bin_str(*op), w1, r1, r2),
      BinI(op, w1, r1, i) => write!(f, "{} {:?}, {:?}, {:?}", bin_str(*op), w1, r1, i),
      Un(op, w1, r1) => write!(f, "{} {:?}, {:?}", un_str(*op), w1, r1),
      Mv(w1, r1) => write!(f, "move {:?}, {:?}", w1, r1),
      Jal(l) => write!(f, "jal {}", l),
      Jalr(r1) => write!(f, "jalr {:?}", r1),
      J(l) => write!(f, "j {}", l),
      Ret => write!(f, "jr $ra"),
      B(l, r1, z) => write!(f, "{} {:?}, {}", if *z { "beqz" } else { "bnez" }, r1, l),
      Lw(w1, r1, i) => write!(f, "lw {:?}, {:?}({:?})", w1, i, r1),
      Sw(r1, r2, i) => write!(f, "sw {:?}, {:?}({:?})", r1, i, r2),
      Li(r1, i) => write!(f, "li {:?}, {:?}", r1, i),
      La(r1, a) => write!(f, "la {:?}, {}", r1, a),
      Label(l) => write!(f, "{}", l),
      SysCall(id) => {
        writeln!(f, "li $v0, {}", *id as u32).ignore();
        write!(f, "syscall")
      }
    }
  }
}

// we will output a lot of pseudo mips instructions, and depend on assembler or simulator to translate these pseudo instructions
pub fn bin_str(op: BinOp) -> &'static str {
  use BinOp::*;
  match op { Add => "addu", Sub => "subu", Mul => "mul", Div => "div", Mod => "rem", And => "and", Or => "or", Eq => "seq", Ne => "sne", Lt => "slt", Le => "sle", Gt => "sgt", Ge => "sge" }
}

pub fn un_str(op: UnOp) -> &'static str {
  match op { UnOp::Neg => "neg", UnOp::Not => "not" }
}