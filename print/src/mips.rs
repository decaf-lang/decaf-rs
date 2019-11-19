use common::{IndentPrinter, IgnoreResult};
use tac::{TacProgram};
use codegen::mips::AsmTemplate;
use std::fmt::Write;

pub fn data(pr: &TacProgram, p: &mut IndentPrinter) {
  write!(p, ".data").ignore();
  write!(p, ".align 2").ignore();
  for v in &pr.vtbl {
    write!(p, "_{}:", v.class).ignore();
    p.indent(|p| {
      if let Some(pa) = v.parent {
        write!(p, ".word _{}", pr.vtbl[pa as usize].class).ignore();
      } else {
        write!(p, ".word 0").ignore();
      }
      write!(p, ".word _STRING{}", pr.str_pool.get_full(v.class).expect("tacgen should have put class name into `str_pool`").0).ignore();
      for &f in &v.func {
        write!(p, ".word {}", pr.func[f as usize].name).ignore();
      }
    });
  }
  writeln!(p).ignore();
  write!(p, ".data").ignore();
  for (idx, s) in pr.str_pool.iter().enumerate() {
    write!(p, "_STRING{}:", idx).ignore();
    p.indent(|p| write!(p, ".asciiz \"{}\"", s).ignore());
  }
  writeln!(p).ignore();
}

pub fn func(f: &[AsmTemplate], name: &str, p: &mut IndentPrinter) {
  write!(p, ".text").ignore();
  write!(p, ".globl {}", name).ignore();
  write!(p, "{}:", name).ignore();
  p.indent(|p| for asm in f { write!(p, "{:?}", asm).ignore(); });
  writeln!(p).ignore();
}