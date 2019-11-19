#![feature(result_map_or_else)]

pub mod test_util;

use common::{IndentPrinter, Errors};
use syntax::{ASTAlloc, Ty, parser, parser_ll};
use typeck::TypeCkAlloc;
use tacopt::bb::FuncBB;
use codegen::mips_gen::FuncGen;
use tac::TacNode;
use typed_arena::Arena;

pub use test_util::*;

#[derive(Eq, PartialEq, Copy, Clone)]
pub enum Stage { Parse, TypeCk, Tac, TacOpt, Asm }

#[derive(Copy, Clone)]
pub enum Parser { LL, LR }

#[derive(Copy, Clone)]
pub struct CompileCfg {
  pub stage: Stage,
  pub parser: Parser,
}

#[derive(Default)]
pub struct Alloc<'a> {
  ast: ASTAlloc<'a>,
  typeck: TypeCkAlloc<'a>,
  tac: Arena<TacNode<'a>>,
}

// it is recommended to use this function to debug your compiler
// `code` can be provided by hard-coded string literal, `cfg` can be provided by `Pa::Pax.to_cfg()`
pub fn compile<'a>(code: &'a str, alloc: &'a Alloc<'a>, cfg: CompileCfg) -> Result<String, Errors<'a, Ty<'a>>> {
  let mut p = IndentPrinter::default();
  let pr = match cfg.parser {
    Parser::LL => parser_ll::work(code, &alloc.ast)?,
    Parser::LR => parser::work(code, &alloc.ast)?,
  };
  if cfg.stage == Stage::Parse {
    print::ast::program(&pr, &mut p);
    return Ok(p.finish());
  }
  typeck::work(&pr, &alloc.typeck)?;
  if cfg.stage == Stage::TypeCk {
    print::scope::program(&pr, &mut p);
    return Ok(p.finish());
  }
  let mut tp = tacgen::work(&pr, &alloc.tac);
  if cfg.stage == Stage::Tac {
    print::tac::program(&tp, &mut p);
    return Ok(p.finish());
  }
  if cfg.stage == Stage::Asm {
    print::mips::data(&tp, &mut p);
  }
  let mut new_funcs = Vec::new();
  for f in &tp.func {
    let mut fu = FuncBB::new(f);
    fu.optimizen(10);
    if cfg.stage == Stage::Asm {
      let asm = FuncGen::work(&fu, &tp, codegen::AllocMethod::Graph);
      print::mips::func(&asm, &f.name, &mut p);
    } else { // cfg.stage == Stage::TacOpt
      new_funcs.push(fu.to_tac_func());
    }
  }
  if cfg.stage == Stage::TacOpt {
    tp.func = new_funcs;
    print::tac::program(&tp, &mut p);
    Ok(p.finish())
  } else { Ok(p.finish() + include_str!("../../codegen/lib.s")) }
}