use syntax::FuncDef;
use common::IndexMap;

// these structs are used in tacgen to keep some intermediate information

pub struct VarInfo {
  // if the var is a VarDef in class, `off` is the offset in object pointer
  // if the var is a VarDef in function, `off` is a virtual register number
  pub off: u32,
}

pub struct FuncInfo {
  // the offset in vtbl
  // vtbl[0] = parent, vtbl[1] = class name
  pub off: u32,
  // which function it is in TacProgram (index in TacProgram::func)
  pub idx: u32,
}

pub struct ClassInfo<'a> {
  pub field_num: u32,
  // which vtbl it's vtbl is in TacProgram (index in TacProgram::vtbl)
  pub idx: u32,
  pub vtbl: IndexMap<&'a str, &'a FuncDef<'a>>,
}