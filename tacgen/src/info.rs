use syntax::FuncDef;
use common::IndexMap;

// these structs are used in tacgen to keep some intermediate information

pub struct VarInfo {
  // for a VarDef in class, it is the offset in object pointer
  // for a VarDef in function, it is the virtual register number
  pub off: u32,
}

pub struct FuncInfo {
  // the offset in vtbl
  // vtbl[0] = parent, vtbl[1] = class name
  pub off: u32,
  // which function it is in TacProgram
  pub idx: u32,
}

pub struct ClassInfo<'a> {
  pub field_cnt: u32,
  // which vtbl it's vtbl is in TacProgram
  pub idx: u32,
  pub vtbl: IndexMap<&'a str, &'a FuncDef<'a>>,
}