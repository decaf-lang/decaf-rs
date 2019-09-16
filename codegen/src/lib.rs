pub mod mips;
pub mod mips_gen;
pub mod graph_alloc;
pub mod brute_alloc;

pub enum AllocMethod { Graph, Brute }

// PreColored/Allocated's values both mean machine register number
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum Reg {
  PreColored(u32),
  Allocated(u32),
  Virtual(u32),
}

impl Reg {
  // no matter what kind of reg it is, this function just return its id, although their meaning may be different
  pub fn id(&self) -> u32 {
    match *self { Reg::PreColored(r) => r, Reg::Allocated(r) => r, Reg::Virtual(r) => r }
  }
}