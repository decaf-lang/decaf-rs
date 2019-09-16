// http://www.cse.iitm.ac.in/~krishna/cs6013/george.pdf

use common::{HashSet, IndexSet};
use std::marker::PhantomData;
use crate::Reg;

pub trait AllocCtx: Sized {
  // number of registers to allocate
  const K: u32;

  // return (initial virtual register, initial nodes)
  // pre-colored and normal registers are indexed in the same way, you can make a difference between them by using different number ranges
  fn initial(&self) -> (Vec<u32>, Vec<Node>);

  // build inference graph
  fn build(&self, allocator: &mut Allocator<Self>);

  // generate spill related code, no need to build inference graph here, because build() will be called again
  fn rewrite(&mut self, spilled_nodes: &HashSet<u32>);

  fn finish(&mut self, result: &[Node]);
}

pub struct Node {
  pub degree: u32,
  pub alias: u32,
  pub color: Reg,
  pub adj_list: Vec<u32>,
  pub move_list: Vec<(u32, u32)>,
}

impl Node {
  pub fn new(color: Reg) -> Node {
    // pre-colored register's degree is set to a very big value(>= K + number of nodes is ok)
    let degree = if let Reg::PreColored(_) = color { std::u32::MAX } else { 0 };
    Node { degree, alias: 0, color, adj_list: Vec::new(), move_list: Vec::new() }
  }

  pub fn pre_colored(&self) -> bool {
    match self.color { Reg::PreColored(_) => true, _ => false, }
  }

  pub fn expect_colored(&self) -> u32 {
    match self.color {
      Reg::PreColored(r) | Reg::Allocated(r) => r,
      Reg::Virtual(r) => panic!("Register allocation not finished yet, now is virtual register {}.", r),
    }
  }
}

// some fields the paper mentions are not really necessary, I leave them in comments
// some fields doesn't need to be a set, because only push(guaranteed unique) and iteration are required
// some fields need to be a set and need to record insertion order, use IndexSet
pub struct Allocator<A: AllocCtx> {
  pub nodes: Vec<Node>,
  // machine registers, preassigned a color
  // pre_colored: HashSet<u32>,
  // virtual registers, not preassigned a color and not yet processed by the algorithm
  initial: Vec<u32>,
  // list of low-degree non-move-related nodes
  simplify_work_list: HashSet<u32>,
  // low-degree move-related nodes
  freeze_work_list: HashSet<u32>,
  // high-degree nodes
  spill_work_list: HashSet<u32>,
  // nodes marked for spilling during this round; initially empty
  spilled_nodes: HashSet<u32>,
  // registers that have been coalesced;
  // when the move u = v is coalesced, one of u or v is added to this set, and the other is put back on some work list
  coalesced_nodes: HashSet<u32>,
  // nodes successfully colored
  // colored_nodes: Vec<u32>,
  // stack containing temporaries removed from the graph
  select_stack: IndexSet<u32>,
  // moves that have been coalesced
  // coalesced_moves: HashSet<(u32, u32)>,
  // moves whose source and target interfere
  // constrained_moves: HashSet<(u32, u32)>,
  // moves that will no longer be considered for coalescing
  // frozen_moves: HashSet<(u32, u32)>,
  // moves enabled for possible coalescing
  pub work_list_moves: HashSet<(u32, u32)>,
  // moves not yet ready for coalescing
  active_moves: HashSet<(u32, u32)>,
  adj_set: HashSet<(u32, u32)>,
  _p: PhantomData<A>,
}

impl<A: AllocCtx> Allocator<A> {
  pub fn work(ctx: &mut A) {
    // unluckily cannot use #[derive(Default)] because A may not be Default, even though PhantomData<A> is
    // I still don't know why rust has such a requirement
    let mut a = Allocator { nodes: Vec::new(), initial: Vec::new(), simplify_work_list: HashSet::new(), freeze_work_list: HashSet::new(), spill_work_list: HashSet::new(), spilled_nodes: HashSet::new(), coalesced_nodes: HashSet::new(), select_stack: IndexSet::default(), work_list_moves: HashSet::new(), active_moves: HashSet::new(), adj_set: HashSet::new(), _p: PhantomData };
    // actually no information in `a` is preserved for the next loop
    // because in this simple variant of this algo, all coalesces are discarded if spill happens
    // so the only reason for creating `a` outside the loop is to reuse some memory
    // should remember to clear all fields after each iteration step (`initial` and `nodes` doesn't have to be cleared because they will be reassigned)
    let nodes = loop {
      let (initial, nodes) = ctx.initial();
      a.initial = initial;
      a.nodes = nodes;
      ctx.build(&mut a);
      a.mk_work_list();
      loop {
        match () { // just to avoid many if-else
          _ if !a.simplify_work_list.is_empty() => a.simplify(),
          _ if !a.work_list_moves.is_empty() => a.coalesce(),
          _ if !a.freeze_work_list.is_empty() => a.freeze(),
          _ if !a.spill_work_list.is_empty() => a.select_spill(),
          _ => break,
        }
      }
      a.assign_color();
      if !a.spilled_nodes.is_empty() {
        a.rewrite_program(ctx);
      } else { break a.nodes; }
    };
    ctx.finish(&nodes);
  }

  pub fn add_edge(&mut self, u: u32, v: u32) {
    if u != v && !self.adj_set.contains(&(u, v)) {
      self.adj_set.insert((u, v));
      self.adj_set.insert((v, u));
      let (u, v) = (u as usize, v as usize);
      // pre colored register can be the dest of edge, but not the src(or it's adj_list may be too big)
      // its degree will not grow, but can decrease starting from std::u32::MAX(still won't have any effect, can never have a degree < K)
      if !self.nodes[u].pre_colored() {
        self.nodes[u].adj_list.push(v as u32);
        self.nodes[u].degree += 1;
      }
      if !self.nodes[v].pre_colored() {
        self.nodes[v].adj_list.push(u as u32);
        self.nodes[v].degree += 1;
      }
    }
  }

  // the paper defines many functions that return a set of nodes, we don't really need to allocate space for a set, using an iterator is better
  // however rust's lifetime requirement almost make it impossible to define such functions that return an iterator
  // because it must borrow self as an whole, so you can't modify any other fields which are not involved in this iterator
  // the solution is to inline these functions manually, then it will only borrow some fields of self, not self as an whole

  fn mk_work_list(&mut self) {
    unimplemented!()  
  }

  fn simplify(&mut self) {
    unimplemented!()
  }

  fn coalesce(&mut self) {
    unimplemented!()
  }

  fn get_alias(&self, mut _n: u32) -> u32 {
    unimplemented!()
  }

  fn freeze(&mut self) {
    unimplemented!()
  }

  fn select_spill(&mut self) {
    unimplemented!()
  }

  fn assign_color(&mut self) {
    let mut available = HashSet::with_capacity(A::K as usize);
    for &n in self.select_stack.iter().rev() { // pop all, need to traverse reversely
      available.clear();
      for i in 0..A::K { available.insert(i); }
      for &w in &self.nodes[n as usize].adj_list {
        let a = self.get_alias(w);
        match self.nodes[a as usize].color {
          Reg::PreColored(r) | Reg::Allocated(r) => { available.remove(&r); }
          Reg::Virtual(_) => {}
        };
      }
      // PreColored select_stack should never be added to select_stack, so this assign will not violate the requirement
      match available.iter().nth(0) {
        Some(r) => {
          self.nodes[n as usize].color = Reg::Allocated(*r);
        }
        None => { self.spilled_nodes.insert(n); }
      };
    }
    self.select_stack.clear();
    for &n in &self.coalesced_nodes {
      self.nodes[n as usize].color = self.nodes[self.get_alias(n) as usize].color;
    }
  }

  fn rewrite_program(&mut self, ctx: &mut A) {
    ctx.rewrite(&self.spilled_nodes);
    self.spilled_nodes.clear();
    self.coalesced_nodes.clear();
    self.active_moves.clear();
    self.adj_set.clear();
  }
}