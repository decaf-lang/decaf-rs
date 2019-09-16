// https://en.wikipedia.org/wiki/Semilattice
pub trait Meet<T: Copy> {
  const TOP: T;

  fn meet(x: T, y: T) -> T;
}

pub struct And;

impl Meet<u32> for And {
  const TOP: u32 = !0;

  fn meet(x: u32, y: u32) -> u32 { x & y }
}

pub struct Or;

impl Meet<u32> for Or {
  const TOP: u32 = 0;

  fn meet(x: u32, y: u32) -> u32 { x | y }
}

// this is a forward flow infrastructure
// if you want a backward flow, do the replacement: backward { use_, kill, in_, out } <-> forward { gen, def, out, in_ }
// please forgive me for making code more complex, but I really want to improve performance
pub struct Flow<M> {
  inner: Vec<u32>,
  // inner.len() == 4 * n * each for `n` elements each using `each` u32
  n: usize,
  each: usize,
  _p: std::marker::PhantomData<M>,
}

impl<M: Meet<u32>> Flow<M> {
  // `each` is the number of BITS
  pub fn new(n: usize, each: usize) -> Flow<M> {
    let each = bitset::traits::bslen(each);
    Flow { inner: vec![0; 4 * n * each], n, each, _p: std::marker::PhantomData }
  }

  // if the edges of a node in the graph are empty, the `in_` will always be M::TOP
  // which may not be desirable if M is `And`, so you need to add a virtual entry node with `out` = empty
  // but if M is `Or`, it is okay without that virtual node, because M::TOP == 0, which is what we expect
  pub fn solve<I: IntoIterator<Item=usize>>(&mut self, graph: impl IntoIterator<Item=(usize, I)> + Clone) {
    let (n, each) = (self.n, self.each);
    assert_eq!(4 * n * each, self.inner.len());
    // rust doesn't allow index out of range when slicing, even if the slice is empty, so just return to avoid a panic!()
    if self.inner.is_empty() { return; }

    for in_ in self.split().in_ { *in_ = M::TOP; }
    let mut changed = true;
    while changed {
      changed = false;
      let FlowElem { in_, out, .. } = self.split();
      for (this, edges) in graph.clone() {
        let off = this * each;
        for edge in edges {
          let off1 = edge * each;
          for (x, y) in in_[off..off + each].iter_mut().zip(out[off1..off1 + each].iter()) {
            *x = M::meet(*x, *y);
          }
        }
      }
      let FlowElem { gen, kill, in_, out, .. } = self.split();
      for i in 0..(n * each) {
        // I have checked output assembly, unfortunately rustc & llvm currently can NOT optimize these range checks
        // if this project is not a course exercise, I will not hesitate at all to use unsafe here
        let ox = out[i];
        out[i] = gen[i] | (in_[i] & !kill[i]);
        changed |= out[i] != ox;
      }
    }
  }

  pub fn get(&mut self, idx: usize) -> FlowElem {
    let each = self.each;
    let FlowElem { gen, kill, in_, out } = self.split();
    FlowElem { gen: &mut gen[idx..idx + each], kill: &mut kill[idx..idx + each], in_: &mut in_[idx..idx + each], out: &mut out[idx..idx + each] }
  }

  pub fn split(&mut self) -> FlowElem {
    let each_arr = self.n * self.each;
    let (gen, rem) = self.inner.split_at_mut(each_arr);
    let (kill, rem) = rem.split_at_mut(each_arr);
    let (in_, rem) = rem.split_at_mut(each_arr);
    let (out, _) = rem.split_at_mut(each_arr);
    FlowElem { gen, kill, in_, out }
  }

  pub fn n(&self) -> usize { self.n }
  pub fn each(&self) -> usize { self.each }
}

pub struct FlowElem<'a> {
  pub gen: &'a mut [u32],
  pub kill: &'a mut [u32],
  pub in_: &'a mut [u32],
  pub out: &'a mut [u32],
}