use crate::TacNode;
use std::iter::FusedIterator;

// these codes are basically copied from std::collections::LinkedList

#[derive(Copy, Clone)]
pub struct TacIter<'a> {
  first: Option<&'a TacNode<'a>>,
  last: Option<&'a TacNode<'a>>,
  len: usize,
}

impl<'a> TacIter<'a> {
  pub fn new(first: Option<&'a TacNode<'a>>, last: Option<&'a TacNode<'a>>, len: usize) -> TacIter<'a> {
    TacIter { first, last, len }
  }
}

impl<'a> Iterator for TacIter<'a> {
  type Item = &'a TacNode<'a>;

  fn next(&mut self) -> Option<Self::Item> {
    if self.len != 0 {
      self.first.map(|x| {
        self.len -= 1;
        self.first = x.next.get();
        x
      })
    } else { None }
  }

  fn size_hint(&self) -> (usize, Option<usize>) { (self.len, Some(self.len)) }
  fn count(self) -> usize { self.len }
}

impl<'a> DoubleEndedIterator for TacIter<'a> {
  fn next_back(&mut self) -> Option<Self::Item> {
    if self.len != 0 {
      self.last.map(|x| {
        self.len -= 1;
        self.last = x.prev.get();
        x
      })
    } else { None }
  }
}

impl ExactSizeIterator for TacIter<'_> {}

impl FusedIterator for TacIter<'_> {}