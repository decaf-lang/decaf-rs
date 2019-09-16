use std::{hash::{Hash, Hasher}, cmp::Ordering, ops::Deref};

// comparing reference by their pointer value (this is 100% safe rust)
pub struct Ref<'a, T>(pub &'a T);

impl<T> Clone for Ref<'_, T> {
  fn clone(&self) -> Self { Self(self.0) }
}

impl<T> Copy for Ref<'_, T> {}

impl<T> PartialEq for Ref<'_, T> {
  fn eq(&self, other: &Self) -> bool {
    self.0 as *const T == other.0 as *const T
  }
}

impl<T> Eq for Ref<'_, T> {}

impl<T> PartialOrd for Ref<'_, T> {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    (self.0 as *const T).partial_cmp(&(other.0 as *const T))
  }
}

impl<T> Ord for Ref<'_, T> {
  fn cmp(&self, other: &Self) -> Ordering {
    (self.0 as *const T).cmp(&(other.0 as *const T))
  }
}

impl<T> Hash for Ref<'_, T> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    (self.0 as *const T).hash(state)
  }
}

impl<T> Deref for Ref<'_, T> {
  type Target = T;

  fn deref(&self) -> &Self::Target { self.0 }
}
