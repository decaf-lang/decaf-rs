// it can be helpful when you know a Result is definitely Ok/Some and doesn't need its value
// because it can suppress the warning from rustc about 'unused result which must be used'
// (of course if you don't care about warnings, this is useless)
pub trait IgnoreResult: Sized {
  fn ignore(self) {}
}

impl<V, E> IgnoreResult for Result<V, E> {}

impl<T> IgnoreResult for Option<T> {}