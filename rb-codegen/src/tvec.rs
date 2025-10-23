use std::{
  fmt,
  ops::{
    Deref, DerefMut, Index, IndexMut, Range, RangeFrom, RangeInclusive, RangeTo, RangeToInclusive,
  },
};

#[derive(Clone, PartialEq, Eq)]
pub struct TVec<K, T>(Vec<T>, std::marker::PhantomData<K>);

impl<K, T> Default for TVec<K, T> {
  fn default() -> Self { Self::new() }
}

pub trait TIndex<T> {
  fn from_index(index: usize) -> Self;
  fn to_index(self) -> usize;
}

impl<K, T> TVec<K, T> {
  pub const fn new() -> Self { TVec(Vec::new(), std::marker::PhantomData) }

  pub const fn as_slice(&self) -> &[T] { self.0.as_slice() }
  pub const fn as_mut_slice(&mut self) -> &mut [T] { self.0.as_mut_slice() }
}

impl<K, T> TVec<K, T>
where
  K: TIndex<T>,
{
  pub fn get(&self, index: K) -> Option<&T> { self.0.get(index.to_index()) }
  #[track_caller]
  pub fn set(&mut self, index: K, value: T) {
    let idx = index.to_index();
    if self.0.len() == idx {
      self.0.push(value);
    } else {
      self.0[idx] = value;
    }
  }
  pub fn set_with(&mut self, index: K, value: T, def: impl Fn() -> T) {
    let idx = index.to_index();
    if self.0.len() == idx {
      self.0.push(value);
    } else if self.0.len() < idx {
      self.0.resize_with(idx + 1, def);
      self.0[idx] = value;
    } else {
      self.0[idx] = value;
    }
  }

  pub fn enumerate(&self) -> impl Iterator<Item = (K, &T)> {
    self.0.iter().enumerate().map(|(i, v)| (K::from_index(i), v))
  }
}

impl<K, T> Deref for TVec<K, T> {
  type Target = Vec<T>;

  fn deref(&self) -> &Self::Target { &self.0 }
}

impl<K, T> DerefMut for TVec<K, T> {
  fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
}

impl<K, T> From<Vec<T>> for TVec<K, T> {
  fn from(v: Vec<T>) -> Self { TVec(v, std::marker::PhantomData) }
}

macro_rules! index {
  ($idx:ty, $pred:ty, $convert:expr) => {
    impl<T, I: TIndex<T>> Index<$idx> for TVec<I, T> {
      type Output = <[T] as Index<$pred>>::Output;

      #[inline]
      fn index(&self, i: $idx) -> &Self::Output { &self.0[$convert(i)] }
    }

    impl<T, I: TIndex<T>> IndexMut<$idx> for TVec<I, T> {
      #[inline]
      fn index_mut(&mut self, i: $idx) -> &mut Self::Output { &mut self.0[$convert(i)] }
    }
  };
}

index!(I, usize, |i: I| i.to_index());
index!(Range<I>, Range<usize>, |i: Range<I>| i.start.to_index()..i.end.to_index());
index!(RangeFrom<I>, RangeFrom<usize>, |i: RangeFrom<I>| i.start.to_index()..);
index!(RangeTo<I>, RangeTo<usize>, |i: RangeTo<I>| ..i.end.to_index());
index!(RangeInclusive<I>, RangeInclusive<usize>, |i: RangeInclusive<I>| {
  let (start, end) = i.into_inner();
  start.to_index()..=end.to_index()
});
index!(RangeToInclusive<I>, RangeToInclusive<usize>, |i: RangeToInclusive<I>| {
  ..=i.end.to_index()
});

impl<'a, K, T> IntoIterator for &'a TVec<K, T> {
  type Item = &'a T;
  type IntoIter = std::slice::Iter<'a, T>;

  fn into_iter(self) -> Self::IntoIter { self.0.iter() }
}

impl<'a, K, T> IntoIterator for &'a mut TVec<K, T> {
  type Item = &'a mut T;
  type IntoIter = std::slice::IterMut<'a, T>;

  fn into_iter(self) -> Self::IntoIter { self.0.iter_mut() }
}

impl<K, T> IntoIterator for TVec<K, T> {
  type Item = T;
  type IntoIter = std::vec::IntoIter<T>;

  fn into_iter(self) -> Self::IntoIter { self.0.into_iter() }
}

impl<K, T> fmt::Debug for TVec<K, T>
where
  T: fmt::Debug,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}
