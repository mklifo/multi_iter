//! This crate provides an iterator which can act on multiple elements at once without any
//! allocations. These combinators are similar to those of [`std::iter::Iterator`].

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "unstable")]
use std::collections::BinaryHeap;

/// An iterator that provides combinators for acting on multiple elements at a time.
///
/// This `struct` is created by the `multi_iter` method on [`IntoMultiIterator`]. See its
/// documentation for more.
#[derive(Debug)]
pub struct MultiIterator<'a, T> {
    data: &'a [T],
    cursor: usize,
}

impl<'a, T> MultiIterator<'a, T> {
    /// Constructs a new, empty `MultiIterator<T>`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::MultiIterator;
    /// let iter = MultiIterator::new(&[1, 2, 3]);
    /// ```
    #[inline]
    pub fn new(data: &'a [T]) -> Self {
        Self { data, cursor: 0 }
    }

    /// Peeks the slice of the next `n` elements after the cursor.
    ///
    /// If there are less than `n` elements, [`None`] is returned instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::IntoMultiIterator;
    /// let a = [1, 2, 3];
    /// let iter = a.multi_iter();
    /// assert_eq!(iter.peek_n(2).unwrap(), [1, 2].as_ref());
    /// assert_eq!(iter.len(), 3);
    /// ```
    #[inline]
    pub fn peek_n(&self, n: usize) -> Option<&'a [T]> {
        self.span_next(n)
    }

    /// Peeks the remaining slice of elements after the cursor.
    ///
    /// If nothing is remaining, [`None`] is returned instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::IntoMultiIterator;
    /// let a = [1, 2, 3];
    /// let iter = a.multi_iter();
    /// assert_eq!(iter.peek_remaining().unwrap(), [1, 2, 3]);
    /// assert_eq!(iter.len(), 3);
    /// ```
    #[inline]
    pub fn peek_remaining(&self) -> Option<&'a [T]> {
        self.span_remaining()
    }

    /// Returns a slice of the next `n` elements after the cursor, which is then advanced by `n`.
    ///
    /// If there are less than `n` elements, [`None`] is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::IntoMultiIterator;
    /// let a = [1, 2, 3];
    /// let mut iter = a.multi_iter();
    /// assert_eq!(iter.next_n(2).unwrap(), [1, 2].as_ref());
    /// assert_eq!(iter.len(), 1);
    /// ```
    #[inline]
    pub fn next_n(&mut self, n: usize) -> Option<&'a [T]> {
        let span = self.span_next(n)?;
        self.advance_cursor(span.len());
        Some(span)
    }

    /// Returns a slice of the next `n` elements after the cursor if `func` is true for each element
    /// in the slice. The cursor is then advanced by `n`.
    ///
    /// If there are less than `n` elements, or `func` returns false, [`None`] is returned instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::IntoMultiIterator;
    /// let a = [1, 2, 3];
    /// let mut iter = a.multi_iter();
    /// let items = iter.next_n_if_each(2, |x| *x >= 1).unwrap();
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(iter.len(), 1);
    /// ```
    #[inline]
    pub fn next_n_if_each(&mut self, n: usize, func: impl Fn(&'a T) -> bool) -> Option<&'a [T]> {
        let span = self.span_next(n)?;
        for elem in span {
            if !func(elem) {
                return None;
            }
        }
        self.advance_cursor(span.len());
        Some(span)
    }

    /// Returns a slice of the next `n` elements after the cursor if `func` is true for the entire
    /// slice. The cursor is then advanced by `n`.
    ///
    /// If there are less than `n` elements, or `func` returns false, [`None`] is returned instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::IntoMultiIterator;
    /// let a = [1, 2, 3];
    /// let mut iter = a.multi_iter();
    /// let items = iter.next_n_if_slice(2, |x| x[0] == 1 && x[1] == 2).unwrap();
    /// assert_eq!(items.len(), 2);
    /// assert_eq!(iter.len(), 1);
    /// ```
    #[inline]
    pub fn next_n_if_slice(
        &mut self,
        n: usize,
        func: impl FnOnce(&'a [T]) -> bool,
    ) -> Option<&'a [T]> {
        let span = self.span_next(n)?;
        if func(span) {
            self.advance_cursor(span.len());
            Some(span)
        } else {
            None
        }
    }

    /// Returns a slice of the remaining elements. This is useful if you want something similar to
    /// [`std::iter::Iterator::collect`] without allocating.
    ///
    /// If there is nothing remaining, [`None`] is returned instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::IntoMultiIterator;
    /// let iter = [1, 2, 3].multi_iter();
    /// let items = iter.remaining().unwrap();
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(items[2], 3);
    /// ```
    #[inline]
    pub fn remaining(self) -> Option<&'a [T]> {
        self.span_remaining()
    }

    /// Returns a slice of the remaining elements if `func` is true for each element in the slice.
    ///
    /// Otherwise, if nothing is remaining or `func` returns false, [`None`] is returned instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::IntoMultiIterator;
    /// let iter = [1, 2, 3].multi_iter();
    /// let items = iter.remaining_if_each(|x| *x >= 1).unwrap();
    /// assert_eq!(items.len(), 3);
    /// ```
    #[inline]
    pub fn remaining_if_each(self, func: impl Fn(&'a T) -> bool) -> Option<&'a [T]> {
        let span = self.span_remaining()?;
        for elem in span {
            if !func(elem) {
                return None;
            }
        }
        Some(span)
    }

    /// Returns a slice of the remaining elements if `func` is true for the entire slice.
    ///
    /// Otherwise, if nothing is remaining or `func` returns false, [`None`] is returned intsead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use multi_iter::IntoMultiIterator;
    /// let iter = [1, 2, 3].multi_iter();
    /// let items = iter.remaining_if_slice(|x| {
    ///     x[0] == 1 && x[1] == 2 && x[2] == 3
    /// }).unwrap();
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(items[2], 3);
    /// ```
    #[inline]
    pub fn remaining_if_slice(self, func: impl FnOnce(&'a [T]) -> bool) -> Option<&'a [T]> {
        let span = self.span_remaining()?;
        if !func(span) {
            None
        } else {
            Some(span)
        }
    }

    /// Creates a span over the next `n` elements after the cursor. Returns [`None`] if there are
    /// less than `n` elements.
    #[inline]
    fn span_next(&self, n: usize) -> Option<&'a [T]> {
        let start = self.cursor;
        let end = start + n;
        if end > self.data.len() {
            None
        } else {
            Some(&self.data[start..end])
        }
    }

    /// Creates a span over the remaining of the elements after the cursor. Returns [`None`] if
    /// there are no elements remaining.
    #[inline]
    fn span_remaining(&self) -> Option<&'a [T]> {
        if self.len() == 0 {
            None
        } else {
            self.span_next(self.len())
        }
    }

    /// Advances the cursor by `n`.
    #[inline]
    fn advance_cursor(&mut self, n: usize) {
        self.cursor += n;
    }
}

impl<'a, T> Iterator for MultiIterator<'a, T> {
    type Item = &'a T;

    /// Returns the next element and advances the cursor by one.
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.data.get(self.cursor);
        self.advance_cursor(1);
        item
    }
}

impl<'a, T> ExactSizeIterator for MultiIterator<'a, T> {
    /// Returns the distance between the cursor and the end of the wrapped `data`.
    #[inline]
    fn len(&self) -> usize {
        self.data.len() - self.cursor
    }
}

/// Conversion into a [`MultiIterator`].
///
/// By implementing `IntoMultiIterator` for a type, you define how it will be converted into a
/// multi iterator.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use multi_iter::IntoMultiIterator;
/// let iter = [1, 2, 3].multi_iter();
/// ```
pub trait IntoMultiIterator<'a> {
    type Item;

    fn multi_iter(&'a self) -> MultiIterator<'a, Self::Item>;
}

impl<'a, T> IntoMultiIterator<'a> for [T] {
    type Item = T;

    #[inline]
    fn multi_iter(&'a self) -> MultiIterator<'a, Self::Item> {
        MultiIterator::new(self)
    }
}

#[cfg(feature = "std")]
impl<'a, T> IntoMultiIterator<'a> for Vec<T> {
    type Item = T;

    #[inline]
    fn multi_iter(&'a self) -> MultiIterator<'a, Self::Item> {
        MultiIterator::new(self.as_slice())
    }
}

#[cfg(feature = "std")]
#[cfg(feature = "unstable")]
impl<'a, T> IntoMultiIterator<'a> for BinaryHeap<T> {
    type Item = T;

    #[inline]
    fn multi_iter(&'a self) -> MultiIterator<'a, Self::Item> {
        MultiIterator::new(self.as_slice())
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_peek_n() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let iter = a.multi_iter();
        let items = iter.peek_n(3).unwrap();

        assert_eq!(iter.len(), 3);
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);

        assert!(iter.peek_n(4).is_none());
    }

    #[test]
    fn test_peek_remaining() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let iter = a.multi_iter();
        assert_eq!(iter.len(), 3);

        let items = iter.peek_remaining().unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
    }

    #[test]
    fn test_next_n() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let mut iter = a.multi_iter();

        let items = iter.next_n(4);
        assert!(items.is_none());

        let items = iter.next_n(3).unwrap();
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
    }

    #[test]
    fn test_next_n_if_each() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let mut iter = a.multi_iter();

        assert!(iter.next_n_if_each(3, |x| *x > 1).is_none());

        let items = iter.next_n_if_each(3, |x| *x >= 1).unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
    }

    #[test]
    fn test_next_n_if_slice() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let mut iter = a.multi_iter();

        let items = iter.next_n_if_slice(3, |x| x[0] == 1 && x[1] == 2 && x[2] == 4);
        assert!(items.is_none());

        let items = iter
            .next_n_if_slice(3, |x| x[0] == 1 && x[1] == 2 && x[2] == 3)
            .unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
    }

    #[test]
    fn test_remaining() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let iter = a.multi_iter();
        assert_eq!(iter.len(), 3);

        let items = iter.remaining().unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
    }

    #[test]
    fn test_remaining_if_each() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];

        let items = a.multi_iter().remaining_if_each(|x| *x >= 1).unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);

        assert!(a.multi_iter().remaining_if_each(|x| *x > 1).is_none());
    }

    #[test]
    fn test_remaining_if_slice() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];

        assert!(a
            .multi_iter()
            .remaining_if_slice(|x| { x[0] == 1 && x[1] == 2 && x[2] == 4 })
            .is_none());

        let items = a
            .multi_iter()
            .remaining_if_slice(|x| x[0] == 1 && x[1] == 2 && x[2] == 3)
            .unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
    }
}
