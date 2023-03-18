//! This crate provides an iterator which can act on multiple elements at once without any
//! allocations. Its functions are similar to [`std::iter::Iterator`].

#![cfg_attr(not(feature = "std"), no_std)]

use std::iter::FusedIterator;

#[cfg(feature = "unstable")]
use std::collections::BinaryHeap;

/// An iterator that provides functions for acting on multiple elements at a time.
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
    ///
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
    ///
    /// let a = [1, 2, 3];
    /// let iter = a.multi_iter();
    /// let items = iter.peek_n(2).unwrap();
    ///
    /// assert_eq!(items.len(), 2); 
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(iter.len(), 3);
    /// ```
    #[inline]
    pub fn peek_n(&self, n: usize) -> Option<&'a [T]> {
        if n == 0 {
            return None;
        }

        let start = self.cursor;
        let end = start + n;
        if end > self.data.len() {
            None
        } else {
            Some(&self.data[start..end])
        }
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
    ///
    /// let a = [1, 2, 3];
    /// let iter = a.multi_iter();
    /// let items = iter.peek_remaining().unwrap();
    ///
    /// assert_eq!(items.len(), 3);
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(items[2], 3);
    /// assert_eq!(iter.len(), 3);
    /// ```
    #[inline]
    pub fn peek_remaining(&self) -> Option<&'a [T]> {
        if self.len() == 0 {
            None
        } else {
            self.peek_n(self.len())
        }
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
    ///
    /// let a = [1, 2, 3];
    /// let mut iter = a.multi_iter();
    /// let items = iter.next_n(2).unwrap();
    ///
    /// assert_eq!(items.len(), 2);
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(iter.len(), 1);
    /// ```
    #[inline]
    pub fn next_n(&mut self, n: usize) -> Option<&'a [T]> {
        let span = self.peek_n(n)?;
        self.cursor += span.len();
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
    ///
    /// let a = [1, 2, 3];
    /// let mut iter = a.multi_iter();
    /// let items = iter.next_n_if_each(2, |x| *x >= 1).unwrap();
    ///
    /// assert_eq!(items.len(), 2);
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(iter.len(), 1);
    /// ```
    #[inline]
    pub fn next_n_if_each(&mut self, n: usize, func: impl Fn(&'a T) -> bool) -> Option<&'a [T]> {
        let span = self.peek_n(n)?;
        for elem in span {
            if !func(elem) {
                return None;
            }
        }
        self.cursor += span.len();
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
    ///
    /// let a = [1, 2, 3];
    /// let mut iter = a.multi_iter();
    /// let items = iter.next_n_if_slice(2, |x| x[0] == 1 && x[1] == 2).unwrap();
    ///
    /// assert_eq!(items.len(), 2);
    /// assert_eq!(iter.len(), 1);
    /// ```
    #[inline]
    pub fn next_n_if_slice(
        &mut self,
        n: usize,
        func: impl FnOnce(&'a [T]) -> bool,
    ) -> Option<&'a [T]> {
        let span = self.peek_n(n)?;
        if func(span) {
            self.cursor += span.len();
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
    ///
    /// let a = [1, 2, 3];
    /// let iter = a.multi_iter();
    /// let items = iter.remaining().unwrap();
    ///
    /// assert_eq!(items.len(), 3);
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(items[2], 3);
    /// ```
    #[inline]
    pub fn remaining(self) -> Option<&'a [T]> {
        self.peek_remaining()
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
    ///
    /// let a = [1, 2, 3];
    /// let iter = a.multi_iter();
    /// let items = iter.remaining_if_each(|x| *x >= 1).unwrap();
    ///
    /// assert_eq!(items.len(), 3);
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(items[2], 3);
    /// ```
    #[inline]
    pub fn remaining_if_each(self, func: impl Fn(&'a T) -> bool) -> Option<&'a [T]> {
        let span = self.peek_remaining()?;
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
    ///
    /// let a = [1, 2, 3];
    /// let iter = a.multi_iter();
    /// let items = iter.remaining_if_slice(|x| {
    ///     x[0] == 1 && x[1] == 2 && x[2] == 3
    /// }).unwrap();
    ///
    /// assert_eq!(items.len(), 3);
    /// assert_eq!(items[0], 1);
    /// assert_eq!(items[1], 2);
    /// assert_eq!(items[2], 3);
    /// ```
    #[inline]
    pub fn remaining_if_slice(self, func: impl FnOnce(&'a [T]) -> bool) -> Option<&'a [T]> {
        let span = self.peek_remaining()?;
        if !func(span) {
            None
        } else {
            Some(span)
        }
    }
}

impl<'a, T> Iterator for MultiIterator<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        let item = self.data.get(self.cursor);
        self.cursor += 1;
        item
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), None)
    }

    #[inline]
    fn last(self) -> Option<&'a T> {
        self.data.last()
    }
}

impl<'a, T> ExactSizeIterator for MultiIterator<'a, T> {
    #[inline]
    fn len(&self) -> usize {
        self.data.len() - self.cursor
    }
}

impl<'a, T> FusedIterator for MultiIterator<'a, T> {}

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
/// 
/// let a = [1, 2, 3];
/// let iter = a.multi_iter();
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

        // Ensure `None` is returned when `n` == 0
        let items = iter.peek_n(0);
        assert!(items.is_none());

        // Ensure cursor does not advance & correct items are returned when 0 < `n` <= `iter.len()`
        let items = iter.peek_n(3).unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
        assert_eq!(iter.len(), 3);

        // Ensure `None` is returned when `n` > `self.len()`
        assert!(iter.peek_n(4).is_none());
    }

    #[test]
    fn test_peek_remaining() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let iter = a.multi_iter();

        // Ensure peeking does not advance cursor & returns correct items on non-empty iterator
        let items = iter.peek_remaining().unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
        assert_eq!(iter.len(), 3);

        // Ensure `None` is returned when iterator is empty
        let b: [i32; 0] = [];
        let iter = b.multi_iter().peek_remaining();
        assert!(iter.is_none());
    }

    #[test]
    fn test_next_n() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let mut iter = a.multi_iter();

        // Ensure `None` is returned when `n` == 0
        let items = iter.next_n(0);
        assert!(items.is_none());

        // Ensure `None` is returned & cursor does not advance when `n` > `self.len()`
        let items = iter.next_n(4);
        assert!(items.is_none());
        assert_eq!(iter.len(), 3);

        // Ensure correct items are returned & cursor is advanced when 0 < `n` <= `self.len()`
        let items = iter.next_n(3).unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
        assert_eq!(iter.len(), 0);

        // Ensure `None` is returned when iterator is empty
        let b: [i32; 0] = [];
        let iter = b.multi_iter().next_n(1);
        assert!(iter.is_none());
    }

    #[test]
    fn test_next_n_if_each() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let mut iter = a.multi_iter();

        // Ensure condition succeeding when `n` == 0 returns `None`
        let items = iter.next_n_if_each(0, |_| true);
        assert!(items.is_none());

        // Ensure condition failing on non-empty iterator returns `None` & does not advance cursor
        let items = iter.next_n_if_slice(3, |x| x[0] == 1 && x[1] == 2 && x[2] == 4);
        assert!(items.is_none());
        assert_eq!(iter.len(), 3);

        // Ensure condition succeeding on non-empty iterator returns correct items & advances cursor
        let items = iter.next_n_if_each(3, |x| *x >= 1).unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
        assert_eq!(iter.len(), 0);

        // Ensure condition failing on empty iterator returns `None`
        let items = iter.next_n_if_each(1, |x| *x >= 1);
        assert!(items.is_none());
    }

    #[test]
    fn test_next_n_if_slice() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let mut iter = a.multi_iter();

        // Ensure condition succeeding when `n` == 0 returns `None`
        let items = iter.next_n_if_slice(0, |_| true);
        assert!(items.is_none());

        // Ensure condition failing on non-empty iterator returns `None`
        let items = iter.next_n_if_slice(3, |x| x[0] == 1 && x[1] == 2 && x[2] == 4);
        assert!(items.is_none());
        assert_eq!(iter.len(), 3);

        // Ensure condition succeeding on non-empty iterator returns correct items & advances cursor
        let items = iter
            .next_n_if_slice(3, |x| x[0] == 1 && x[1] == 2 && x[2] == 3)
            .unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);
        assert_eq!(iter.len(), 0);

        // Ensure condition succeeding on empty iterator returns `None`
        let items = iter.next_n_if_slice(1, |_| true);
        assert!(items.is_none());
    }

    #[test]
    fn test_remaining() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];
        let iter = a.multi_iter();

        // Ensure correct items are returned when iterator is not empty
        let items = iter.remaining().unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);

        // Ensure `None` is returned when iterator is empty
        let b: [i32; 0] = [];
        let iter = b.multi_iter().remaining();
        assert!(iter.is_none());
    }

    #[test]
    fn test_remaining_if_each() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];

        // Ensure condition succeeding on non-empty iterator returns correct items
        let items = a.multi_iter().remaining_if_each(|x| *x >= 1).unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);

        // Ensure condition failing on non-empty iterator returns `None`
        let items = a.multi_iter().remaining_if_each(|x| *x > 1);
        assert!(items.is_none());

        // Ensure successful condition on empty iterator returns `None`
        let b: [i32; 0] = [];
        let items = b.multi_iter().remaining_if_each(|_| true);
        assert!(items.is_none());
    }

    #[test]
    fn test_remaining_if_slice() {
        use super::IntoMultiIterator;

        let a = [1, 2, 3];

        // Ensure condition succeeding on non-empty iterator returns correct items
        let items = a
            .multi_iter()
            .remaining_if_slice(|x| x[0] == 1 && x[1] == 2 && x[2] == 3)
            .unwrap();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], 1);
        assert_eq!(items[1], 2);
        assert_eq!(items[2], 3);

        // Ensure condition failing on non-empty iterator returns `None`
        assert!(a
            .multi_iter()
            .remaining_if_slice(|x| { x[0] == 1 && x[1] == 2 && x[2] == 4 })
            .is_none());

        // Ensure successful condition on empty iterator returns `None`
        let b: [i32; 0] = [];
        assert!(b.multi_iter().remaining_if_slice(|_| true).is_none());
    }
}
