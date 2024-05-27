//! Entry API for iterating over and removing elements from a `Vec`.
//!
//! ## Description
//!
//! Sometimes you want to do efficently remove and modify elements of a `Vec` in a slightly more
//! complex way than [`Vec::dedup_by`], [`Vec::retain`], or [`Vec::drain`] enable. This crate aims
//! to target a similar, but more expansive functionality.
//!
//! ## Usage
//!
//! Just import the extension trait and call the new method. The [`EntriesExt::entries`] enables
//! iterating across elements, mutating, removing, and re-inserting as needed. Like
//! [`Vec::dedup_by`] this is done by passing in a function which take an [`Entries`] object and
//! returns anything.
//!
//! ```
//! use vec_entries::EntriesExt;
//!
//! let mut v = vec![1, 2, 3];
//! let c = v.entries(.., |e| {
//!     let a = e.remove().unwrap();      // Remove the `1`
//!     let b = e.remove_back().unwrap(); // Remove the `3`
//!     e.try_insert_outside(0);          // Insert a `0` where we removed the `1`
//!     a + b
//! });
//! assert_eq!(c, 4);
//! assert_eq!(v, [0, 2]);
//! ```
#![no_std]

extern crate alloc;

use core::{
    iter::FusedIterator,
    ops::{Bound, Deref, DerefMut, RangeBounds},
    ptr::{self, drop_in_place},
};

use alloc::vec::Vec;

/// A view into the elements of a [`Vec`]
pub struct Entries<'a, T> {
    read_head: usize,
    write_head: usize,
    read_tail: usize,
    write_tail: usize,
    vec: &'a mut Vec<T>,
}

impl<'a, T> Drop for Entries<'a, T> {
    fn drop(&mut self) {
        self.cleanup();
    }
}

pub struct Entry<'a, 'b, T> {
    entries: &'b mut Entries<'a, T>,
    front: bool,
}

impl<'a, 'b, T> Entry<'a, 'b, T> {
    fn shift_front(self) -> &'a mut T {
        debug_assert!(self.front);

        let e = self.entries;
        let read_ptr = unsafe { e.vec.as_mut_ptr().add(e.read_head) };
        let write_ptr = unsafe { e.vec.as_mut_ptr().add(e.write_head) };

        if e.read_head != e.write_head {
            unsafe {
                ptr::copy_nonoverlapping(read_ptr, write_ptr, 1);
            }
        }

        e.read_head += 1;
        e.write_head += 1;

        unsafe { &mut *write_ptr }
    }

    fn shift_back(self) -> &'a mut T {
        debug_assert!(!self.front);

        let e = self.entries;

        e.read_tail -= 1;
        e.write_tail -= 1;

        let read_ptr = unsafe { e.vec.as_mut_ptr().add(e.read_tail) };
        let write_ptr = unsafe { e.vec.as_mut_ptr().add(e.write_tail) };

        if e.read_tail != e.write_tail {
            unsafe {
                ptr::copy_nonoverlapping(read_ptr, write_ptr, 1);
            }
        }

        unsafe { &mut *write_ptr }
    }

    fn remove_front(self) -> T {
        debug_assert!(self.front);

        let e = self.entries;

        let v = unsafe { ptr::read(e.vec.as_mut_ptr().add(e.read_head)) };
        e.read_head += 1;

        v
    }

    fn remove_back(mut self) -> T {
        debug_assert!(!self.front);

        let e = &mut self.entries;

        e.read_tail -= 1;
        let v = unsafe { ptr::read(e.vec.as_mut_ptr().add(e.read_tail)) };

        v
    }

    /// Shift the the view inward by one, returning a mutable reference to the now
    /// excluded element.
    #[inline]
    pub fn shift(self) -> &'a mut T {
        if self.front {
            self.shift_front()
        } else {
            self.shift_back()
        }
    }

    /// Remove the element from the underlying `Vec`, returning the now removed item.
    #[inline]
    pub fn remove(self) -> T {
        if self.front {
            self.remove_front()
        } else {
            self.remove_back()
        }
    }
}

impl<'a, 'b, T> Deref for Entry<'a, 'b, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        let entries = &self.entries;
        unsafe {
            if self.front {
                entries.vec.get_unchecked(entries.read_head)
            } else {
                entries.vec.get_unchecked(entries.read_tail - 1)
            }
        }
    }
}

impl<'a, 'b, T> DerefMut for Entry<'a, 'b, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let entries = &mut self.entries;
        unsafe {
            if self.front {
                entries.vec.get_unchecked_mut(entries.read_head)
            } else {
                entries.vec.get_unchecked_mut(entries.read_tail - 1)
            }
        }
    }
}

impl<'a, T> Entries<'a, T> {
    fn start(start: Bound<usize>) -> usize {
        match start {
            Bound::Unbounded => 0,
            Bound::Included(v) => v,
            Bound::Excluded(v) => v + 1,
        }
    }

    fn end(vec: &Vec<T>, end: Bound<usize>) -> usize {
        match end {
            Bound::Unbounded => vec.len(),
            Bound::Included(v) => v + 1,
            Bound::Excluded(v) => v,
        }
    }

    fn new(vec: &'a mut Vec<T>, start: Bound<usize>, end: Bound<usize>) -> Self {
        let start = Self::start(start);
        let end = Self::end(vec, end);
        Self {
            read_head: start,
            write_head: start,
            read_tail: end,
            write_tail: end,
            vec,
        }
    }

    fn cleanup(&mut self) {
        let count_head = self.read_tail - self.read_head;
        let count_tail = self.vec.len() - self.write_tail;

        unsafe {
            let src = self.vec.as_ptr().add(self.read_head);
            let dst = self.vec.as_mut_ptr().add(self.write_head);
            ptr::copy(src, dst, count_head);
            let dst = dst.add(count_head);

            let src = self.vec.as_ptr().add(self.write_tail);
            ptr::copy(src, dst, count_tail);
            let dst = dst.add(count_tail);

            let len = dst.offset_from(self.vec.as_ptr()) as usize;
            self.vec.set_len(len);
        }
    }

    /// Get the remaining elements of the view as a mutable slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     assert_eq!(e.remaining(), [0, 1, 2]);
    ///     e.shift();
    ///     assert_eq!(e.remaining(), [1, 2]);
    ///     e.shift();
    ///     assert_eq!(e.remaining(), [2]);
    /// });
    /// ```
    pub fn remaining(&mut self) -> &mut [T] {
        unsafe { self.vec.get_unchecked_mut(self.read_head..self.read_tail) }
    }

    /// Get the number of elements still present in the view.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     assert_eq!(e.remaining_len(), 3);
    ///     e.shift();
    ///     assert_eq!(e.remaining_len(), 2);
    ///     e.shift();
    ///     assert_eq!(e.remaining_len(), 1);
    /// });
    /// ```
    pub const fn remaining_len(&self) -> usize {
        self.read_tail - self.read_head
    }

    /// Get the length of portion of the underlying `Vec` before the view.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     assert_eq!(e.len_before(), 0);
    ///     e.shift();
    ///     assert_eq!(e.len_before(), 1);
    ///     e.shift();
    ///     assert_eq!(e.len_before(), 2);
    /// });
    /// ```
    pub const fn len_before(&self) -> usize {
        self.write_head
    }

    /// Get the length of portion of the underlying `Vec` after the view.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     assert_eq!(e.len_after(), 0);
    ///     e.shift_back();
    ///     assert_eq!(e.len_after(), 1);
    ///     e.shift_back();
    ///     assert_eq!(e.len_after(), 2);
    /// });
    /// ```
    pub fn len_after(&self) -> usize {
        self.vec.len() - self.write_tail
    }

    /// Remove and drop all remaining elements in the view.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2, 3, 4];
    /// v.entries(.., |e| {
    ///     e.shift(); // shift `0` out of view
    ///     e.shift_back(); // shift `4` out of view
    ///     e.clear(); // Drop 1, 2, and 3
    /// });
    /// assert_eq!(v, [0, 4]);
    /// ```
    pub fn clear(&mut self) {
        while self.read_head != self.read_tail {
            unsafe { drop_in_place(self.vec.as_mut_ptr().add(self.read_head)) }
            self.read_head += 1;
        }
    }

    /// Get an entry for the element at the head of the view.
    ///
    /// Returns `None` if the view is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     let f = e.front().unwrap();
    ///     assert_eq!(*f, 0);
    ///     f.shift();
    ///
    ///     let f = e.front().unwrap();
    ///     assert_eq!(*f, 1);
    ///     f.shift();
    ///
    ///     let f = e.front().unwrap();
    ///     assert_eq!(*f, 2);
    ///     f.shift();
    ///
    ///     assert!(e.front().is_none());
    /// });
    /// ```
    #[inline]
    pub fn front<'b>(&'b mut self) -> Option<Entry<'a, 'b, T>> {
        if self.read_head == self.read_tail {
            None
        } else {
            Some(Entry {
                entries: self,
                front: true,
            })
        }
    }

    /// Get an entry for the element at the tail of the view.
    ///
    /// Returns `None` if the view is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     let b = e.back().unwrap();
    ///     assert_eq!(*b, 2);
    ///     b.shift();
    ///
    ///     let b = e.back().unwrap();
    ///     assert_eq!(*b, 1);
    ///     b.shift();
    ///
    ///     let b = e.back().unwrap();
    ///     assert_eq!(*b, 0);
    ///     b.shift();
    ///
    ///     assert!(e.back().is_none());
    /// });
    /// ```
    #[inline]
    pub fn back<'b>(&'b mut self) -> Option<Entry<'a, 'b, T>> {
        if self.read_head == self.read_tail {
            None
        } else {
            Some(Entry {
                entries: self,
                front: false,
            })
        }
    }

    /// Shift the head of the view inward by one, returning a mutable reference to the now
    /// excluded item.
    ///
    /// Returns `None` if the view is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     assert_eq!(e.shift(), Some(&mut 0));
    ///     assert_eq!(e.shift(), Some(&mut 1));
    ///     assert_eq!(e.shift(), Some(&mut 2));
    ///     assert_eq!(e.shift(), None);
    /// });
    /// ```
    #[inline]
    pub fn shift(&mut self) -> Option<&'a mut T> {
        self.front().map(Entry::shift_front)
    }

    /// Shift the tail of the view inward by one, returning a mutable reference to the now
    /// excluded item.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     assert_eq!(e.shift_back(), Some(&mut 2));
    ///     assert_eq!(e.shift_back(), Some(&mut 1));
    ///     assert_eq!(e.shift_back(), Some(&mut 0));
    ///     assert_eq!(e.shift_back(), None);
    /// });
    /// ```
    #[inline]
    pub fn shift_back(&mut self) -> Option<&'a mut T> {
        self.back().map(Entry::shift_back)
    }

    /// Remove the item at the head of the view from the underlying `Vec`, returning the now
    /// removed item.
    ///
    /// Returns `None` if the view is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     e.shift();
    ///     assert_eq!(e.remove(), Some(1));
    /// });
    /// assert_eq!(v, [0, 2]);
    /// ```
    #[inline]
    pub fn remove(&mut self) -> Option<T> {
        self.front().map(Entry::remove_front)
    }

    /// Remove the item at the tail of the view from the underlying `Vec`, returning the now
    /// removed item.
    ///
    /// Returns `None` if the view is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     assert_eq!(e.remove_back(), Some(2));
    /// });
    /// assert_eq!(v, [0, 1]);
    /// ```
    pub fn remove_back(&mut self) -> Option<T> {
        self.back().map(Entry::remove_back)
    }

    /// Try to insert an item into the underlying `Vec`, just before the head of the view.
    /// The view is then shifted include the added item.
    ///
    /// Returns `Err` if the there is no empty space for the insert to occur.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     // Can't insert if you didn't remove
    ///     assert_eq!(e.try_insert_inside(5), Err(5));
    ///
    ///     assert_eq!(e.remove(), Some(0));
    ///     assert_eq!(e.remaining(), [1, 2]);
    ///     assert_eq!(e.try_insert_inside(5), Ok(&mut 5));
    ///     assert_eq!(e.remaining(), [5, 1, 2]);
    /// });
    /// assert_eq!(v, [5, 1, 2]);
    /// ```
    pub fn try_insert_inside(&mut self, v: T) -> Result<&mut T, T> {
        if self.read_head == self.write_head {
            return Err(v);
        }

        self.read_head -= 1;
        let v = unsafe {
            let write_ptr = self.vec.as_mut_ptr().add(self.read_head);
            ptr::write(write_ptr, v);
            self.vec.get_unchecked_mut(self.read_head)
        };

        Ok(v)
    }

    /// Try to insert an item into the underlying `Vec`, just after the tail of the view.
    /// The view is then shifted include the added item.
    ///
    /// Returns `Err` if the there is no empty space for the insert to occur.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     // Can't insert if you didn't remove
    ///     assert_eq!(e.try_insert_inside_back(5), Err(5));
    ///
    ///     assert_eq!(e.remove_back(), Some(2));
    ///     assert_eq!(e.remaining(), [0, 1]);
    ///     assert_eq!(e.try_insert_inside_back(5), Ok(&mut 5));
    ///     assert_eq!(e.remaining(), [0, 1, 5]);
    /// });
    /// assert_eq!(v, [0, 1, 5]);
    /// ```
    pub fn try_insert_inside_back(&mut self, v: T) -> Result<&mut T, T> {
        if self.read_tail == self.write_tail {
            return Err(v);
        }

        let v = unsafe {
            let write_ptr = self.vec.as_mut_ptr().add(self.read_tail);
            ptr::write(write_ptr, v);
            self.vec.get_unchecked_mut(self.read_tail)
        };
        self.read_tail += 1;

        Ok(v)
    }

    /// Try to insert an item into the underlying `Vec`, just before the head of the view.
    ///
    /// Returns `Err` if the there is no empty space for the insert to occur.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     // Can't insert if you didn't remove
    ///     assert_eq!(e.try_insert_outside(5), Err(5));
    ///
    ///     assert_eq!(e.remove(), Some(0));
    ///     assert_eq!(e.remaining(), [1, 2]);
    ///     assert_eq!(e.try_insert_outside(5), Ok(&mut 5));
    ///     assert_eq!(e.remaining(), [1, 2]);
    /// });
    /// assert_eq!(v, [5, 1, 2]);
    /// ```
    pub fn try_insert_outside(&mut self, v: T) -> Result<&'a mut T, T> {
        if self.read_head == self.write_head {
            return Err(v);
        }

        let v = unsafe {
            let write_ptr = self.vec.as_mut_ptr().add(self.write_head);
            ptr::write(write_ptr, v);
            &mut *write_ptr
        };
        self.write_head += 1;

        Ok(v)
    }

    /// Try to insert an item into the underlying `Vec`, just after the tail of the view.
    ///
    /// Returns `Err` if the there is no empty space for the insert to occur.
    ///
    /// # Examples
    ///
    /// ```
    /// use vec_entries::EntriesExt;
    ///
    /// let mut v = vec![0, 1, 2];
    /// v.entries(.., |e| {
    ///     // Can't insert if you didn't remove
    ///     assert_eq!(e.try_insert_outside_back(5), Err(5));
    ///
    ///     assert_eq!(e.remove_back(), Some(2));
    ///     assert_eq!(e.remaining(), [0, 1]);
    ///     assert_eq!(e.try_insert_outside_back(5), Ok(&mut 5));
    ///     assert_eq!(e.remaining(), [0, 1]);
    /// });
    /// assert_eq!(v, [0, 1, 5]);
    /// ```
    pub fn try_insert_outside_back(&mut self, v: T) -> Result<&'a mut T, T> {
        if self.read_tail == self.write_tail {
            return Err(v);
        }

        self.write_tail -= 1;
        let v = unsafe {
            let write_ptr = self.vec.as_mut_ptr().add(self.write_tail);
            ptr::write(write_ptr, v);
            &mut *write_ptr
        };

        Ok(v)
    }

    /// Get an iterator which gives mutable references to entries.
    pub fn shift_iter<'b>(&'b mut self) -> ShiftIter<'a, 'b, T> {
        ShiftIter { entries: self }
    }

    /// Get an iterator which removes entries.
    pub fn remove_iter<'b>(&'b mut self) -> RemoveIter<'a, 'b, T> {
        RemoveIter { entries: self }
    }
}

/// An iterator which utilizes [`Entries::shift`] and [`Entries::shift_back`] to traverse entries.
pub struct ShiftIter<'a, 'b, T> {
    entries: &'b mut Entries<'a, T>,
}

impl<'a, 'b, T> Iterator for ShiftIter<'a, 'b, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<Self::Item> {
        self.entries.shift()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, 'b, T> DoubleEndedIterator for ShiftIter<'a, 'b, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.entries.shift_back()
    }
}

impl<'a, 'b, T> ExactSizeIterator for ShiftIter<'a, 'b, T> {
    fn len(&self) -> usize {
        self.entries.read_tail - self.entries.read_head
    }
}

impl<'a, 'b, T> FusedIterator for ShiftIter<'a, 'b, T> {}

/// An iterator which utilizes [`Entries::remove`] and [`Entries::remove_back`] to traverse
/// entries.
pub struct RemoveIter<'a, 'b, T> {
    entries: &'b mut Entries<'a, T>,
}

impl<'a, 'b, T> Iterator for RemoveIter<'a, 'b, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.entries.remove()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, 'b, T> DoubleEndedIterator for RemoveIter<'a, 'b, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.entries.remove_back()
    }
}

impl<'a, 'b, T> ExactSizeIterator for RemoveIter<'a, 'b, T> {
    fn len(&self) -> usize {
        self.entries.read_tail - self.entries.read_head
    }
}

impl<'a, 'b, T> FusedIterator for RemoveIter<'a, 'b, T> {}

// An extension trait to add an `entries` method.
pub trait EntriesExt {
    /// The element type of the underlying container.
    type T;

    /// The entries type
    type Entries<'a, T: 'a>;

    /// Inspect the entries of a container within a specific `range`.
    fn entries<'a, R, F, Ret>(&'a mut self, range: R, f: F) -> Ret
    where
        R: RangeBounds<usize>,
        F: FnOnce(&mut Self::Entries<'a, Self::T>) -> Ret;
}

impl<T> EntriesExt for Vec<T> {
    type T = T;
    type Entries<'a, V: 'a> = Entries<'a, V>;

    fn entries<'a, R, F, Ret>(&'a mut self, range: R, f: F) -> Ret
    where
        R: RangeBounds<usize>,
        F: FnOnce(&mut Self::Entries<'a, Self::T>) -> Ret,
    {
        f(&mut Entries::new(
            self,
            range.start_bound().cloned(),
            range.end_bound().cloned(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;

    #[test]
    fn nothing() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
        });
        assert_eq!(foo, [1, 2, 3, 4]);
    }

    #[test]
    fn skip() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.shift(), Some(&mut 1));
            assert_eq!(e.remaining(), [2, 3, 4]);
        });
        assert_eq!(foo, [1, 2, 3, 4]);
    }

    #[test]
    fn skip_back() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.shift_back(), Some(&mut 4));
            assert_eq!(e.remaining(), [1, 2, 3]);
        });
        assert_eq!(foo, [1, 2, 3, 4]);
    }

    #[test]
    fn remove() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.remove(), Some(1));
            assert_eq!(e.remaining(), [2, 3, 4]);
        });
        assert_eq!(foo, [2, 3, 4]);
    }

    #[test]
    fn remove_back() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.remove_back(), Some(4));
            assert_eq!(e.remaining(), [1, 2, 3]);
        });
        assert_eq!(foo, [1, 2, 3]);
    }

    #[test]
    fn skip_remove() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.shift(), Some(&mut 1));
            assert_eq!(e.remove(), Some(2));
        });
        assert_eq!(foo, [1, 3, 4]);
    }

    #[test]
    fn skip_back_remove() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.shift_back(), Some(&mut 4));
            assert_eq!(e.remove(), Some(1));
        });
        assert_eq!(foo, [2, 3, 4]);
    }

    #[test]
    fn skip_remove_back() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.shift(), Some(&mut 1));
            assert_eq!(e.remove_back(), Some(4));
        });
        assert_eq!(foo, [1, 2, 3]);
    }

    #[test]
    fn skip_back_remove_back() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.shift_back(), Some(&mut 4));
            assert_eq!(e.remove_back(), Some(3));
        });
        assert_eq!(foo, [1, 2, 4]);
    }

    #[test]
    fn skip_iter() {
        let mut foo = vec![1, 2, 3, 4];
        foo.entries(.., |e| {
            assert_eq!(e.remaining(), [1, 2, 3, 4]);
            assert_eq!(e.shift_iter().next(), Some(&mut 1));
            assert_eq!(e.remaining(), [2, 3, 4]);
        });
        assert_eq!(foo, [1, 2, 3, 4]);
    }
}
