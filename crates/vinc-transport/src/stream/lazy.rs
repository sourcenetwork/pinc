//! A fixed table of `N` entries that is written only as far as it is used.
//!
//! With the `alloc` feature the room for all `N` entries is reserved when the table is made, and an entry is written the
//! first time it is taken for writing; the memory of entries never used is never touched, so a large table costs what
//! its busiest moment used, and nothing is allocated after it is made. An entry not written yet reads as a blank one.
//! Without `alloc` it is a plain array with every entry written at once.
//!
//! Invariants: the table always reads as `N` entries; an entry not written reads exactly as `T::BLANK`; with `alloc`
//! the reserved room never grows, so no write allocates.

/// A value an empty table entry holds.
pub(crate) trait Blank {
    /// The empty entry.
    const BLANK: Self;
}

/// `N` entries of `T`; see the module docs.
#[derive(Debug, Clone)]
pub(crate) struct Lazy<T, const N: usize> {
    /// The entries written so far, a prefix of the table; its capacity is `N` from the start.
    #[cfg(feature = "alloc")]
    written: alloc::vec::Vec<T>,
    /// What every entry beyond `written` reads as.
    #[cfg(feature = "alloc")]
    blank: T,
    #[cfg(not(feature = "alloc"))]
    all: [T; N],
}

#[cfg(feature = "alloc")]
impl<T: Blank, const N: usize> Lazy<T, N> {
    /// A table of blank entries.
    pub(crate) fn new() -> Self {
        Self {
            written: alloc::vec::Vec::with_capacity(N),
            blank: T::BLANK,
        }
    }

    /// Entry `i`.
    pub(crate) fn get(&self, i: usize) -> Option<&T> {
        (i < N).then(|| self.written.get(i).unwrap_or(&self.blank))
    }

    /// Entry `i`, writable: it and every entry before it are written now if they were not yet.
    pub(crate) fn get_mut(&mut self, i: usize) -> Option<&mut T> {
        if i >= N {
            return None;
        }
        // Within the capacity reserved at the start: no push reallocates.
        while self.written.len() <= i {
            self.written.push(T::BLANK);
        }
        self.written.get_mut(i)
    }

    /// Entry `i` if it was ever written: an entry that still reads as blank is not written by this call.
    pub(crate) fn written_mut(&mut self, i: usize) -> Option<&mut T> {
        self.written.get_mut(i)
    }

    /// Every entry, in order: `N` of them.
    #[cfg(any(test, feature = "trace"))]
    pub(crate) fn iter(&self) -> impl Iterator<Item = &T> {
        self.written
            .iter()
            .chain(core::iter::repeat_n(&self.blank, N - self.written.len()))
    }

    /// The entries ever written, in order; every other entry is blank.
    pub(crate) fn written(&self) -> &[T] {
        &self.written
    }

    /// The entries ever written, in order; every other entry is blank.
    pub(crate) fn written_iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.written.iter_mut()
    }

    /// The first `n` entries as a slice, if all of them were written.
    pub(crate) fn prefix_mut(&mut self, n: usize) -> Option<&mut [T]> {
        self.written.get_mut(..n)
    }

    /// Make every entry blank again, keeping the reserved room.
    pub(crate) fn clear(&mut self) {
        self.written.clear();
    }
}

#[cfg(not(feature = "alloc"))]
impl<T: Blank, const N: usize> Lazy<T, N> {
    /// A table of blank entries.
    pub(crate) const fn new() -> Self {
        Self {
            all: [const { T::BLANK }; N],
        }
    }

    /// Entry `i`.
    pub(crate) fn get(&self, i: usize) -> Option<&T> {
        self.all.get(i)
    }

    /// Entry `i`, writable.
    pub(crate) fn get_mut(&mut self, i: usize) -> Option<&mut T> {
        self.all.get_mut(i)
    }

    /// Entry `i`, writable.
    pub(crate) fn written_mut(&mut self, i: usize) -> Option<&mut T> {
        self.all.get_mut(i)
    }

    /// Every entry, in order.
    #[cfg(any(test, feature = "trace"))]
    pub(crate) fn iter(&self) -> impl Iterator<Item = &T> {
        self.all.iter()
    }

    /// Every entry, in order.
    pub(crate) fn written(&self) -> &[T] {
        &self.all
    }

    /// Every entry, in order.
    pub(crate) fn written_iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.all.iter_mut()
    }

    /// The first `n` entries as a slice.
    pub(crate) fn prefix_mut(&mut self, n: usize) -> Option<&mut [T]> {
        self.all.get_mut(..n)
    }

    /// Make every entry blank again.
    pub(crate) fn clear(&mut self) {
        for e in &mut self.all {
            *e = T::BLANK;
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    struct E(u32);

    impl Blank for E {
        const BLANK: Self = Self(7);
    }

    #[test]
    fn an_entry_not_written_reads_blank_and_a_write_keeps_the_rest_blank() {
        let mut t = Lazy::<E, 5>::new();
        assert_eq!(t.get(3), Some(&E(7)));
        assert_eq!(t.get(5), None);
        assert!(t.written_mut(2).is_none_or(|e| *e == E(7)));
        t.get_mut(2).unwrap().0 = 1;
        assert!(t.iter().copied().eq([E(7), E(7), E(1), E(7), E(7)]));
        assert!(t.get_mut(5).is_none());
        t.clear();
        assert_eq!(t.iter().count(), 5);
        assert!(t.iter().all(|e| *e == E(7)));
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn writing_every_entry_never_grows_the_reserved_room() {
        let mut t = Lazy::<E, 64>::new();
        let room = (t.written.capacity(), t.written.as_ptr());
        assert!(room.0 >= 64);
        t.get_mut(63).unwrap().0 = 2;
        assert_eq!(t.written.len(), 64);
        t.clear();
        t.get_mut(10).unwrap().0 = 3;
        assert_eq!((t.written.capacity(), t.written.as_ptr()), room);
        assert!(
            t.written_mut(11).is_none(),
            "an entry past the written prefix is not written by asking"
        );
        assert_eq!(t.get(11), Some(&E(7)));
    }
}
