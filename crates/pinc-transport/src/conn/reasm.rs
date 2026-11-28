//! Reassembly of one handshake message from fragments that arrive in any order, any number of times.
//!
//! The message is `total` bytes. The bytes that arrived are kept as at most [`RUNS`] disjoint, sorted runs
//! `[start, end)`, with runs that touch merged into one. A fragment that needs a ninth run is dropped and the
//! retransmission brings it again. A fragment that disagrees with what is held (a message of another length while one
//! is under way, or other bytes at an offset a run already covers) is refused as a [`Added::Conflict`] and changes
//! nothing: the first bytes written to an offset stay, so a forged fragment can neither erase nor overwrite the
//! genuine ones, and a caller that wants both messages keeps a second reassembly for the fragment.
//!
//! Invariants: the runs are sorted, disjoint, non-adjacent and non-empty, every run lies inside `[0, total)`, and
//! the bytes of the buffer inside a run are the bytes of the first fragments received there; the message is complete
//! exactly when one run covers `[0, total)`, and `total` is at most [`MAX_MESSAGE_LEN`].

use pinc_security::message::MAX_MESSAGE_LEN;

/// The most disjoint runs of one message the receiver tracks (a message is a handful of datagrams).
pub(crate) const RUNS: usize = 8;

/// What [`Reassembly::add`] did with a fragment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Added {
    /// The fragment was kept, dropped for want of a free run, or ignored as malformed: the message is not complete.
    Part,
    /// The message is complete: its length. A fresh message starts.
    Whole(usize),
    /// The fragment disagrees with what is held; nothing changed.
    Conflict,
}

/// The runs received of the message being assembled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Reassembly {
    runs: [(usize, usize); RUNS],
    len: usize,
    total: usize,
}

impl Default for Reassembly {
    fn default() -> Self {
        Self::new()
    }
}

impl Reassembly {
    /// Nothing received.
    pub(crate) const fn new() -> Self {
        Self {
            runs: [(0, 0); RUNS],
            len: 0,
            total: 0,
        }
    }

    /// Forget everything received.
    pub(crate) fn clear(&mut self) {
        *self = Self::new();
    }

    /// Whether a fragment of a message was kept and the message is not complete yet.
    pub(crate) const fn busy(&self) -> bool {
        self.len > 0
    }

    /// How many bytes of the message being assembled are in.
    pub(crate) fn covered(&self) -> usize {
        self.runs.iter().take(self.len).map(|&(s, e)| e.saturating_sub(s)).sum()
    }

    /// The length of the message being assembled, 0 for none.
    pub(crate) const fn total(&self) -> usize {
        self.total
    }

    /// Keep `data`, which starts at `off` of a message of `total` bytes, in `buf` (the message buffer, if there is
    /// one). Returns the length of the message once every byte is in, and starts a fresh message then; a fragment
    /// that disagrees with what is held is refused and changes nothing (an O(fragment) compare with the buffer).
    pub(crate) fn add(&mut self, buf: Option<&mut [u8]>, total: usize, off: usize, data: &[u8]) -> Added {
        self.try_add(buf, total, off, data).unwrap_or(Added::Part)
    }

    fn try_add(&mut self, buf: Option<&mut [u8]>, total: usize, off: usize, data: &[u8]) -> Option<Added> {
        if total == 0 || total > MAX_MESSAGE_LEN {
            return None;
        }
        if total != self.total {
            if self.len > 0 {
                return Some(Added::Conflict);
            }
            self.total = total;
        }
        let end = off.checked_add(data.len())?.min(total);
        let data = data.get(..end.checked_sub(off)?)?;
        if data.is_empty() {
            return None;
        }
        let buf = buf?;
        let disagrees = self.runs.iter().take(self.len).any(|&(s, e)| {
            let (a, b) = (s.max(off), e.min(end));
            a < b && buf.get(a..b) != data.get(a - off..b - off)
        });
        if disagrees {
            return Some(Added::Conflict);
        }
        // Merge the new run into the sorted, disjoint runs; with no free slot the fragment is dropped and the
        // retransmission brings it again.
        let (mut lo, mut hi) = (off, end);
        let mut keep = [(0usize, 0usize); RUNS];
        let mut n = 0;
        for &(s, e) in self.runs.iter().take(self.len) {
            if e < lo || s > hi {
                *keep.get_mut(n)? = (s, e);
                n += 1;
            } else {
                lo = lo.min(s);
                hi = hi.max(e);
            }
        }
        if n == RUNS {
            return None;
        }
        buf.get_mut(off..end)?.copy_from_slice(data);
        *keep.get_mut(n)? = (lo, hi);
        n += 1;
        keep.get_mut(..n)?.sort_unstable();
        self.runs = keep;
        self.len = n;
        if n == 1 && lo == 0 && hi == total {
            self.total = 0;
            self.len = 0;
            return Some(Added::Whole(total));
        }
        None
    }

    /// The runs and the message length, for trace validation.
    #[cfg(feature = "trace")]
    pub(crate) fn trace_view(&self) -> trace::ReasmView {
        trace::ReasmView {
            runs: self.runs.iter().take(self.len).copied().collect(),
            total: self.total,
        }
    }
}

/// Test-only driver of the reassembly, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
pub(super) mod trace {
    use alloc::vec::Vec;

    use pinc_security::message::MAX_MESSAGE_LEN;

    use super::{Added, RUNS, Reassembly};

    /// The state of a reassembly: the runs, the message length being assembled.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct ReasmView {
        /// The runs `[start, end)`, lowest first.
        pub runs: Vec<(usize, usize)>,
        /// The message length being assembled, 0 for none.
        pub total: usize,
    }

    /// What the handshake did with the body of one Handshake packet: the state of the reassembly before and after,
    /// what `on_fragment` returned, and the bytes of the message buffer (as many as the message being assembled, or
    /// the message just completed, is long).
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct FragmentView {
        /// The reassembly before the call.
        pub before: ReasmView,
        /// The reassembly after the call.
        pub after: ReasmView,
        /// The length of the message, if the fragment completed it.
        pub ret: Option<usize>,
        /// The first bytes of the message buffer.
        pub message: Vec<u8>,
    }

    /// A reassembly with its own message buffer.
    #[derive(Debug)]
    pub struct ReasmProbe {
        r: Reassembly,
        buf: Vec<u8>,
    }

    impl Default for ReasmProbe {
        fn default() -> Self {
            Self::new()
        }
    }

    impl ReasmProbe {
        /// An empty reassembly and a zeroed buffer of the largest message.
        pub fn new() -> Self {
            Self {
                r: Reassembly::new(),
                buf: alloc::vec![0; MAX_MESSAGE_LEN],
            }
        }

        /// The runs a message may have at most.
        pub const RUNS: usize = RUNS;

        /// The largest message.
        pub const MAX_MESSAGE: usize = MAX_MESSAGE_LEN;

        /// Hand one fragment to the reassembly; the length of the message if it is complete.
        pub fn add(&mut self, total: usize, off: usize, data: &[u8]) -> Option<usize> {
            match self.r.add(Some(&mut self.buf), total, off, data) {
                Added::Whole(n) => Some(n),
                Added::Part | Added::Conflict => None,
            }
        }

        /// The bytes of the message buffer.
        pub fn buffer(&self) -> &[u8] {
            &self.buf
        }

        /// The state.
        pub fn view(&self) -> ReasmView {
            ReasmView {
                runs: self.r.runs.iter().take(self.r.len).copied().collect(),
                total: self.r.total,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Added, Reassembly};

    fn buf() -> [u8; 64] {
        [0; 64]
    }

    #[test]
    fn a_fragment_of_another_total_is_refused_and_changes_nothing() {
        let (mut r, mut b) = (Reassembly::new(), buf());
        assert_eq!(r.add(Some(&mut b), 10, 0, &[1; 4]), Added::Part);
        let (before, bytes) = (r, b);
        assert_eq!(r.add(Some(&mut b), 12, 4, &[2; 4]), Added::Conflict);
        assert!(r == before && b == bytes);
    }

    #[test]
    fn different_overlap_bytes_are_refused_and_equal_ones_kept() {
        let (mut r, mut b) = (Reassembly::new(), buf());
        assert_eq!(r.add(Some(&mut b), 10, 0, &[1, 2, 3, 4]), Added::Part);
        let (before, bytes) = (r, b);
        assert_eq!(r.add(Some(&mut b), 10, 2, &[9, 4, 5]), Added::Conflict);
        assert!(r == before && b == bytes);
        assert_eq!(r.add(Some(&mut b), 10, 2, &[3, 4, 5, 6]), Added::Part);
        assert_eq!(r.add(Some(&mut b), 10, 6, &[7, 8, 9, 10]), Added::Whole(10));
        assert_eq!(b.get(..10), Some(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10][..]));
    }

    #[test]
    fn a_complete_message_starts_a_fresh_one() {
        let (mut r, mut b) = (Reassembly::new(), buf());
        assert_eq!(r.add(Some(&mut b), 4, 0, &[1; 4]), Added::Whole(4));
        assert_eq!(r.add(Some(&mut b), 6, 0, &[2; 6]), Added::Whole(6));
    }
}
