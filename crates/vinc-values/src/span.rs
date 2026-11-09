//! Byte spans and bounded span lists.
//!
//! [`RangeList`] is a fixed-capacity, ordered list of `(offset, length)` spans: the fetch queue, a provider's assigned
//! work and a request's ranges. Invariant: it never grows past its capacity. A push onto a full list widens the last
//! span over the gap instead of failing, which can only ask for bytes twice, never skip a byte: coverage never
//! shrinks. The helpers [`holes`] and [`align`] are the range arithmetic of the fetch (what is missing from the
//! verified set, and the rounding of requests to whole groups).

use crate::knobs::GROUP;
use crate::store::ValueStore;

/// A byte span of a value.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Span {
    /// The first byte.
    pub off: u64,
    /// The number of bytes.
    pub len: u64,
}

impl Span {
    /// The offset just past the span.
    pub const fn end(&self) -> u64 {
        self.off.saturating_add(self.len)
    }
}

/// The parts of `span` that the store has not verified, in order; each is passed to `emit`.
pub fn holes<St: ValueStore + ?Sized>(st: &St, root: &[u8; 32], span: Span, mut emit: impl FnMut(Span)) {
    let end = span.end();
    let mut cur = span.off;
    while cur < end {
        match st.verified_from(root, cur) {
            Some(v) if v.start <= cur => cur = v.end,
            Some(v) if v.start < end => {
                emit(Span {
                    off: cur,
                    len: v.start - cur,
                });
                cur = v.end;
            }
            _ => {
                emit(Span {
                    off: cur,
                    len: end - cur,
                });
                return;
            }
        }
    }
}

/// Round `span` out to whole groups, clamped to a value of `total` bytes; `None` if nothing is left (an empty span
/// asks for no bytes, whatever its offset).
pub fn align(span: Span, total: u64) -> Option<Span> {
    let a = span.off / GROUP * GROUP;
    let b = span.end().div_ceil(GROUP).saturating_mul(GROUP).min(total);
    b.checked_sub(a)
        .filter(|&len| span.len > 0 && len > 0)
        .map(|len| Span { off: a, len })
}

/// A bounded, ordered list of up to `N` spans.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangeList<const N: usize> {
    items: [Span; N],
    len: usize,
}

impl<const N: usize> Default for RangeList<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> RangeList<N> {
    /// An empty list.
    pub const fn new() -> Self {
        Self {
            items: [Span { off: 0, len: 0 }; N],
            len: 0,
        }
    }

    /// The spans in order.
    pub fn as_slice(&self) -> &[Span] {
        self.items.get(..self.len).unwrap_or_default()
    }

    /// Whether the list is empty.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The number of spans.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// The bytes the spans cover in all.
    pub fn total(&self) -> u64 {
        self.as_slice().iter().fold(0, |a, s| a.saturating_add(s.len))
    }

    /// Remove every span.
    pub const fn clear(&mut self) {
        self.len = 0;
    }

    /// Append `s`, merging with the last span when `s` starts inside or right after it; a full list widens its last
    /// span over `s`. Spans need not arrive in order.
    // vertexia: a full list widens the last span (asks twice, never skips); a fragmentation-proof queue would need an
    // interval tree, not worth it at 64 spans.
    pub fn push(&mut self, s: Span) {
        if s.len == 0 {
            return;
        }
        if let Some(last) = self.len.checked_sub(1).and_then(|i| self.items.get_mut(i)) {
            let touches = s.off >= last.off && s.off <= last.end();
            if touches || self.len == N {
                let off = last.off.min(s.off);
                last.len = last.end().max(s.end()) - off;
                last.off = off;
                return;
            }
        }
        if let Some(slot) = self.items.get_mut(self.len) {
            *slot = s;
            self.len += 1;
        }
    }

    /// Append the parts of `s` that no span of the list covers yet, in order. Bytes asked twice are fetched twice, so
    /// a caller that cannot promise disjoint input uses this instead of [`RangeList::push`].
    pub fn push_new(&mut self, s: Span) {
        let (mut cur, end) = (s.off, s.end());
        while cur < end {
            let covered = self
                .as_slice()
                .iter()
                .filter(|e| e.off <= cur && cur < e.end())
                .map(Span::end)
                .max();
            if let Some(to) = covered {
                cur = to;
                continue;
            }
            let next = self
                .as_slice()
                .iter()
                .map(|e| e.off)
                .filter(|&o| o > cur && o < end)
                .min()
                .unwrap_or(end);
            self.push(Span {
                off: cur,
                len: next - cur,
            });
            cur = next;
        }
    }

    /// Insert `s` at the front; a full list widens its first span back over `s`.
    pub fn push_front(&mut self, s: Span) {
        if s.len == 0 {
            return;
        }
        if self.len == N {
            if let Some(first) = self.items.first_mut() {
                let end = first.end().max(s.end());
                first.off = first.off.min(s.off);
                first.len = end - first.off;
            }
            return;
        }
        self.items.copy_within(0..self.len, 1);
        if let Some(slot) = self.items.first_mut() {
            *slot = s;
            self.len += 1;
        }
    }

    /// Remove and return the first span.
    pub fn pop_front(&mut self) -> Option<Span> {
        let first = *self.as_slice().first()?;
        self.items.copy_within(1..self.len, 0);
        self.len -= 1;
        Some(first)
    }

    /// Keep, of every span, only the parts `st` has not verified for `root`.
    pub fn retain_missing<St: ValueStore + ?Sized>(&mut self, st: &St, root: &[u8; 32]) {
        let mut out = Self::new();
        for s in self.as_slice() {
            holes(st, root, *s, |h| out.push(h));
        }
        *self = out;
    }

    /// The parts of this list that `st` has not verified for `root`.
    #[must_use]
    pub fn missing<St: ValueStore + ?Sized>(&self, st: &St, root: &[u8; 32]) -> Self {
        let mut out = self.clone();
        out.retain_missing(st, root);
        out
    }

    /// Append every span of `other`.
    pub fn extend<const M: usize>(&mut self, other: &RangeList<M>) {
        for s in other.as_slice() {
            self.push(*s);
        }
    }

    /// Split this list into `k` contiguous shares of whole groups (at least one group each, the last takes the rest).
    /// `k` is clamped to `1..=S`.
    pub fn split<const S: usize>(&self, k: usize) -> [Self; S] {
        let k = k.clamp(1, S.max(1));
        let share = (self.total() / u64::try_from(k).unwrap_or(1) / GROUP * GROUP).max(GROUP);
        let mut out: [Self; S] = core::array::from_fn(|_| Self::new());
        let (mut idx, mut acc) = (0usize, 0u64);
        for s in self.as_slice() {
            let (mut cur, end) = (s.off, s.end());
            while cur < end {
                let last = idx + 1 >= k;
                let room = if last {
                    end - cur
                } else {
                    share.saturating_sub(acc).max(1)
                };
                let take = room.min(end - cur);
                if let Some(l) = out.get_mut(idx) {
                    l.push(Span { off: cur, len: take });
                }
                cur += take;
                acc += take;
                if acc >= share && !last {
                    idx += 1;
                    acc = 0;
                }
            }
        }
        out
    }
}
