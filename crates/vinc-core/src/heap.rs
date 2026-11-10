//! The deadline heap: one indexed binary min-heap over every connection, so the next timer is a peek and a change is
//! logarithmic.
//!
//! Each of the `N` ids holds at most one deadline. Setting an id's deadline moves it within the heap in place, so no
//! stale entry ever accumulates and the heap never holds more than `N` items. Ties break on the lower id, which makes
//! the order of firing deterministic.
//!
//! Invariants: `pos[id]` names the heap index of `id` or is `NONE`; `heap[pos[id]] == id`; for every heap index `i`
//! the key of `heap[i]` is not less than the key of its parent.

use crate::store::{Store, filled, store_fn};

const NONE: u32 = u32::MAX;

/// An indexed min-heap of `(deadline, id)` pairs for ids below `N`.
pub struct DeadlineHeap<const N: usize> {
    heap: Store<u32, N>,
    pos: Store<u32, N>,
    at: Store<u64, N>,
    len: usize,
}

impl<const N: usize> core::fmt::Debug for DeadlineHeap<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("DeadlineHeap")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

impl<const N: usize> DeadlineHeap<N> {
    store_fn! {
    /// An empty heap.
    pub fn new() -> Self {
        const { assert!(N < NONE as usize) };
        Self {
            heap: filled(0),
            pos: filled(NONE),
            at: filled(0),
            len: 0,
        }
    }
    }

    /// How many ids have a deadline.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether no id has a deadline.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn key(&self, heap_index: usize) -> (u64, u32) {
        let id = self.heap.get(heap_index).copied().unwrap_or(0);
        (self.at.get(id as usize).copied().unwrap_or(u64::MAX), id)
    }

    fn put(&mut self, heap_index: usize, id: u32) {
        if let Some(h) = self.heap.get_mut(heap_index) {
            *h = id;
        }
        if let Some(p) = self.pos.get_mut(id as usize) {
            *p = heap_index as u32;
        }
    }

    fn up(&mut self, mut i: usize) {
        let id = self.heap.get(i).copied().unwrap_or(0);
        let k = self.key(i);
        while i > 0 {
            let parent = (i - 1) / 2;
            if self.key(parent) <= k {
                break;
            }
            let p = self.heap.get(parent).copied().unwrap_or(0);
            self.put(i, p);
            i = parent;
        }
        self.put(i, id);
    }

    fn down(&mut self, mut i: usize) {
        let id = self.heap.get(i).copied().unwrap_or(0);
        let k = self.key(i);
        loop {
            let l = 2 * i + 1;
            if l >= self.len {
                break;
            }
            let r = l + 1;
            let c = if r < self.len && self.key(r) < self.key(l) {
                r
            } else {
                l
            };
            if self.key(c) >= k {
                break;
            }
            let ch = self.heap.get(c).copied().unwrap_or(0);
            self.put(i, ch);
            i = c;
        }
        self.put(i, id);
    }

    /// Give `id` the deadline `at`, or remove its deadline with `None`. An id outside `0..N` is ignored.
    pub fn set(&mut self, id: usize, at: Option<u64>) {
        let Some(p) = self.pos.get(id).copied() else { return };
        let uid = id as u32;
        match (p != NONE, at) {
            (false, Some(t)) => {
                if let Some(a) = self.at.get_mut(id) {
                    *a = t;
                }
                let i = self.len;
                self.len += 1;
                self.put(i, uid);
                self.up(i);
            }
            (true, Some(t)) => {
                let old = self.at.get(id).copied().unwrap_or(t);
                if let Some(a) = self.at.get_mut(id) {
                    *a = t;
                }
                if t < old {
                    self.up(p as usize);
                } else if t > old {
                    self.down(p as usize);
                }
            }
            (true, None) => {
                self.len -= 1;
                let last = self.heap.get(self.len).copied().unwrap_or(uid);
                if let Some(q) = self.pos.get_mut(id) {
                    *q = NONE;
                }
                if last != uid {
                    self.put(p as usize, last);
                    self.up(p as usize);
                    let now_at = self.pos.get(last as usize).copied().unwrap_or(NONE);
                    self.down(now_at as usize);
                }
            }
            (false, None) => {}
        }
    }

    /// The earliest deadline and its id, without removing it.
    pub fn peek(&self) -> Option<(u64, usize)> {
        let id = *self.heap.first().filter(|_| self.len > 0)?;
        Some((self.at.get(id as usize).copied()?, id as usize))
    }

    /// The deadline of `id`, if it has one.
    pub fn deadline(&self, id: usize) -> Option<u64> {
        (self.pos.get(id).copied()? != NONE)
            .then(|| self.at.get(id).copied())
            .flatten()
    }
}

impl<const N: usize> Default for DeadlineHeap<N> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn orders_by_deadline_then_id_and_moves_in_place() {
        let mut h: DeadlineHeap<8> = DeadlineHeap::new();
        for (id, t) in [(3, 50), (1, 20), (5, 20), (0, 90), (7, 10)] {
            h.set(id, Some(t));
        }
        assert_eq!(h.peek(), Some((10, 7)));
        h.set(7, Some(100));
        assert_eq!(h.peek(), Some((20, 1)));
        h.set(1, None);
        assert_eq!(h.peek(), Some((20, 5)));
        h.set(0, Some(1));
        assert_eq!(h.peek(), Some((1, 0)));
        assert_eq!(h.len(), 4);
        let mut seen = std::vec::Vec::new();
        while let Some((t, id)) = h.peek() {
            seen.push((t, id));
            h.set(id, None);
        }
        assert_eq!(seen, [(1, 0), (20, 5), (50, 3), (100, 7)]);
    }

    #[test]
    fn random_operations_match_a_model() {
        let mut h: DeadlineHeap<16> = DeadlineHeap::new();
        let mut model = [None::<u64>; 16];
        let mut x = 12345u64;
        for _ in 0..5000 {
            x = x
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let id = ((x >> 33) % 16) as usize;
            let t = if (x >> 20).trailing_zeros() >= 2 {
                None
            } else {
                Some((x >> 40) % 1000)
            };
            h.set(id, t);
            if let Some(m) = model.get_mut(id) {
                *m = t;
            }
            let want = model.iter().enumerate().filter_map(|(i, t)| t.map(|t| (t, i))).min();
            assert_eq!(h.peek(), want);
        }
    }
}
