//! A hub's log of one topic: the last [`LOG_CAP`] messages of the last [`LOG_WINDOW`], kept in a byte ring.
//!
//! The ring and the entry queue are allocated once when the log is created; pushing a message copies its bytes into
//! the ring and evicts the oldest messages until the new one fits, so the steady path allocates nothing and the log
//! is bounded in bytes as well as in entries.
//!
//! Invariants: entries are in arrival order; an entry's bytes are contiguous in the ring (a message that would
//! straddle the end starts at the beginning, and the skipped tail is charged to it); a message id is in the log at
//! most once.

use alloc::collections::VecDeque;
use alloc::vec;
use alloc::vec::Vec;
use vinc_membership::Nanos;

use crate::consts::{LOG_CAP, LOG_WINDOW};
use crate::table::MidMap;

#[derive(Debug, Clone, Copy)]
struct Entry {
    mid: u64,
    at: Nanos,
    wall_ms: u64,
    off: usize,
    len: usize,
    // Bytes this entry occupies in the ring, its own length plus any tail skipped to keep it contiguous.
    cost: usize,
}

/// The log of one topic on a hub.
#[derive(Debug)]
pub(crate) struct HubLog {
    entries: VecDeque<Entry>,
    index: MidMap,
    base: u64,
    ring: Vec<u8>,
    wpos: usize,
    used: usize,
}

impl HubLog {
    pub(crate) fn new(bytes: usize) -> Self {
        Self {
            entries: VecDeque::with_capacity(LOG_CAP),
            index: MidMap::with_capacity(LOG_CAP),
            base: 0,
            ring: vec![0; bytes],
            wpos: 0,
            used: 0,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn contains(&self, mid: u64) -> bool {
        self.index.get(mid).is_some()
    }

    /// When the oldest message leaves the window (strictly after this instant), if any.
    pub(crate) fn next_expiry(&self) -> Option<Nanos> {
        self.entries
            .front()
            .map(|e| e.at.saturating_add(LOG_WINDOW).saturating_add(1))
    }

    /// The sequence number the next message will get. Every logged message has a smaller one, in arrival order, and
    /// a number is never used twice.
    pub(crate) fn end(&self) -> u64 {
        self.base + u64::try_from(self.entries.len()).unwrap_or(0)
    }

    /// The sequence number of the oldest message still logged.
    pub(crate) const fn base(&self) -> u64 {
        self.base
    }

    /// The head and body of the message with sequence number `seq`, if it is still logged.
    pub(crate) fn at(&self, seq: u64) -> Option<&[u8]> {
        let e = self.entries.get(usize::try_from(seq.checked_sub(self.base)?).ok()?)?;
        self.ring.get(e.off..e.off + e.len)
    }

    /// When the message with sequence number `seq` was logged, if it still is.
    pub(crate) fn logged_at(&self, seq: u64) -> Option<Nanos> {
        let e = self.entries.get(usize::try_from(seq.checked_sub(self.base)?).ok()?)?;
        Some(e.at)
    }

    /// How many of the oldest messages [`HubLog::push`] would evict to fit a message of `n` bytes, evicting none:
    /// the loop of `push` on copies of the accounting.
    pub(crate) fn evicts(&self, n: usize) -> usize {
        let (mut wpos, mut used, mut k) = (self.wpos, self.used, 0);
        let ring = self.ring.len();
        loop {
            let pad = if wpos + n > ring { ring - wpos } else { 0 };
            if self.entries.len() - k < LOG_CAP && used + pad + n <= ring {
                return k;
            }
            let Some(e) = self.entries.get(k) else { return k };
            k += 1;
            used -= e.cost;
            if k == self.entries.len() {
                wpos = 0;
                used = 0;
            }
        }
    }

    fn entry(&self, mid: u64) -> Option<&Entry> {
        let seq = self.index.get(mid)?;
        self.entries.get(usize::try_from(seq.checked_sub(self.base)?).ok()?)
    }

    /// The head and body of a logged message.
    pub(crate) fn get(&self, mid: u64) -> Option<&[u8]> {
        let e = self.entry(mid)?;
        self.ring.get(e.off..e.off + e.len)
    }

    /// Drop the oldest message; returns its id.
    pub(crate) fn pop(&mut self) -> Option<u64> {
        let e = self.entries.pop_front()?;
        if self.index.get(e.mid) == Some(self.base) {
            self.index.remove(e.mid);
        }
        self.base += 1;
        self.used -= e.cost;
        if self.entries.is_empty() {
            self.wpos = 0;
            self.used = 0;
        }
        Some(e.mid)
    }

    /// Log a message made of `head` then `body`. Evicted ids go to `evicted`. Returns false if it cannot fit.
    pub(crate) fn push(
        &mut self,
        mid: u64,
        at: Nanos,
        wall_ms: u64,
        head: &[u8],
        body: &[u8],
        mut evicted: impl FnMut(u64),
    ) -> bool {
        let n = head.len() + body.len();
        if n > self.ring.len() || self.contains(mid) {
            return false;
        }
        loop {
            let pad = if self.wpos + n > self.ring.len() {
                self.ring.len() - self.wpos
            } else {
                0
            };
            if self.entries.len() < LOG_CAP && self.used + pad + n <= self.ring.len() {
                let off = if pad > 0 { 0 } else { self.wpos };
                if let Some(d) = self.ring.get_mut(off..off + head.len()) {
                    d.copy_from_slice(head);
                }
                if let Some(d) = self.ring.get_mut(off + head.len()..off + n) {
                    d.copy_from_slice(body);
                }
                let seq = self.base + u64::try_from(self.entries.len()).unwrap_or(0);
                self.entries.push_back(Entry {
                    mid,
                    at,
                    wall_ms,
                    off,
                    len: n,
                    cost: pad + n,
                });
                self.index.insert(mid, seq);
                self.used += pad + n;
                self.wpos = (off + n) % self.ring.len();
                return true;
            }
            match self.pop() {
                Some(old) => evicted(old),
                None => return false,
            }
        }
    }

    /// Drop the messages older than the window; each dropped id goes to `gone`.
    pub(crate) fn expire(&mut self, now: Nanos, mut gone: impl FnMut(u64)) {
        while self
            .entries
            .front()
            .is_some_and(|e| now.saturating_sub(e.at) > LOG_WINDOW)
        {
            if let Some(m) = self.pop() {
                gone(m);
            }
        }
    }

    /// The ids of messages logged at or after `since_ms` (the hub's wall clock), oldest first.
    pub(crate) fn since(&self, since_ms: u64) -> impl DoubleEndedIterator<Item = u64> + '_ {
        self.entries
            .iter()
            .filter(move |e| e.wall_ms >= since_ms)
            .map(|e| e.mid)
    }

    /// The ids logged in `[now - from, now - to)`, oldest first.
    pub(crate) fn window(&self, now: Nanos, from: Nanos, to: Nanos) -> impl DoubleEndedIterator<Item = u64> + '_ {
        self.entries
            .iter()
            .filter(move |e| now.saturating_sub(from) <= e.at && e.at < now.saturating_sub(to))
            .map(|e| e.mid)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `evicts` names exactly the messages `push` then evicts, across wraps, padding and the entry cap.
    #[test]
    fn evicts_predicts_push() {
        let mut log = HubLog::new(10_000);
        let mut x = 7u64;
        for mid in 0..20_000u64 {
            x = x.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            // Runs of one-byte messages reach the entry cap before the bytes run out.
            let n = if (x >> 40).is_multiple_of(4) {
                usize::try_from(x >> 52).unwrap_or(0) % 3000 + 1
            } else {
                1
            };
            let body = vec![0u8; n];
            let want = log.evicts(n);
            let mut got = 0;
            assert!(log.push(mid, 0, 0, &[], &body, |_| got += 1));
            assert_eq!(want, got, "message {mid} of {n} bytes");
            assert_eq!(log.at(log.end() - 1).map(<[u8]>::len), Some(n));
        }
    }
}
