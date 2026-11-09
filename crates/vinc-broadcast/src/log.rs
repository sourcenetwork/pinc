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

use crate::consts::{LOG_BYTES, LOG_CAP, LOG_WINDOW};
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
    pub(crate) fn new() -> Self {
        Self {
            entries: VecDeque::with_capacity(LOG_CAP),
            index: MidMap::with_capacity(LOG_CAP),
            base: 0,
            ring: vec![0; LOG_BYTES],
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
