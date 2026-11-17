//! A hub's log of one topic: the last [`LOG_CAP`] messages of the last [`LOG_WINDOW`], kept in a byte ring.
//!
//! The ring and the entry queue are allocated once when the log is created; pushing a message copies its bytes into
//! the ring and evicts the oldest messages until the new one fits, so the steady path allocates nothing and the log
//! is bounded in bytes as well as in entries.
//!
//! Invariants: entries are in arrival order; an entry's bytes are contiguous in the ring (a message that would
//! straddle the end starts at the beginning, and the skipped tail is charged to it); a message id is in the log at
//! most once; an entry keeps the print of its message's signature and hands it on with the id when it leaves; `origins`
//! counts the entries of each origin, kept where an entry is pushed and popped; `gone` is the newest stamp of a message
//! that left the log, so a hub can say whether it still holds everything since a time.

use alloc::collections::{BTreeMap, VecDeque};
use alloc::vec;
use alloc::vec::Vec;
use vinc_membership::{Nanos, NodeId};

use crate::consts::{LOG_CAP, LOG_WINDOW};
use crate::table::{IdKey, MidMap};

#[derive(Debug, Clone, Copy)]
struct Entry {
    mid: u64,
    origin: NodeId,
    at: Nanos,
    wall_ms: u64,
    // The print of the logged message's signature, handed on with the id when the entry leaves the log.
    print: u64,
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
    /// How many logged messages each origin has here.
    origins: BTreeMap<NodeId, u32>,
    /// When the newest message that left the log (evicted or expired) was logged, on the hub's wall clock.
    gone: Option<u64>,
}

impl HubLog {
    pub(crate) fn new(bytes: usize, key: IdKey) -> Self {
        Self {
            entries: VecDeque::with_capacity(LOG_CAP),
            index: MidMap::with_capacity(LOG_CAP, key),
            base: 0,
            ring: vec![0; bytes],
            wpos: 0,
            used: 0,
            origins: BTreeMap::new(),
            gone: None,
        }
    }

    /// Whether a message logged at or after `since_ms` (the hub's wall clock) has left the log: a hub asked for the
    /// topic from that time cannot offer everything.
    pub(crate) fn dropped_since(&self, since_ms: u64) -> bool {
        self.gone.is_some_and(|w| w >= since_ms)
    }

    /// Whether a message of `origin` is logged here.
    pub(crate) fn holds(&self, origin: &NodeId) -> bool {
        self.origins.contains_key(origin)
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn contains(&self, mid: u64) -> bool {
        self.index.get(mid).is_some()
    }

    /// How many walks of the index read as many slots as [`PROBE_LONG`](crate::table::PROBE_LONG) or more.
    pub(crate) fn long_walks(&self) -> u64 {
        self.index.long_walks()
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

    /// The hub's wall clock when the message with sequence number `seq` was logged, if it still is.
    pub(crate) fn wall_at(&self, seq: u64) -> Option<u64> {
        let e = self.entries.get(usize::try_from(seq.checked_sub(self.base)?).ok()?)?;
        Some(e.wall_ms)
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

    /// The sequence number of a logged message.
    pub(crate) fn seq_of(&self, mid: u64) -> Option<u64> {
        let seq = self.index.get(mid)?;
        self.entry(mid).map(|_| seq)
    }

    /// The head and body of a logged message.
    pub(crate) fn get(&self, mid: u64) -> Option<&[u8]> {
        let e = self.entry(mid)?;
        self.ring.get(e.off..e.off + e.len)
    }

    /// The print of the signature of a logged message.
    pub(crate) fn print(&self, mid: u64) -> Option<u64> {
        self.entry(mid).map(|e| e.print)
    }

    /// Drop the oldest message; returns its id and its print.
    pub(crate) fn pop(&mut self) -> Option<(u64, u64)> {
        let e = self.entries.pop_front()?;
        if let Some(n) = self.origins.get_mut(&e.origin) {
            *n -= 1;
            if *n == 0 {
                self.origins.remove(&e.origin);
            }
        }
        if self.index.get(e.mid) == Some(self.base) {
            self.index.remove(e.mid);
        }
        self.base += 1;
        self.gone = Some(self.gone.map_or(e.wall_ms, |w| w.max(e.wall_ms)));
        self.used -= e.cost;
        if self.entries.is_empty() {
            self.wpos = 0;
            self.used = 0;
        }
        Some((e.mid, e.print))
    }

    /// Log a message of `origin` made of `head` then `body`, with the `print` of its signature. Each evicted message's
    /// id and print go to `evicted`. Returns false if it cannot fit.
    #[allow(clippy::too_many_arguments, reason = "the parts of one logged message")]
    pub(crate) fn push(
        &mut self,
        mid: u64,
        origin: &NodeId,
        at: Nanos,
        wall_ms: u64,
        head: &[u8],
        body: &[u8],
        print: u64,
        mut evicted: impl FnMut(u64, u64),
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
                    origin: *origin,
                    at,
                    wall_ms,
                    print,
                    off,
                    len: n,
                    cost: pad + n,
                });
                self.index.insert(mid, seq);
                *self.origins.entry(*origin).or_insert(0) += 1;
                self.used += pad + n;
                self.wpos = (off + n) % self.ring.len();
                return true;
            }
            match self.pop() {
                Some((old, p)) => evicted(old, p),
                None => return false,
            }
        }
    }

    /// Drop the messages older than the window; each dropped id and its print go to `gone`.
    pub(crate) fn expire(&mut self, now: Nanos, mut gone: impl FnMut(u64, u64)) {
        while self
            .entries
            .front()
            .is_some_and(|e| now.saturating_sub(e.at) > LOG_WINDOW)
        {
            if let Some((m, p)) = self.pop() {
                gone(m, p);
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

    #[allow(clippy::unwrap_used, reason = "the secrets are fixed and nonzero")]
    fn key() -> IdKey {
        IdKey::new(7, &crate::table::TEST_SECRETS).unwrap()
    }

    /// `evicts` names exactly the messages `push` then evicts, across wraps, padding and the entry cap.
    #[test]
    fn evicts_predicts_push() {
        let mut log = HubLog::new(10_000, key());
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
            let origin = [u8::try_from(mid % 3).unwrap_or(0); 32];
            assert!(log.push(mid, &origin, 0, 0, &[], &body, mid + 1, |_, _| got += 1));
            assert_eq!(want, got, "message {mid} of {n} bytes");
            assert_eq!(log.at(log.end() - 1).map(<[u8]>::len), Some(n));
            // The count of each origin is that of its entries still logged (looked at every 97th message).
            for o in (0..3u8).filter(|_| mid % 97 == 0) {
                let logged = (log.base()..log.end()).any(|seq| u64::from(o) == seq_mid(&log, seq) % 3);
                assert_eq!(log.holds(&[o; 32]), logged, "origin {o} after message {mid}");
            }
        }
        log.expire(LOG_WINDOW + 1, |_, _| {});
        assert!((0..3u8).all(|o| !log.holds(&[o; 32])), "an empty log holds no origin");
    }

    /// An evicted entry hands its id and its print on, and so does an expired one; a logged entry answers its print.
    #[test]
    fn an_evicted_entry_hands_over_its_print() {
        let mut log = HubLog::new(100, key());
        let body = [0u8; 60];
        let mut gone = Vec::new();
        assert!(log.push(1, &[1; 32], 0, 0, &[], &body, 11, |m, p| gone.push((m, p))));
        assert_eq!((log.print(1), gone.len()), (Some(11), 0));
        assert!(log.push(2, &[1; 32], 1, 1, &[], &body, 22, |m, p| gone.push((m, p))));
        assert_eq!(gone, vec![(1, 11)], "the first left with its print");
        assert_eq!((log.print(1), log.print(2)), (None, Some(22)));
        log.expire(LOG_WINDOW + 2, |m, p| gone.push((m, p)));
        assert_eq!(gone, vec![(1, 11), (2, 22)], "the expired one left with its print");
        assert_eq!(log.print(2), None);
    }

    fn seq_mid(log: &HubLog, seq: u64) -> u64 {
        log.entries
            .get(usize::try_from(seq - log.base()).unwrap_or(usize::MAX))
            .map_or(u64::MAX, |e| e.mid)
    }
}
