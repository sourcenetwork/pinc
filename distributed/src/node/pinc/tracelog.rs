//! The bounded log a PINC node keeps when the scenario asks for traces: the node's trace records and every datagram
//! and relay carrier write or read, each with the milliseconds since the node started.
//!
//! Invariants: at most [`CAP`] entries and [`CAP_BYTES`] bytes of text are held; the oldest go first and `dropped`
//! counts them, so a reader knows whether the log starts at the beginning.

use std::collections::VecDeque;
use std::time::Instant;

use serde_json::{Value, json};

/// The most entries kept.
pub const CAP: usize = 50_000;
/// The most bytes of entry text kept: a trace record can be long, so the count alone does not bound the memory.
pub const CAP_BYTES: usize = 32 << 20;

/// One entry: milliseconds since the node started, a short kind, and a text.
pub type Entry = (u64, &'static str, String);

/// The log. See the module docs.
pub struct TraceLog {
    start: Instant,
    entries: VecDeque<Entry>,
    dropped: u64,
    bytes: usize,
    cap: usize,
}

impl TraceLog {
    /// An empty log whose clock starts now.
    pub fn new() -> Self {
        Self::with_cap(CAP)
    }

    fn with_cap(cap: usize) -> Self {
        Self {
            start: Instant::now(),
            entries: VecDeque::new(),
            dropped: 0,
            bytes: 0,
            cap,
        }
    }

    /// Add an entry at `ms`, dropping the oldest while the log is full by count or by bytes.
    pub fn push(&mut self, ms: u64, kind: &'static str, text: String) {
        self.bytes += text.len();
        while self.entries.len() >= self.cap || self.bytes > CAP_BYTES {
            let Some((_, _, old)) = self.entries.pop_front() else {
                break;
            };
            self.bytes -= old.len();
            self.dropped += 1;
        }
        self.entries.push_back((ms, kind, text));
    }

    /// Add an entry stamped with the time since the log was made.
    pub fn note(&mut self, kind: &'static str, text: String) {
        let ms = u64::try_from(self.start.elapsed().as_millis()).unwrap_or(u64::MAX);
        self.push(ms, kind, text);
    }

    /// The log as the report carries it: `{"dropped": n, "entries": [[ms, kind, text], ...]}`.
    pub fn report(&self) -> Value {
        json!({ "dropped": self.dropped, "entries": self.entries })
    }
}

impl Default for TraceLog {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_full_log_drops_the_oldest_and_counts_them() {
        let mut l = TraceLog::with_cap(3);
        for i in 0..5u64 {
            l.push(i, "udp_rx", format!("peer {i}"));
        }
        assert_eq!(
            l.report(),
            json!({ "dropped": 2, "entries": [[2, "udp_rx", "peer 2"], [3, "udp_rx", "peer 3"], [4, "udp_rx", "peer 4"]] })
        );
    }

    #[test]
    fn the_real_capacity_is_fifty_thousand() {
        let mut l = TraceLog::new();
        for i in 0..(CAP as u64 + 7) {
            l.push(i, "trace", String::new());
        }
        assert_eq!(l.entries.len(), CAP);
        assert_eq!(l.dropped, 7);
    }

    #[test]
    fn long_entries_are_bounded_by_their_bytes() {
        let mut l = TraceLog::new();
        for i in 0..40u64 {
            l.push(i, "trace", "x".repeat(1 << 20));
        }
        assert_eq!((l.entries.len(), l.dropped, l.bytes), (32, 8, CAP_BYTES));
    }
}
