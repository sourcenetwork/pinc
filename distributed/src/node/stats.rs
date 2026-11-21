//! What a node counts of the publish and subscribe workload, the same for every stack: distinct deliveries, duplicates,
//! delivery latency from the header the sender wrote, bytes, and the longest silence between two deliveries.
//!
//! Invariants: a delivery is counted once per (origin, sequence); the table of seen messages is bounded and a delivery
//! that finds it full is counted as delivered and as unchecked, never dropped; a latency is the receiver's wall clock
//! minus the sender's, both read on the same machine or on machines whose clocks the run states are not synchronised.

use std::collections::HashSet;

use crate::node::data::Header;
use crate::node::proto::PubSubReport;

/// The most (origin, sequence) pairs remembered for duplicate detection.
const SEEN_MAX: usize = 4 << 20;

/// The counters of one node.
#[derive(Debug)]
pub struct PubSubStats {
    me: u16,
    seen: HashSet<(u16, u32)>,
    rep: PubSubReport,
    first_ns: Option<u64>,
    last_ns: u64,
    gap_max_ns: u64,
    gap_at_ns: u64,
    /// The publisher's counts of how its stack took its messages (`publish_waited`, `publish_refused`), for a stack
    /// whose node keeps none of its own.
    counters: std::collections::BTreeMap<&'static str, u64>,
}

impl PubSubStats {
    /// Counters for the node with index `me` (its own messages are not deliveries).
    pub fn new(me: u16) -> Self {
        Self {
            me,
            seen: HashSet::new(),
            rep: PubSubReport::default(),
            first_ns: None,
            last_ns: 0,
            gap_max_ns: 0,
            gap_at_ns: 0,
            counters: std::collections::BTreeMap::new(),
        }
    }

    /// Count one `what` of the publisher.
    pub fn count(&mut self, what: &'static str) {
        *self.counters.entry(what).or_insert(0) += 1;
    }

    /// The publisher's counts.
    pub fn counters(&self) -> &std::collections::BTreeMap<&'static str, u64> {
        &self.counters
    }

    /// This node published a message.
    pub fn published(&mut self) {
        self.rep.published += 1;
    }

    /// A message `body` arrived at wall time `now_ns`. Bodies without a header are not workload messages and are
    /// ignored.
    pub fn record(&mut self, body: &[u8], now_ns: u64) {
        let Some(h) = Header::parse(body) else { return };
        if h.origin == self.me {
            return;
        }
        if self.seen.len() >= SEEN_MAX {
            self.rep.unchecked += 1;
        } else if !self.seen.insert((h.origin, h.seq)) {
            self.rep.duplicates += 1;
            return;
        }
        self.rep.delivered += 1;
        self.rep.bytes += body.len() as u64;
        *self.rep.per_origin.entry(h.origin).or_insert(0) += 1;
        self.rep.latency_us.add(now_ns.saturating_sub(h.sent_ns) / 1000);
        self.rep
            .latency_intended_us
            .add(now_ns.saturating_sub(h.intended_ns) / 1000);
        if self.first_ns.is_none() {
            self.first_ns = Some(now_ns);
        } else {
            let gap = now_ns.saturating_sub(self.last_ns);
            if gap > self.gap_max_ns {
                self.gap_max_ns = gap;
                self.gap_at_ns = self.last_ns;
            }
        }
        self.last_ns = now_ns;
    }

    /// What was counted.
    // Nanosecond spans of a run fit an f64's integer range.
    #[allow(clippy::cast_precision_loss)]
    pub fn report(&self) -> PubSubReport {
        let mut r = self.rep.clone();
        if let Some(first) = self.first_ns.filter(|_| self.rep.delivered > 1) {
            r.gap_max_ms = Some(self.gap_max_ns as f64 / 1e6);
            r.gap_at_ms = Some(self.gap_at_ns.saturating_sub(first) as f64 / 1e6);
        }
        r
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    fn body(origin: u16, seq: u32, sent_ns: u64) -> Vec<u8> {
        Header {
            origin,
            seq,
            sent_ns,
            intended_ns: sent_ns,
        }
        .body(64)
    }

    #[test]
    fn deliveries_are_counted_once_and_latency_comes_from_the_header() {
        let mut s = PubSubStats::new(3);
        s.record(&body(1, 0, 1_000_000), 6_000_000);
        s.record(&body(1, 0, 1_000_000), 7_000_000);
        s.record(&body(1, 1, 2_000_000), 8_000_000);
        s.record(&body(3, 0, 2_000_000), 8_000_000);
        s.record(b"not a workload message", 9_000_000);
        let r = s.report();
        assert_eq!((r.delivered, r.duplicates, r.bytes), (2, 1, 128));
        assert_eq!(r.per_origin.get(&1), Some(&2));
        // 5 ms and 6 ms.
        let p50 = r.latency_us.quantile(0.5).unwrap();
        assert!((p50 - 5000.0).abs() < 100.0, "{p50}");
        // The longest silence: from the first delivery at 6 ms to the second at 8 ms.
        assert!((r.gap_max_ms.unwrap() - 2.0).abs() < 1e-9);
        assert!(r.gap_at_ms.unwrap().abs() < 1e-9);
    }

    #[test]
    fn a_single_delivery_has_no_gap() {
        let mut s = PubSubStats::new(0);
        s.record(&body(1, 0, 0), 10);
        assert_eq!(s.report().gap_max_ms, None);
    }
}
