//! Putting the counts of many node programs together: the lives of one node into one report, and the reports of the
//! subscribers into the figures of a publish and subscribe measurement. Pure, so it is tested without containers.
//!
//! Invariants: what a node was owed is what the publishers sent while it could have received (every message of every
//! other publisher); a node whose report is missing counts as having received nothing and says so; a node that
//! started again never counts a message twice (per origin, it is capped at what that origin published).

use std::collections::BTreeMap;

use serde_json::{Map, Value, json};

use crate::node::data::Hist;
use crate::node::proto::PubSubReport;

/// The lives of one node as one report. A message a second life got again is not a second delivery: per origin the
/// total is capped at what that origin published.
pub(crate) fn merge_lives(lives: &[PubSubReport], published: &BTreeMap<u16, u32>) -> PubSubReport {
    let mut out = PubSubReport::default();
    for l in lives {
        out.published += l.published;
        out.duplicates += l.duplicates;
        out.unchecked += l.unchecked;
        out.bytes += l.bytes;
        out.latency_us.merge(&l.latency_us);
        out.latency_intended_us.merge(&l.latency_intended_us);
        for (o, n) in &l.per_origin {
            *out.per_origin.entry(*o).or_insert(0) += n;
        }
        out.gap_max_ms = match (out.gap_max_ms, l.gap_max_ms) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.or(b),
        };
    }
    for (o, n) in &mut out.per_origin {
        if let Some(cap) = published.get(o) {
            *n = (*n).min(u64::from(*cap));
        }
    }
    out.delivered = out.per_origin.values().sum();
    out
}

/// One subscriber's merged report, or none when it could not be read.
pub(crate) struct Subscriber {
    pub(crate) index: u16,
    pub(crate) report: Option<PubSubReport>,
}

/// The figures of a publish and subscribe measurement, by the names the results use. `publishers` maps a publisher's
/// index to the messages it was to send. A figure that cannot be computed is absent.
pub(crate) fn pubsub_figures(subs: &[Subscriber], publishers: &BTreeMap<u16, u32>) -> Map<String, Value> {
    let mut out = Map::new();
    let (mut expected, mut delivered, mut duplicates, mut unchecked, mut missing) = (0u64, 0u64, 0u64, 0u64, 0u32);
    let (mut lat, mut lat_intended) = (Hist::default(), Hist::default());
    let mut gap: Option<f64> = None;
    for s in subs {
        let owed: u64 = publishers
            .iter()
            .filter(|(p, _)| **p != s.index)
            .map(|(_, n)| u64::from(*n))
            .sum();
        expected += owed;
        match &s.report {
            Some(r) => {
                delivered += r.delivered.min(owed);
                duplicates += r.duplicates;
                unchecked += r.unchecked;
                lat.merge(&r.latency_us);
                lat_intended.merge(&r.latency_intended_us);
                gap = match (gap, r.gap_max_ms) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    (a, b) => a.or(b),
                };
            }
            None => missing += 1,
        }
    }
    if expected == 0 {
        return out;
    }
    let lost = expected - delivered;
    out.insert("expected".into(), json!(expected));
    out.insert("delivered".into(), json!(delivered));
    out.insert("lost".into(), json!(lost));
    // A count of a run fits an f64's integer range.
    #[allow(clippy::cast_precision_loss)]
    out.insert("loss_pct".into(), json!(lost as f64 * 100.0 / expected as f64));
    out.insert("duplicates".into(), json!(duplicates));
    if let Some(p) = lat.quantile(0.5) {
        out.insert("p50_us".into(), json!(p));
    }
    if let Some(p) = lat.quantile(0.99) {
        out.insert("p99_us".into(), json!(p));
    }
    // From the time the schedule meant each message to go: every wait of a publisher held back by its stack counts.
    for (k, q) in [("p50_intended_us", 0.5), ("p99_intended_us", 0.99), ("p999_intended_us", 0.999)] {
        if let Some(p) = lat_intended.quantile(q) {
            out.insert(k.into(), json!(p));
        }
    }
    if let Some(g) = gap {
        out.insert("gap_max_ms".into(), json!(g));
    }
    if missing > 0 {
        out.insert(
            "missing_reports".into(),
            json!(format!(
                "{missing} subscriber(s) could not be read; their messages count as lost"
            )),
        );
    }
    if unchecked > 0 {
        out.insert("unchecked".into(), json!(unchecked));
    }
    out
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use super::*;

    fn report(per: &[(u16, u64)], dups: u64, lat_us: &[u64], gap: Option<f64>) -> PubSubReport {
        let mut r = PubSubReport::default();
        for (o, n) in per {
            r.per_origin.insert(*o, *n);
            r.delivered += n;
        }
        r.duplicates = dups;
        for l in lat_us {
            r.latency_us.add(*l);
            // A publisher held back 500 us more than its stamp says.
            r.latency_intended_us.add(*l + 500);
        }
        r.gap_max_ms = gap;
        r
    }

    #[test]
    fn a_second_life_never_counts_a_message_twice() {
        let pubs = BTreeMap::from([(1u16, 100u32)]);
        let a = report(&[(1, 60)], 0, &[100], Some(5.0));
        let b = report(&[(1, 70)], 2, &[200], Some(9.0));
        let m = merge_lives(&[a, b], &pubs);
        assert_eq!(m.delivered, 100);
        assert_eq!(m.duplicates, 2);
        assert_eq!(m.gap_max_ms, Some(9.0));
        assert_eq!(m.latency_us.count(), 2);
    }

    #[test]
    fn figures_count_what_each_node_was_owed() {
        // Nodes 1 and 2 publish 10 each; nodes 2 and 3 subscribe. Node 2 is owed node 1's 10; node 3 is owed 20.
        let pubs = BTreeMap::from([(1u16, 10u32), (2, 10)]);
        let subs = [
            Subscriber {
                index: 2,
                report: Some(report(&[(1, 10)], 0, &[1000; 10], Some(2.0))),
            },
            Subscriber {
                index: 3,
                report: Some(report(&[(1, 10), (2, 5)], 1, &[3000; 15], Some(40.0))),
            },
        ];
        let f = pubsub_figures(&subs, &pubs);
        assert_eq!(f["expected"], json!(30));
        assert_eq!(f["delivered"], json!(25));
        assert_eq!(f["lost"], json!(5));
        assert!((f["loss_pct"].as_f64().unwrap() - 100.0 * 5.0 / 30.0).abs() < 1e-9);
        assert_eq!(f["duplicates"], json!(1));
        assert_eq!(f["gap_max_ms"], json!(40.0));
        // 10 values of 1 ms and 15 of 3 ms: the median is the 13th of 25, a 3 ms value.
        assert!((f["p50_us"].as_f64().unwrap() - 3000.0).abs() < 60.0);
        assert!((f["p50_intended_us"].as_f64().unwrap() - 3500.0).abs() < 70.0);
    }

    #[test]
    fn a_missing_report_counts_as_lost_and_says_so() {
        let pubs = BTreeMap::from([(1u16, 10u32)]);
        let subs = [Subscriber { index: 2, report: None }];
        let f = pubsub_figures(&subs, &pubs);
        assert_eq!(f["delivered"], json!(0));
        assert_eq!(f["lost"], json!(10));
        assert!(f.contains_key("missing_reports"));
        assert!(!f.contains_key("p50_us"));
    }

    #[test]
    fn nothing_owed_gives_no_figures() {
        let pubs = BTreeMap::from([(1u16, 10u32)]);
        let subs = [Subscriber { index: 1, report: None }];
        assert!(pubsub_figures(&subs, &pubs).is_empty());
    }
}
