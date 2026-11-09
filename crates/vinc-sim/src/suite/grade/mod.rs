//! Grading: the validity gates, the 21 score terms, the score against a reference and the noise floor.
//!
//! Everything here is computed from a finished [`crate::suite::rec::Rec`], the [`World`] it ran and a
//! [`RunFacts`] holding what only the host knows (final node state, key-provenance verdicts, CPU and export sizes).
//! The formulas are the reference harness's, ported exactly: [`gates`] decides the gates, [`terms`] the terms (the
//! current metric and the fair one), [`mod@score`] pools and scores them against a reference term set, [`noise`] draws
//! the noise floor and decides `is_better`, [`delivery`] is the small-message delivery check.
//!
//! Invariants: nothing here reads a clock or a random source other than the seeded noise draw; a gate that cannot be
//! decided because the run lacks a layer or a verdict is reported as not evaluated, never as a pass; a term with no
//! samples is `None` and is dropped from the score, never zero.

pub mod delivery;
pub mod fixture;
pub mod gates;
pub mod noise;
pub mod score;
pub mod terms;

pub use delivery::{DeliveryShares, delivery_share, delivery_shares};
pub use gates::{GATES, GateReport, GateStatus, evaluate_gates, gate_det};
pub use noise::{NOISE_DRAWS, NoiseError, is_better, noise_floor};
pub use score::{GROUPS, ScenarioRuns, ScenarioScore, ScoreReport, WEIGHTS, pool, scenario_score, score, total};
pub use terms::{FairSamples, compute_fair_terms, compute_terms, with_fair};

use crate::suite::rec::Rec;
use crate::suite::world::model::World;

/// The 21 term names in the reference order (latency, throughput, continuation, cost, resources).
pub const TERMS: [&str; 21] = [
    "L1", "L2", "L3", "L4", "L5", "T1", "T2", "T3", "T4", "C1", "C2", "C3", "C4", "B1", "B2", "B3", "B4", "B5", "R1",
    "R2", "R3",
];

/// The terms of one run (or the pool of several): one optional value per term, in [`TERMS`] order. `None` means
/// the term does not apply or had no samples.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Terms {
    v: [Option<f64>; 21],
}

impl Terms {
    /// All terms absent.
    pub fn new() -> Self {
        Self::default()
    }

    /// The value of term `name`; `None` for an absent term or an unknown name.
    pub fn get(&self, name: &str) -> Option<f64> {
        TERMS
            .iter()
            .position(|t| *t == name)
            .and_then(|i| self.v.get(i).copied().flatten())
    }

    /// Sets term `name`; an unknown name is ignored.
    pub fn set(&mut self, name: &str, value: Option<f64>) {
        if let Some(slot) = TERMS.iter().position(|t| *t == name).and_then(|i| self.v.get_mut(i)) {
            *slot = value;
        }
    }

    /// Builds the terms from `(name, value)` pairs.
    pub fn from_pairs(pairs: &[(&str, f64)]) -> Self {
        let mut t = Self::new();
        for (k, v) in pairs {
            t.set(k, Some(*v));
        }
        t
    }

    /// The terms in order with their values.
    pub fn iter(&self) -> impl Iterator<Item = (&'static str, Option<f64>)> + '_ {
        TERMS.iter().copied().zip(self.v.iter().copied())
    }
}

/// What the host knows about one node at the end of the run.
#[derive(Clone, Debug, PartialEq)]
pub struct NodeFacts {
    /// The device class (`cloud`, `desktop`, `phone`, `browser`, `embedded`, `mcu`); caps for G-BOUND.
    pub device: String,
    /// The node's site at the end of the run (it changes at a handover); G-SURFACE's base round trip uses it.
    pub site: usize,
    /// A state peak the host observed outside [`Rec::state_sample`]; the effective peak is the larger of both. Zero
    /// when every sample went through the recorder.
    pub state_peak: u64,
    /// The node's `view()` as `(epoch, members)` with members resolved to node indices; `None` when the call did
    /// not return a view, which fails G-AWARE for a node that is alive and awake at the end.
    pub view: Option<(u64, Vec<usize>)>,
    /// The node is running at the end.
    pub alive_at_end: bool,
    /// The node is suspended at the end.
    pub suspended_at_end: bool,
    /// The largest `export_state` blob it ever produced (0 if never exported): feeds R3.
    pub export_max: u64,
}

/// The security verdict inputs, produced by the instrumented crypto from the real keys.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SecFacts {
    /// Payload keys the harvest-now-decrypt-later adversary can derive.
    pub hndl_known_payload_keys: u64,
    /// Payload keys first used before a compromise that the classical adversary then derives.
    pub forward_secrecy_broken: u64,
    /// AEAD nonces reused under one key with different content.
    pub nonce_reuse: u64,
    /// Keys whose provenance the instrumentation could not establish: the verdict cannot be trusted.
    pub unknown_provenance: u64,
    /// Payload seen in plaintext on the wire, `(node, time)`, beyond what [`Rec::plaintext_payload`] holds.
    pub plaintext_payload: Vec<(usize, u64)>,
}

/// What the gates and terms need from the host beyond the recorder.
#[derive(Clone, Debug, PartialEq)]
pub struct RunFacts {
    /// One entry per world node (a missing entry counts as a dead node with no export).
    pub nodes: Vec<NodeFacts>,
    /// The security verdict inputs.
    pub sec: SecFacts,
    /// The static provenance lint passed (G-PROV).
    pub prov_clean: bool,
    /// The run has a membership layer; without one G-AWARE cannot be decided.
    pub has_membership: bool,
    /// The endpoint's own awareness bound in ns; the gate uses the smaller of it and the world's cap.
    pub awareness_bound_ns: u64,
    /// The endpoint's own false-suspicion rate per member hour; the gate uses the smaller of it and the world's cap.
    pub false_suspicion_per_member_hour: f64,
}

impl RunFacts {
    /// Facts for a run that ended with every node alive and awake at its first site and nothing else known: the
    /// reference defaults for the endpoint constants (60 s awareness bound, 0.1 false suspicions per member hour).
    pub fn new(world: &World) -> Self {
        let nodes = world
            .nodes
            .iter()
            .map(|n| NodeFacts {
                device: n.device.clone(),
                site: n.site,
                state_peak: 0,
                view: None,
                alive_at_end: true,
                suspended_at_end: false,
                export_max: 0,
            })
            .collect();
        Self {
            nodes,
            sec: SecFacts::default(),
            prov_clean: true,
            has_membership: true,
            awareness_bound_ns: 60 * crate::suite::rec::NS,
            false_suspicion_per_member_hour: 0.1,
        }
    }

    /// The effective state peak of node `idx`: the larger of the recorder's samples and the host's own peak, or
    /// `None` when the node was never sampled.
    pub(crate) fn state_peak(&self, rec: &Rec, idx: usize) -> Option<u64> {
        let own = self.nodes.get(idx).map_or(0, |n| n.state_peak);
        match (rec.state_peaks.get(&idx).copied(), own) {
            (None, 0) => None,
            (r, own) => Some(r.unwrap_or(0).max(own)),
        }
    }
}

/// `sorted(xs)[len // 2]`, or `None` when empty.
pub(crate) fn p50(xs: &[i64]) -> Option<f64> {
    if xs.is_empty() {
        return None;
    }
    let mut s = xs.to_vec();
    s.sort_unstable();
    s.get(s.len() / 2).map(|&v| v as f64)
}

/// The mean of the largest `ceil(5% * len)` (at least 1) values, or `None` when empty.
pub(crate) fn tail_mean(xs: &[i64]) -> Option<f64> {
    if xs.is_empty() {
        return None;
    }
    let mut s = xs.to_vec();
    s.sort_unstable();
    let k = ((s.len() as f64 * 0.05).ceil() as usize).max(1);
    let sum: i128 = s.iter().skip(s.len() - k).map(|&v| i128::from(v)).sum();
    Some(sum as f64 / k as f64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn p50_takes_the_upper_middle_and_tail_the_ceil_five_percent() {
        assert_eq!(p50(&[]), None);
        assert_eq!(p50(&[5]), Some(5.0));
        assert_eq!(p50(&[4, 1, 3, 2]), Some(3.0));
        assert_eq!(tail_mean(&[]), None);
        assert_eq!(tail_mean(&[7]), Some(7.0));
        let twenty: Vec<i64> = (1..=20).collect();
        assert_eq!(tail_mean(&twenty), Some(20.0));
        let twenty_one: Vec<i64> = (1..=21).collect();
        assert_eq!(tail_mean(&twenty_one), Some(20.5));
    }

    #[test]
    fn terms_set_get_and_unknown_names() {
        let mut t = Terms::new();
        assert_eq!(t.get("L1"), None);
        t.set("L1", Some(2.0));
        t.set("nope", Some(1.0));
        assert_eq!(t.get("L1"), Some(2.0));
        assert_eq!(t.get("nope"), None);
        assert_eq!(t.iter().filter(|(_, v)| v.is_some()).count(), 1);
        assert_eq!(t.iter().count(), 21);
    }
}
