//! The delay-tolerant workload: bundles sent to nodes that are offline, carried by others, with the checks that decide
//! whether the rules of `vinc-dtn` held. The node programs report what happened to every bundle (see
//! `node::proto::DtnReport`); [`evaluate`] reads those logs against the scenario's checks.
//!
//! Each check is a rule of the crate, as its models name it:
//! - `delivered` / `not-delivered`: store and forward: a bundle reaches its destination once and intact, through the
//!   named carrier, after the destination came back (`DtnScenario.tla` `Served`); or never, when it expired first.
//! - `custody`: custody leaves a node only by a verified acknowledgement from the node it was offered to, which took
//!   custody first, and only up the rank of node ids (`DtnScenario.tla` `CustodyAlive`, `DtnCustody.tla`).
//! - `copies`: spray and wait never makes more holders than the copy budget, and a node hands on fewer copies than it
//!   received (`DtnScenario.tla` `HeldLeBudget` and `Account`, `DtnForward.tla` `HeldNeverGrows`).
//! - `no-refetch`: a reception that resumes never asks again for a symbol it verified (`DtnReception.tla`).
//! - `refused`: a transfer refused for the named reason (a full ledger, a slice that fails its proof).
//! - `within-budget`: the store never held more than its ledger's budget (`DtnStore.tla` `Inv`).
//! - `expired`: every holder ends the bundle at its lifetime and keeps nothing (`DtnStore.tla`, `DtnScenario.tla`).
//! - `restored`: what a restarted node read back from its kept store, a record with a tampered head dropped.
//!
//! Invariants: a check that cannot be decided from the logs fails and says why; a log that lost trace records fails
//! every check, because an absent entry would then prove nothing.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use serde_json::{Map, Value, json};

use crate::node::proto::{DtnReport, DtnWhat};
use crate::scenario::{NodeSpec, Problem, Role, Scenario, Stack};

/// The delay-tolerant workload.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Dtn {
    /// Payload sizes, one after the other.
    pub sizes: Vec<u64>,
    /// Seconds each repetition runs from its start; the faults count from the same start.
    pub duration_s: f64,
    /// Seconds between everyone having joined and the start.
    #[serde(default = "warmup_default")]
    pub warmup_s: f64,
    /// Settings of nodes that differ from the defaults (every peer runs the layer).
    #[serde(default)]
    pub nodes: Vec<DtnNode>,
    /// The bundles sent.
    pub sends: Vec<Send>,
    /// Contact windows; when there are any, a node is in contact only during its windows.
    #[serde(default)]
    pub contacts: Vec<Window>,
    /// The rules checked.
    pub checks: Vec<Check>,
    /// The stacks without delay-tolerant delivery run the same sends as one publication each, with no store and
    /// forward, and report what reached the destination.
    #[serde(default)]
    pub baseline: bool,
}

fn warmup_default() -> f64 {
    3.0
}

/// One node's settings.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DtnNode {
    /// The node.
    pub name: String,
    /// The ledger's budget as a multiple of one bundle's sealed size (64 MiB when not set).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub budget_bundles: Option<f64>,
    /// Keep the bundle store on disk, so the node resumes from it when it is restarted.
    #[serde(default)]
    pub persist: bool,
    /// The node's store corrupts every slice it keeps.
    #[serde(default)]
    pub tamper_slices: bool,
    /// The heads of the held bundles' records are corrupted when the node starts from its kept store.
    #[serde(default)]
    pub tamper_heads: bool,
}

/// Bundles from one node to another.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Send {
    /// Seconds after the start.
    pub at_s: f64,
    /// The source.
    pub from: String,
    /// The destination.
    pub to: String,
    /// How many bundles, each with its own payload.
    #[serde(default = "one")]
    pub count: u32,
    /// The copy budget of each.
    #[serde(default = "two")]
    pub copies: u16,
    /// The lifetime of each, in seconds.
    #[serde(default = "lifetime_default")]
    pub lifetime_s: f64,
    /// Data symbols per erasure block.
    #[serde(default = "four")]
    pub k: u8,
    /// Parity symbols per erasure block.
    #[serde(default = "two8")]
    pub m: u8,
    /// The slice size log (slices of 1 KiB to 16 KiB). The default, 4 (16 KiB slices), keeps a 1 MiB bundle inside
    /// vinc-node's 64-interval reception cap; smaller slices make more erasure blocks, so more disjoint verified
    /// ranges, and a large bundle overflows that cap (see the PR's gaps).
    #[serde(default = "four8")]
    pub slice_log: u8,
}

fn one() -> u32 {
    1
}
fn two() -> u16 {
    2
}
fn two8() -> u8 {
    2
}
fn four() -> u8 {
    4
}
fn four8() -> u8 {
    4
}
fn lifetime_default() -> f64 {
    300.0
}

/// A contact window between two nodes.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Window {
    /// One node.
    pub a: String,
    /// The other.
    pub b: String,
    /// Opens, seconds after the start.
    pub from_s: f64,
    /// Closes.
    pub to_s: f64,
}

/// A custody move that must happen.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Move {
    /// The node relieved.
    pub from: String,
    /// The new custodian.
    pub to: String,
}

/// A rule checked against the nodes' logs.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "rule", rename_all = "kebab-case")]
pub enum Check {
    /// Every bundle sent to `to` was opened there once, intact; through `via` if named; not before `after_s`.
    Delivered {
        /// The destination.
        to: String,
        /// The carrier the last transfer came from.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        via: Option<String>,
        /// The earliest second after the start a delivery may happen.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        after_s: Option<f64>,
    },
    /// No bundle sent to `to` was opened there.
    NotDelivered {
        /// The destination.
        to: String,
    },
    /// Every relief of custody is a verified acknowledgement from a node that took custody first and ranks above;
    /// the moves listed happen.
    Custody {
        /// Moves that must happen.
        #[serde(default)]
        moves: Vec<Move>,
    },
    /// No more holders than the copy budget; every node hands on fewer copies than it received.
    Copies,
    /// The reception at `at` never asks again for a symbol it verified.
    NoRefetch {
        /// The receiver.
        at: String,
    },
    /// At least `min` transfers refused at `at` for `reason` (from `from`, if named).
    Refused {
        /// The refusing node.
        at: String,
        /// The reason: `no-room`, `bad-proof`, `expired`, `malformed`, ...
        reason: String,
        /// The fewest.
        #[serde(default = "one")]
        min: u32,
        /// The holder refused.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        from: Option<String>,
    },
    /// The store at `at` never held more sealed bytes than its budget.
    WithinBudget {
        /// The node.
        at: String,
    },
    /// Every node in `at` that held a bundle reported its expiry, not before its lifetime, and holds nothing at the
    /// end.
    Expired {
        /// The nodes.
        at: Vec<String>,
    },
    /// What `at` restored from its kept store over its restarts.
    Restored {
        /// The node.
        at: String,
        /// The fewest records dropped.
        #[serde(default)]
        dropped_min: u64,
        /// The fewest bundles held again.
        #[serde(default)]
        held_min: u64,
        /// The most bundles held again.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        held_max: Option<u64>,
    },
}

/// The test id of one size.
pub fn id(size: u64) -> String {
    format!("dtn_{}", crate::workloads::size_id(size))
}

impl Dtn {
    /// The sealed size of a bundle of `size` payload bytes under the first send's code, for budgets.
    pub fn sealed_len(&self, size: u64) -> Option<u64> {
        let s = self.sends.first()?;
        vinc_dtn::layout::SliceLayout::new(s.k, s.m, s.slice_log, size)
            .ok()
            .map(|l| l.total_len())
    }

    /// The settings of node `name`, if it has its own.
    pub fn node(&self, name: &str) -> Option<&DtnNode> {
        self.nodes.iter().find(|n| n.name == name)
    }

    pub(crate) fn check(&self, sc: &Scenario, nodes: &BTreeMap<&str, &NodeSpec>, out: &mut Vec<Problem>) {
        let mut name = |path: String, n: &str| {
            if !nodes.contains_key(n) {
                out.push(Problem::new(path, "no node has this name"));
            }
        };
        for (i, s) in self.sends.iter().enumerate() {
            name(format!("workload.sends[{i}].from"), &s.from);
            name(format!("workload.sends[{i}].to"), &s.to);
        }
        for (i, w) in self.contacts.iter().enumerate() {
            name(format!("workload.contacts[{i}].a"), &w.a);
            name(format!("workload.contacts[{i}].b"), &w.b);
        }
        for (i, n) in self.nodes.iter().enumerate() {
            name(format!("workload.nodes[{i}].name"), &n.name);
        }
        for (i, c) in self.checks.iter().enumerate() {
            for n in c.names() {
                name(format!("workload.checks[{i}]"), n);
            }
        }
        if self.sends.is_empty() {
            out.push(Problem::new("workload.sends", "send at least one bundle"));
        }
        if self.checks.is_empty() {
            out.push(Problem::new("workload.checks", "check at least one rule"));
        }
        for (i, s) in self.sends.iter().enumerate() {
            let p = format!("workload.sends[{i}]");
            if s.from == s.to {
                out.push(Problem::new(p.clone(), "a bundle goes to another node"));
            }
            if s.copies == 0 || !(1..=16).contains(&s.count) {
                out.push(Problem::new(p.clone(), "use 1 to 16 bundles of at least one copy"));
            }
            if s.k == 0 || usize::from(s.k) + usize::from(s.m) > 255 || s.slice_log > 4 {
                out.push(Problem::new(
                    p.clone(),
                    "use k of 1 or more, k + m up to 255, a slice log of 0 to 4",
                ));
            }
            if !(s.at_s.is_finite() && s.at_s >= 0.0 && s.lifetime_s.is_finite() && s.lifetime_s >= 1.0) {
                out.push(Problem::new(
                    p,
                    "use a start of 0 s or more and a lifetime of 1 s or more",
                ));
            }
        }
        for (i, w) in self.contacts.iter().enumerate() {
            if w.a == w.b || !(w.from_s.is_finite() && w.to_s.is_finite() && 0.0 <= w.from_s && w.from_s < w.to_s) {
                out.push(Problem::new(
                    format!("workload.contacts[{i}]"),
                    "a window is between two nodes and opens before it closes",
                ));
            }
        }
        if self
            .nodes
            .iter()
            .any(|n| n.budget_bundles.is_some_and(|b| !(b.is_finite() && b > 0.0)))
        {
            out.push(Problem::new(
                "workload.nodes",
                "a budget is a positive number of bundles",
            ));
        }
        let room = u64::from(sc.resources.memory_mib) * (1 << 20) / 10;
        for (i, s) in self.sizes.iter().enumerate() {
            if !(8..=room.min(16 << 20)).contains(s) {
                out.push(Problem::new(
                    format!("workload.sizes[{i}]"),
                    "use 8 bytes up to 16 MiB and 10% of a node's memory",
                ));
            }
        }
        if self.sizes.is_empty() {
            out.push(Problem::new("workload.sizes", "add at least one size"));
        }
        if !(self.duration_s.is_finite() && (1.0..=3600.0).contains(&self.duration_s)) {
            out.push(Problem::new("workload.duration_s", "use 1 to 3600 seconds"));
        }
        if !self.baseline && sc.stacks.iter().any(|s| *s != Stack::Vinc) {
            out.push(Problem::new(
                "stacks",
                "only VINC has delay-tolerant delivery; set workload.baseline to run the others without it",
            ));
        }
        crate::workloads::check_group(sc, nodes, out);
    }
}

impl Check {
    fn names(&self) -> Vec<&str> {
        match self {
            Self::Delivered { to, via, .. } => [Some(to.as_str()), via.as_deref()].into_iter().flatten().collect(),
            Self::NotDelivered { to } => vec![to],
            Self::Custody { moves } => moves.iter().flat_map(|m| [m.from.as_str(), m.to.as_str()]).collect(),
            Self::Copies => vec![],
            Self::NoRefetch { at } | Self::WithinBudget { at } | Self::Restored { at, .. } => vec![at],
            Self::Refused { at, from, .. } => [Some(at.as_str()), from.as_deref()].into_iter().flatten().collect(),
            Self::Expired { at } => at.iter().map(String::as_str).collect(),
        }
    }
}

/// A bundle the orchestrator sent.
#[derive(Debug, Clone, PartialEq)]
pub struct Sent {
    /// Its tag.
    pub bundle: String,
    /// The source.
    pub from: String,
    /// The destination.
    pub to: String,
    /// The copy budget.
    pub copies: u16,
    /// When it was made (wall clock, ms).
    pub at_ms: u64,
    /// Its lifetime in ms.
    pub lifetime_ms: u64,
}

/// What the checks found: the failures, and the numbers for the row.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Outcome {
    /// One sentence per failed check.
    pub failures: Vec<String>,
    /// Checks that passed.
    pub passed: u32,
    /// The numbers.
    pub metrics: Map<String, Value>,
}

/// The logs of every node, every life of its program in order.
pub type Logs = BTreeMap<String, Vec<DtnReport>>;

fn entries<'a>(logs: &'a Logs, node: &str) -> impl Iterator<Item = (u64, &'a str, &'a DtnWhat)> + 'a {
    logs.get(node)
        .into_iter()
        .flatten()
        .flat_map(|r| r.log.iter().map(|e| (e.ms, e.bundle.as_str(), &e.what)))
}

fn median(mut v: Vec<f64>) -> Option<f64> {
    v.sort_by(f64::total_cmp);
    let n = v.len();
    if n == 0 {
        return None;
    }
    let mid = |i: usize| v.get(i).copied();
    if n % 2 == 1 {
        mid(n / 2)
    } else {
        mid(n / 2 - 1).zip(mid(n / 2)).map(|(a, b)| f64::midpoint(a, b))
    }
}

/// Read the logs against the checks. `rank` gives a node's id bytes (custody moves up their order); `t0_ms` is the
/// start.
#[allow(clippy::too_many_lines, reason = "one arm per rule, read top to bottom")]
pub fn evaluate(
    checks: &[Check],
    sent: &[Sent],
    logs: &Logs,
    t0_ms: u64,
    rank: impl Fn(&str) -> Option<[u8; 32]>,
) -> Outcome {
    let mut o = Outcome::default();
    let dropped: u64 = logs.values().flatten().map(|r| r.lost).sum();
    if dropped > 0 {
        o.failures.push(format!(
            "the nodes dropped {dropped} trace records, so the logs prove nothing"
        ));
        return o;
    }
    let mut delays = Vec::new();
    let mut delivered = 0u32;
    let mut holders_max = 0usize;
    for c in checks {
        let before = o.failures.len();
        match c {
            Check::Delivered { to, via, after_s } => {
                for s in sent.iter().filter(|s| &s.to == to) {
                    let got: Vec<(u64, bool)> = entries(logs, to)
                        .filter_map(|(ms, b, w)| match w {
                            DtnWhat::Received { intact, .. } if b == s.bundle => Some((ms, *intact)),
                            _ => None,
                        })
                        .collect();
                    match got.as_slice() {
                        [(ms, true)] => {
                            delivered += 1;
                            #[allow(clippy::cast_precision_loss)]
                            delays.push(ms.saturating_sub(s.at_ms) as f64 / 1000.0);
                            #[allow(clippy::cast_precision_loss, reason = "milliseconds since the start")]
                            if let Some(a) = after_s
                                && (ms.saturating_sub(t0_ms) as f64) < a * 1000.0
                            {
                                o.failures.push(format!(
                                    "{to} opened {} before {a} s, while it was to be away",
                                    s.bundle
                                ));
                            }
                            let last_from = entries(logs, to)
                                .filter_map(|(_, b, w)| match w {
                                    DtnWhat::Complete { peer } if b == s.bundle => Some(peer.as_str()),
                                    _ => None,
                                })
                                .last();
                            if let Some(v) = via
                                && last_from != Some(v.as_str())
                            {
                                o.failures.push(format!(
                                    "{} reached {to} from {}, not through the carrier {v}",
                                    s.bundle,
                                    last_from.unwrap_or("nobody")
                                ));
                            }
                        }
                        [] => o
                            .failures
                            .push(format!("{} from {} never reached {to}", s.bundle, s.from)),
                        [(_, false)] => o.failures.push(format!("{} reached {to} corrupted", s.bundle)),
                        more => o
                            .failures
                            .push(format!("{} was opened {} times at {to}", s.bundle, more.len())),
                    }
                }
            }
            Check::NotDelivered { to } => {
                for s in sent.iter().filter(|s| &s.to == to) {
                    if entries(logs, to).any(|(_, b, w)| b == s.bundle && matches!(w, DtnWhat::Received { .. })) {
                        o.failures.push(format!("{} reached {to}, which it must not", s.bundle));
                    }
                }
            }
            Check::Custody { moves } => {
                for node in logs.keys() {
                    for (ms, b, w) in entries(logs, node) {
                        let DtnWhat::HandedOff { to } = w else { continue };
                        let took = entries(logs, to).any(|(t, b2, w2)| {
                            b2 == b && t <= ms + 1000 && matches!(w2, DtnWhat::Custody { peer } if peer == node)
                        });
                        let acked = entries(logs, node).any(|(_, b2, w2)| {
                            b2 == b && matches!(w2, DtnWhat::Acked { peer, relieved: true } if peer == to)
                        });
                        if !took || !acked {
                            o.failures.push(format!(
                                "{node} was relieved of {b} without {to} taking custody and acknowledging it"
                            ));
                        }
                        match (rank(node), rank(to)) {
                            (Some(a), Some(c)) if c > a => {}
                            _ => o
                                .failures
                                .push(format!("custody of {b} moved from {node} down to {to}")),
                        }
                    }
                }
                for m in moves {
                    if !entries(logs, &m.from).any(|(_, _, w)| matches!(w, DtnWhat::HandedOff { to } if *to == m.to)) {
                        o.failures
                            .push(format!("custody never moved from {} to {}", m.from, m.to));
                    }
                }
            }
            Check::Copies => {
                for s in sent {
                    let mut holders: BTreeSet<&str> = BTreeSet::from([s.from.as_str()]);
                    for node in logs.keys().filter(|n| **n != s.to) {
                        if entries(logs, node).any(|(_, b, w)| b == s.bundle && matches!(w, DtnWhat::Custody { .. })) {
                            holders.insert(node);
                        }
                    }
                    holders_max = holders_max.max(holders.len());
                    if holders.len() > usize::from(s.copies) {
                        o.failures.push(format!(
                            "{} had {} holders with a budget of {} copies",
                            s.bundle,
                            holders.len(),
                            s.copies
                        ));
                    }
                    for node in logs.keys() {
                        let mut handed: BTreeMap<&str, u64> = BTreeMap::new();
                        let mut got = 0;
                        for n in logs.keys() {
                            for (_, b, w) in entries(logs, n) {
                                if let DtnWhat::Offer { peer, copies } = w
                                    && b == s.bundle
                                {
                                    if n == node && *peer != s.to {
                                        let h = handed.entry(peer.as_str()).or_default();
                                        *h = (*h).max(*copies);
                                    }
                                    if peer == node {
                                        got = got.max(*copies);
                                    }
                                }
                            }
                        }
                        let received = if *node == s.from { u64::from(s.copies) } else { got };
                        let out: u64 = handed.values().sum();
                        if out > 0 && out >= received {
                            o.failures.push(format!(
                                "{node} handed on {out} copies of {} having received {received}",
                                s.bundle
                            ));
                        }
                    }
                }
            }
            Check::NoRefetch { at } => {
                for life in logs.get(at).into_iter().flatten() {
                    let mut seen = BTreeSet::new();
                    for e in &life.log {
                        if let DtnWhat::Symbols { first, .. } = e.what
                            && !seen.insert((e.bundle.as_str(), first))
                        {
                            o.failures
                                .push(format!("{at} asked again for symbol {first} of {}", e.bundle));
                        }
                    }
                }
                let peers: BTreeSet<&str> = entries(logs, at)
                    .filter_map(|(_, _, w)| match w {
                        DtnWhat::Symbols { peer, .. } => Some(peer.as_str()),
                        _ => None,
                    })
                    .collect();
                o.metrics.insert("served_by".into(), json!(peers.len()));
            }
            Check::Refused { at, reason, min, from } => {
                let n = entries(logs, at)
                    .filter(|(_, _, w)| {
                        matches!(w, DtnWhat::Refused { peer, reason: r }
                            if r == reason && from.as_ref().is_none_or(|f| f == peer))
                    })
                    .count();
                o.metrics.insert("refused".into(), json!(n));
                if n < *min as usize {
                    o.failures
                        .push(format!("{at} refused {n} transfers for {reason}, fewer than {min}"));
                }
            }
            Check::WithinBudget { at } => {
                for r in logs.get(at).into_iter().flatten() {
                    if r.peak_bytes > r.budget {
                        o.failures.push(format!(
                            "{at} held {} bytes with a budget of {}",
                            r.peak_bytes, r.budget
                        ));
                    }
                }
            }
            Check::Expired { at } => {
                for node in at {
                    for s in sent {
                        let held = entries(logs, node).any(|(_, b, w)| {
                            b == s.bundle && matches!(w, DtnWhat::Created { .. } | DtnWhat::Custody { .. })
                        });
                        if !held {
                            continue;
                        }
                        match entries(logs, node)
                            .find(|(_, b, w)| *b == s.bundle && matches!(w, DtnWhat::Expired))
                            .map(|(ms, ..)| ms)
                        {
                            None => o.failures.push(format!("{node} never reported {} expired", s.bundle)),
                            Some(ms) if ms + 1000 < s.at_ms + s.lifetime_ms => o.failures.push(format!(
                                "{node} ended {} {} ms before its lifetime",
                                s.bundle,
                                s.at_ms + s.lifetime_ms - ms
                            )),
                            Some(_) => {}
                        }
                    }
                    if logs.get(node).and_then(|l| l.last()).is_some_and(|r| r.held > 0) {
                        o.failures
                            .push(format!("{node} still holds bundles after they expired"));
                    }
                }
            }
            Check::Restored {
                at,
                dropped_min,
                held_min,
                held_max,
            } => {
                let sum = |i: usize| -> u64 {
                    logs.get(at)
                        .into_iter()
                        .flatten()
                        .map(|r| r.restored.get(i).copied().unwrap_or(0))
                        .sum()
                };
                let (held, dropped) = (sum(0), sum(3));
                o.metrics.insert("restored_held".into(), json!(held));
                o.metrics.insert("restored_dropped".into(), json!(dropped));
                if dropped < *dropped_min || held < *held_min || held_max.is_some_and(|m| held > m) {
                    o.failures
                        .push(format!("{at} restored {held} bundles and dropped {dropped} records"));
                }
            }
        }
        if o.failures.len() == before {
            o.passed += 1;
        }
    }
    let delivering = checks.iter().any(|c| matches!(c, Check::Delivered { .. }));
    if delivering {
        #[allow(clippy::cast_precision_loss)]
        let share = f64::from(delivered) / sent.len().max(1) as f64;
        o.metrics.insert("delivered".into(), json!(share));
    }
    if let Some(d) = median(delays) {
        o.metrics.insert("delivery_s".into(), json!(d));
    }
    if holders_max > 0 {
        o.metrics.insert("holders".into(), json!(holders_max));
    }
    o
}

/// Whether a node with `role` runs the layer in this workload: every peer does, hubs and relays do not.
pub fn runs_layer(role: Role) -> bool {
    role == Role::Peer
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::node::proto::DtnEntry;

    fn life(entries: &[(u64, DtnWhat)]) -> Vec<DtnReport> {
        vec![DtnReport {
            log: entries
                .iter()
                .map(|(ms, what)| DtnEntry {
                    ms: *ms,
                    bundle: "b".into(),
                    what: what.clone(),
                })
                .collect(),
            ..DtnReport::default()
        }]
    }

    /// A relief with no custody taken, a spray past the budget and a refetch are each caught; a clean log passes.
    #[test]
    fn broken_rules_are_caught_and_a_clean_log_passes() {
        let sent = [Sent {
            bundle: "b".into(),
            from: "s".into(),
            to: "d".into(),
            copies: 2,
            at_ms: 0,
            lifetime_ms: 60_000,
        }];
        let offer = |peer: &str, copies| DtnWhat::Offer {
            peer: peer.into(),
            copies,
        };
        let mut logs: Logs = BTreeMap::new();
        logs.insert(
            "s".into(),
            life(&[
                (1, DtnWhat::Created { copies: 2 }),
                (2, offer("x", 1)),
                (3, offer("y", 1)),
            ]),
        );
        logs.insert("x".into(), life(&[(2, DtnWhat::Custody { peer: "s".into() })]));
        logs.insert("y".into(), life(&[(3, DtnWhat::Custody { peer: "s".into() })]));
        let rank = |n: &str| Some([n.as_bytes().first().copied().unwrap_or(0); 32]);
        let o = evaluate(&[Check::Copies], &sent, &logs, 0, rank);
        assert_eq!(o.failures.len(), 2, "{:?}", o.failures);

        logs.remove("y");
        if let Some(s) = logs.get_mut("s") {
            *s = life(&[
                (1, DtnWhat::Created { copies: 2 }),
                (2, offer("x", 1)),
                (5, DtnWhat::HandedOff { to: "x".into() }),
            ]);
        }
        let o = evaluate(
            &[Check::Copies, Check::Custody { moves: vec![] }],
            &sent,
            &logs,
            0,
            rank,
        );
        assert_eq!(o.failures.len(), 1, "an unacknowledged relief: {:?}", o.failures);

        if let Some(s) = logs.get_mut("s") {
            *s = life(&[
                (1, DtnWhat::Created { copies: 2 }),
                (2, offer("x", 1)),
                (
                    4,
                    DtnWhat::Acked {
                        peer: "x".into(),
                        relieved: true,
                    },
                ),
                (5, DtnWhat::HandedOff { to: "x".into() }),
            ]);
        }
        let sym = |first| DtnWhat::Symbols {
            peer: "x".into(),
            first,
        };
        logs.insert("d".into(), life(&[(6, sym(0)), (7, sym(16)), (8, sym(0))]));
        let checks = [
            Check::Copies,
            Check::Custody { moves: vec![] },
            Check::NoRefetch { at: "d".into() },
        ];
        let o = evaluate(&checks, &sent, &logs, 0, rank);
        assert_eq!(o.failures.len(), 1, "a refetch: {:?}", o.failures);
        assert_eq!(o.passed, 2);
    }
}
