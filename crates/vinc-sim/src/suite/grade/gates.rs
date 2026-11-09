//! The validity gates, evaluated on one finished run.
//!
//! [`evaluate_gates`] follows the reference evaluation order exactly, because one gate (G-NOPUNCH) reads which gates
//! had failed so far. G-DET is decided by the caller from two trace hashes ([`gate_det`]). A gate the run cannot
//! decide (G-AWARE without a membership layer, G-SEC with unattributed key provenance) is reported as
//! [`GateStatus::NotEvaluated`] unless a definite failure was already found; it never reads as a pass.
//!
//! Invariant: at most three distinct messages are kept per failed gate, the recorder's own violations come first.

use std::collections::BTreeMap;

use super::{NodeFacts, RunFacts};
use crate::suite::rec::{HOUR, MemberKind, NS, Rec};
use crate::suite::world::model::{ChangeKind, Cut, IntentKind, Param, World};

/// The gate names in the reference order.
pub const GATES: [&str; 15] = [
    "G-DET",
    "G-INT",
    "G-SIZE",
    "G-ORDER",
    "G-SEC",
    "G-ACP",
    "G-LIVE",
    "G-NOPUNCH",
    "G-MEDIUM",
    "G-AWARE",
    "G-CONNECT",
    "G-BOUND",
    "G-SPEC",
    "G-SURFACE",
    "G-PROV",
];

const KIB: u64 = 1024;
const MIB: u64 = 1024 * KIB;

/// The verdict on one gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateStatus {
    /// Checked and held.
    Pass,
    /// Violated; the first (at most three) distinct messages.
    Fail(Vec<String>),
    /// The gate does not apply to this scenario.
    NotApplicable,
    /// Decided by the caller (G-DET), not yet decided.
    Pending,
    /// Could not be decided because the run lacks something the gate needs; the reason says what.
    NotEvaluated(String),
}

/// The verdicts of all gates of one run, in [`GATES`] order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateReport {
    /// `(gate, verdict)` in [`GATES`] order.
    pub gates: Vec<(&'static str, GateStatus)>,
}

impl GateReport {
    /// The verdict of `gate`.
    pub fn status(&self, gate: &str) -> Option<&GateStatus> {
        self.gates.iter().find(|(g, _)| *g == gate).map(|(_, s)| s)
    }

    /// The gates that failed.
    pub fn failed(&self) -> Vec<&'static str> {
        self.gates
            .iter()
            .filter(|(_, s)| matches!(s, GateStatus::Fail(_)))
            .map(|(g, _)| *g)
            .collect()
    }

    /// The gates that could not be decided, with the reason.
    pub fn not_evaluated(&self) -> Vec<(&'static str, &str)> {
        self.gates
            .iter()
            .filter_map(|(g, s)| match s {
                GateStatus::NotEvaluated(r) => Some((*g, r.as_str())),
                _ => None,
            })
            .collect()
    }

    /// Sets the verdict of `gate`.
    pub fn set(&mut self, gate: &str, status: GateStatus) {
        if let Some(slot) = self.gates.iter_mut().find(|(g, _)| *g == gate) {
            slot.1 = status;
        }
    }

    /// True when no gate failed and none is undecided apart from the pending G-DET: the run is valid so far.
    pub fn all_clear(&self) -> bool {
        self.gates.iter().all(|(g, s)| match s {
            GateStatus::Pass | GateStatus::NotApplicable => true,
            GateStatus::Pending => *g == "G-DET",
            GateStatus::Fail(_) | GateStatus::NotEvaluated(_) => false,
        })
    }
}

/// G-DET from the trace hashes of two runs of the same world in separate processes.
pub fn gate_det(first: &str, second: &str) -> GateStatus {
    if first == second {
        GateStatus::Pass
    } else {
        GateStatus::Fail(vec![
            "two runs gave different traces (iteration order or hash dependence?)".to_owned(),
        ])
    }
}

type Details = BTreeMap<&'static str, Vec<String>>;

fn gate_name(g: &str) -> Option<&'static str> {
    GATES.iter().copied().find(|x| *x == g)
}

fn fail(details: &mut Details, gate: &'static str, msg: &str) {
    let lst = details.entry(gate).or_default();
    if lst.len() < 3 && !lst.iter().any(|m| m == msg) {
        lst.push(msg.to_owned());
    }
}

fn device_cap(device: &str) -> u64 {
    match device {
        "embedded" => 4 * MIB,
        "mcu" => 32 * KIB,
        "phone" | "browser" => 16 * MIB,
        _ => 64 * MIB,
    }
}

fn param_truthy(world: &World, key: &str) -> bool {
    match world.params.get(key) {
        Some(Param::Bool(b)) => *b,
        Some(Param::Int(i)) => *i != 0,
        Some(Param::Float(f)) => *f != 0.0,
        _ => false,
    }
}

/// Were the sites `sa` and `sb` partitioned apart at some moment in `[t0, t1]`?
fn cut_between(cuts: &[Cut], t0: i128, t1: i128, sa: usize, sb: usize) -> bool {
    cuts.iter().any(|c| {
        i128::from(c.from) <= t1
            && i128::from(c.to) >= t0
            && ((c.x.contains(&sa) && c.y.contains(&sb)) || (c.x.contains(&sb) && c.y.contains(&sa)))
    })
}

fn cut(world: &World, a: usize, b: usize, t0: i128, t1: i128) -> bool {
    match (world.nodes.get(a), world.nodes.get(b)) {
        (Some(na), Some(nb)) => cut_between(&world.partitions, t0, t1, na.site, nb.site),
        _ => false,
    }
}

/// Does a membership event of this kind answer a change of this kind? (`crash` here also accepts the weaker events;
/// the completeness check excludes them again.)
pub(crate) fn matching(change: ChangeKind, ev: MemberKind) -> bool {
    match change {
        ChangeKind::Join => ev == MemberKind::Joined,
        ChangeKind::Leave => matches!(ev, MemberKind::Left | MemberKind::ConfirmedDown),
        ChangeKind::Crash => {
            matches!(
                ev,
                MemberKind::Suspected | MemberKind::ConfirmedDown | MemberKind::Left | MemberKind::Joined
            )
        }
        ChangeKind::Addr => ev == MemberKind::AddressChanged,
        ChangeKind::Stack => ev == MemberKind::StackChanged,
        ChangeKind::Revoke => ev == MemberKind::Revoked,
    }
}

/// The base round trip of two nodes at the end of the run: twice the one-way path delay.
fn base_rtt(world: &World, facts: &RunFacts, a: usize, z: usize) -> Option<u64> {
    let sa = world.sites.get(facts.nodes.get(a)?.site)?;
    let sz = world.sites.get(facts.nodes.get(z)?.site)?;
    let region = world.region_delay_ns.get(sa.region)?.get(sz.region)?;
    Some(2 * (sa.up_delay_ns + region + sz.down_delay_ns))
}

/// A member up for more than 20 s at `t`.
fn settled(rec: &Rec, m: usize, t: u64) -> bool {
    rec.alive_iv
        .get(&m)
        .and_then(|iv| iv.iter().find(|&&(a, b)| a <= t && b.is_none_or(|b| t < b)))
        .is_some_and(|&(a, _)| t - a > 20 * NS)
}

/// Evaluates every gate of one finished run. G-DET is `Pending`; G-SIZE is `NotApplicable` outside S11 and G-NOPUNCH
/// unless the scenario forbids punching.
pub fn evaluate_gates(world: &World, rec: &Rec, facts: &RunFacts) -> GateReport {
    let mut d = Details::new();
    for v in &rec.violations {
        if let Some(g) = gate_name(&v.gate) {
            fail(&mut d, g, &v.msg);
        }
    }
    completion(world, rec, &mut d);
    if world.id == "S11" {
        size(world, rec, facts, &mut d);
    }
    sec(rec, facts, &mut d);
    let no_punch = param_truthy(world, "no_punch");
    if no_punch {
        if rec.punched_paths != 0 {
            fail(
                &mut d,
                "G-NOPUNCH",
                "a punched path existed although punching was impossible (harness)",
            );
        }
        // The reference reads the other gates' failures at this point of its evaluation order: the gates below
        // (G-AWARE, G-BOUND, G-SURFACE, G-PROV) are not yet decided here, and are not counted.
        if d.keys().any(|g| *g != "G-NOPUNCH") {
            fail(&mut d, "G-NOPUNCH", "the no-hole-punching scenario fails another gate");
        }
    }
    if facts.has_membership {
        aware(world, rec, facts, &mut d);
    }
    bound(world, rec, facts, &mut d);
    surface(world, rec, facts, &mut d);
    if !facts.prov_clean {
        fail(&mut d, "G-PROV", "the static provenance check failed");
    }

    let mut report = GateReport {
        gates: GATES.iter().map(|g| (*g, GateStatus::Pass)).collect(),
    };
    for (g, msgs) in &d {
        report.set(g, GateStatus::Fail(msgs.clone()));
    }
    report.set("G-DET", GateStatus::Pending);
    if !no_punch {
        report.set("G-NOPUNCH", GateStatus::NotApplicable);
    }
    if world.id != "S11" {
        report.set("G-SIZE", GateStatus::NotApplicable);
    }
    if !facts.has_membership && !d.contains_key("G-AWARE") {
        report.set(
            "G-AWARE",
            GateStatus::NotEvaluated("the run has no membership layer".to_owned()),
        );
    }
    if facts.sec.unknown_provenance != 0 && !d.contains_key("G-SEC") {
        report.set(
            "G-SEC",
            GateStatus::NotEvaluated(
                "the provenance of some keys is unknown, so the key verdict is undecided".to_owned(),
            ),
        );
    }
    report
}

/// G-INT, G-LIVE, G-ORDER and G-CONNECT: completion of the must intents.
fn completion(world: &World, rec: &Rec, d: &mut Details) {
    let mut undelivered = [0u64; 7];
    for it in rec.intents.values() {
        match it.kind {
            IntentKind::Fetch => {
                if it.must && !it.delivered.contains_key(&it.node) {
                    undelivered[IntentKind::Fetch as usize] += 1;
                }
            }
            IntentKind::Echo => {
                if it.must && !echo_connected_in_time(world, rec, it.iid) {
                    undelivered[IntentKind::Echo as usize] += 1;
                }
            }
            kind => {
                for r in it.must_set.iter().filter(|&&r| r != it.node) {
                    let late = match it.delivered.get(r) {
                        None => true,
                        Some(t) => it.deadline.is_some_and(|dl| *t > dl),
                    };
                    if late {
                        undelivered[kind as usize] += 1;
                    }
                }
            }
        }
    }
    let n = |k: IntentKind| undelivered[k as usize];
    if n(IntentKind::Fetch) != 0 {
        fail(
            d,
            "G-INT",
            "a value was not completely delivered although a path existed long enough",
        );
        fail(
            d,
            "G-LIVE",
            "value transfers made no complete progress within the liveness bound",
        );
    }
    for (k, name) in [
        (IntentKind::Push, "push"),
        (IntentKind::Publish, "publish"),
        (IntentKind::Docsync, "docsync"),
        (IntentKind::Manage, "manage"),
        (IntentKind::Reconcile, "reconcile"),
    ] {
        if n(k) != 0 {
            fail(
                d,
                "G-LIVE",
                &format!("{name} intents undelivered within their bound while a path existed"),
            );
        }
    }
    if n(IntentKind::Echo) != 0 {
        fail(
            d,
            "G-CONNECT",
            "Connect(peer_id, proto_id) with no hints did not connect within the deadline",
        );
    }
    for seqs in rec.pushlog_order.values() {
        if seqs.windows(2).any(|w| w[1] != w[0] + 1) {
            fail(d, "G-ORDER", "ordered pushes not delivered in sequence exactly once");
            break;
        }
    }
    if n(IntentKind::Push) != 0 {
        fail(d, "G-ORDER", "ordered pushes missing at a replicator");
    }
}

/// A must echo connected within `max(connect deadline, intent deadline - t)` of its intent (shared with C4).
pub(crate) fn echo_connected_in_time(world: &World, rec: &Rec, iid: u32) -> bool {
    let Some(it) = rec.intents.get(&iid) else { return false };
    let Some(c) = rec.echo.get(&iid).and_then(|e| e.connected) else {
        return false;
    };
    let allowed = world
        .connect_deadline_ns
        .max(it.deadline.unwrap_or(it.t).saturating_sub(it.t));
    i128::from(c) - i128::from(it.t) <= i128::from(allowed)
}

/// G-SIZE (S11): every must fetch completes and no node's state peak exceeds 64 MiB.
fn size(world: &World, rec: &Rec, facts: &RunFacts, d: &mut Details) {
    if rec
        .intents
        .values()
        .any(|it| it.kind == IntentKind::Fetch && it.must && !it.delivered.contains_key(&it.node))
    {
        fail(d, "G-SIZE", "a value size class did not complete");
    }
    for i in 0..world.nodes.len() {
        if facts.state_peak(rec, i).unwrap_or(0) > 64 * MIB {
            fail(d, "G-SIZE", "memory held for a transfer grows with the value size");
        }
    }
}

/// G-SEC: the key verdicts, plaintext payload, nonce reuse and amplification.
fn sec(rec: &Rec, facts: &RunFacts, d: &mut Details) {
    if facts.sec.hndl_known_payload_keys != 0 {
        fail(
            d,
            "G-SEC",
            "payload readable by the harvest-now-decrypt-later adversary (H12)",
        );
    }
    if facts.sec.forward_secrecy_broken != 0 {
        fail(
            d,
            "G-SEC",
            "sessions before a key compromise are readable (forward secrecy)",
        );
    }
    if !rec.plaintext_payload.is_empty() || !facts.sec.plaintext_payload.is_empty() {
        fail(d, "G-SEC", "payload sent in plaintext on the wire");
    }
    if facts.sec.nonce_reuse != 0 {
        fail(d, "G-SEC", "AEAD nonce reused under one key with different content");
    }
    for &[rx, tx] in rec.amp.values() {
        if tx > 3 * rx.max(1) {
            fail(
                d,
                "G-SEC",
                "more than 3x the received bytes sent to an unvalidated address",
            );
        }
    }
}

/// G-AWARE: completeness, accuracy and convergence (epochs are recorded by the recorder).
fn aware(world: &World, rec: &Rec, facts: &RunFacts, d: &mut Details) {
    let end = rec.end;
    let b = facts.awareness_bound_ns.min(world.awareness_bound_cap_ns);
    let rate_bound = facts.false_suspicion_per_member_hour.min(world.false_suspicion_cap);
    let (bi, endi) = (i128::from(b), i128::from(end));
    let n = world.nodes.len();
    let mut by = BTreeMap::<(usize, usize), Vec<(u64, MemberKind, Option<u64>)>>::new();
    for m in &rec.membership {
        if let Some(member) = m.member {
            by.entry((m.node, member)).or_default().push((m.t, m.kind, m.extra));
        }
    }
    let denied = &rec.denied;
    'change: for ch in &rec.changes {
        let (t0, kind, x) = (ch.t, ch.kind, ch.node);
        if denied.contains(&x) || t0 + b > end {
            continue;
        }
        if matches!(kind, ChangeKind::Crash | ChangeKind::Leave) {
            let back = rec
                .alive_iv
                .get(&x)
                .and_then(|iv| iv.iter().find(|&&(a, _)| a > t0))
                .map(|&(a, _)| a);
            if back.is_some_and(|a| a < t0 + b) {
                continue;
            }
        }
        let (t0i, t1i) = (i128::from(t0), i128::from(t0 + b));
        for j in 0..n {
            if j == x || denied.contains(&j) || !rec.alive_through_i(j, t0i, t1i) {
                continue;
            }
            if rec.revoked.get(&j).copied().unwrap_or(end + 1) <= t0 + b {
                continue;
            }
            if kind != ChangeKind::Join
                && !(rec.alive_through_i(j, t0i - bi, t0i) && rec.alive_through_i(x, t0i - bi, t0i))
            {
                continue;
            }
            if matches!(kind, ChangeKind::Join | ChangeKind::Addr | ChangeKind::Stack) && rec.suspended_at_i(j, t1i) {
                continue;
            }
            if kind == ChangeKind::Join && rec.revoked.get(&x).copied().unwrap_or(end + 1) <= t0 + b {
                continue;
            }
            if cut(world, j, x, t0i - bi, t1i) {
                continue;
            }
            let ok = by.get(&(j, x)).is_some_and(|evs| {
                evs.iter().any(|&(t, k, ex)| {
                    let ti = i128::from(t);
                    t0i - i128::from(NS) <= ti
                        && ti <= t1i
                        && matching(kind, k)
                        && (kind != ChangeKind::Stack || ex == ch.version)
                        && !(kind == ChangeKind::Crash && matches!(k, MemberKind::Suspected | MemberKind::Joined))
                })
            });
            if !ok {
                let name = match kind {
                    ChangeKind::Join => "join",
                    ChangeKind::Crash => "crash",
                    ChangeKind::Leave => "leave",
                    ChangeKind::Stack => "stack",
                    ChangeKind::Revoke => "revoke",
                    ChangeKind::Addr => "addr",
                };
                fail(
                    d,
                    "G-AWARE",
                    &format!("a {name} was not reported to every live member within the stated bound"),
                );
                continue 'change;
            }
        }
    }
    // accuracy
    let false_n = rec
        .membership
        .iter()
        .filter(|m| matches!(m.kind, MemberKind::Suspected | MemberKind::ConfirmedDown))
        .filter(|m| {
            m.member.is_some_and(|x| {
                rec.alive_at(x, m.t)
                    && !rec.suspended_at(x, m.t)
                    && !denied.contains(&x)
                    && !rec.revoked.contains_key(&x)
                    && settled(rec, x, m.t)
                    && !cut(world, m.node, x, i128::from(m.t) - bi, i128::from(m.t))
            })
        })
        .count();
    let hours = (end as f64 / HOUR as f64).max(1e-9);
    let members = n.saturating_sub(denied.len()).max(1);
    if false_n as f64 / (members as f64 * hours) > rate_bound && false_n > 2 {
        fail(d, "G-AWARE", "false suspicions of live members above the stated rate");
    }
    convergence(rec, facts, n, b, endi, d);
}

fn convergence(rec: &Rec, facts: &RunFacts, n: usize, b: u64, endi: i128, d: &mut Details) {
    let end = rec.end;
    let denied = &rec.denied;
    let node = |i: usize| facts.nodes.get(i);
    let live: Vec<usize> = (0..n)
        .filter(|&j| {
            node(j).is_some_and(|f| f.alive_at_end && !f.suspended_at_end)
                && !denied.contains(&j)
                && !rec.revoked.contains_key(&j)
        })
        .collect();
    if live.is_empty() || endi <= i128::from(b) {
        return;
    }
    if !rec.changes.iter().all(|c| c.t <= end.saturating_sub(b)) {
        return;
    }
    let susp = |i: usize| node(i).is_some_and(|f: &NodeFacts| f.suspended_at_end);
    for &j in &live {
        let Some((_epoch, members)) = node(j).and_then(|f| f.view.as_ref()) else {
            fail(d, "G-AWARE", "view() did not return (epoch, members)");
            return;
        };
        if live.iter().any(|&i| i != j && !susp(i) && !members.contains(&i)) {
            fail(d, "G-AWARE", "membership views did not converge within a component");
            return;
        }
        let gone = |i: usize| (!node(i).is_some_and(|f| f.alive_at_end) || rec.revoked.contains_key(&i)) && !susp(i);
        if members.iter().any(|&i| i < n && gone(i)) {
            fail(d, "G-AWARE", "a view still lists departed, crashed or revoked members");
            return;
        }
    }
}

/// G-BOUND: node state peaks against the device-class caps, and soak growth.
fn bound(world: &World, rec: &Rec, facts: &RunFacts, d: &mut Details) {
    let n = world.nodes.len() as u64;
    let nfetch = rec.intents.values().filter(|it| it.kind == IntentKind::Fetch).count() as u64;
    for i in 0..world.nodes.len() {
        let peak = facts.state_peak(rec, i).unwrap_or(0);
        let device = facts.nodes.get(i).map_or_else(
            || world.nodes.get(i).map_or("", |nd| nd.device.as_str()),
            |f| f.device.as_str(),
        );
        let cap = if device == "cloud" {
            MIB + 16 * KIB * n + 256 * KIB * nfetch.max(1)
        } else {
            device_cap(device)
        };
        if peak > cap {
            fail(
                d,
                "G-BOUND",
                &format!("protocol state above the device-class cap ({device})"),
            );
            break;
        }
    }
    if world.soak
        && rec
            .state_thirds
            .values()
            .any(|&[_, b, c]| b != 0 && c > 2 * b + 64 * KIB)
    {
        fail(d, "G-BOUND", "protocol state keeps growing under steady load (soak)");
    }
}

/// G-SURFACE: a probe echo to a connected peer costs no extra round trip; opening a stream adds none either.
fn surface(world: &World, rec: &Rec, facts: &RunFacts, d: &mut Details) {
    let mut ratios = Vec::<f64>::new();
    for it in rec.intents.values().filter(|it| it.kind == IntentKind::Echo) {
        let e = rec.echo.get(&it.iid).copied().unwrap_or_default();
        if let (true, Some(c), Some(z)) = (it.meta.probe, e.connected, it.meta.to)
            && let Some(base) = base_rtt(world, facts, it.node, z)
            && i128::from(c) - i128::from(it.t) > i128::from(base / 2)
        {
            fail(
                d,
                "G-SURFACE",
                "a second protocol to an already connected peer added a round trip",
            );
        }
        if let (Some(w), Some(s), Some(&done)) = (e.written, e.served, it.delivered.get(&it.node)) {
            let fwd = i128::from(s) - i128::from(w);
            let back = i128::from(done) - i128::from(s);
            if back > 0 {
                ratios.push(fwd as f64 / back as f64);
            }
        }
    }
    if ratios.len() >= 5 {
        ratios.sort_by(f64::total_cmp);
        if ratios.get(ratios.len() / 2).is_some_and(|&m| m > 1.8) {
            fail(d, "G-SURFACE", "opening a stream added a round trip");
        }
    }
}
