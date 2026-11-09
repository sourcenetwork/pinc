//! The trace recorder: everything grading knows about a run, fed by explicit calls from the host.
//!
//! A [`Rec`] is the Rust form of the reference harness's recorder. Candidates never report numbers: the host tells
//! the recorder what crossed the wire, what the application observed and what the environment did, and the gates and
//! terms in [`crate::suite::grade`] are computed from the recorder alone (plus a few host facts).
//!
//! Invariants: every method takes the virtual time or id it needs as an argument and never reads a clock; the trace
//! hash is the blake2b-128 over exactly the `repr` text of the tuples the reference hashes, in call order, so two
//! runs of the same world give the same hash; no method panics on any input.

mod intent;
mod members;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::net::SocketAddr;
use std::rc::Rc;

use blake2::digest::consts::U16;
use blake2::{Blake2b, Digest};

pub use intent::{AsIntentKind, IntentMeta, IntentRec, MustArg, kind_name};
pub use members::{MemberEvent, MemberKind, MemberRec};

use crate::reference::Py;
use crate::suite::world::model::{Change, ChangeKind, IntentKind, World};

/// One second in nanoseconds.
pub const NS: u64 = 1_000_000_000;
/// One hour in nanoseconds.
pub const HOUR: u64 = 3600 * NS;

/// A kept violation: `(gate, node, message, time)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Violation {
    /// The gate name, e.g. `G-INT`.
    pub gate: String,
    /// The node that observed it.
    pub node: usize,
    /// The message.
    pub msg: String,
    /// When.
    pub t: u64,
}

/// Why a resume record was opened.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResumeKind {
    /// A suspension ended.
    Resume,
    /// A link returned (handover or outage end).
    Link,
    /// A restart that kept its state.
    Restart,
}

impl ResumeKind {
    /// The reference name.
    pub fn name(self) -> &'static str {
        match self {
            Self::Resume => "resume",
            Self::Link => "link",
            Self::Restart => "restart",
        }
    }
}

/// A resume record: the wire bytes a node sent between an event and its first application byte (C1, C2).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resume {
    /// The node.
    pub node: usize,
    /// When the event happened.
    pub t: u64,
    /// What kind of event.
    pub kind: ResumeKind,
    /// The first application byte at or after the event.
    pub first: Option<u64>,
    /// Wire bytes sent by the node until `first`.
    pub bytes: u64,
}

/// The timeline of one echo (G-SURFACE, G-CONNECT, C4).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EchoRec {
    /// When the protocol reported the connection (first report only).
    pub connected: Option<u64>,
    /// When the client wrote its request (last write).
    pub written: Option<u64>,
    /// When the server served it (first serve only).
    pub served: Option<u64>,
    /// When the echo returned to the client.
    pub done: Option<u64>,
}

/// An access answer: `(time asked, allow, valid until)`.
pub type AcpAnswer = (u64, bool, u64);

/// A store write of a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ValueEvent {
    /// When.
    pub t: u64,
    /// The writing node.
    pub node: usize,
    /// The value id.
    pub vid: u64,
    /// Offset of the write.
    pub off: u64,
    /// Length of the write.
    pub len: u64,
    /// Bytes that were not held before.
    pub new: u64,
}

/// The recorder. Field names are the reference recorder's attribute names in snake case.
#[derive(Debug)]
pub struct Rec {
    /// The scenario.
    pub world: Rc<World>,
    h: Blake2b<U16>,
    /// Kept violations (the first three per gate and message).
    pub violations: Vec<Violation>,
    /// How many times each `(gate, message)` was recorded.
    pub vcount: BTreeMap<(String, String), u64>,
    /// Transmit calls.
    pub tx_count: u64,
    /// Every byte at send, before any drop.
    pub wire_bytes: u64,
    /// Bytes of datagrams or records that carry another node's data.
    pub third_bytes: u64,
    /// Wire bytes sent inside the idle window.
    pub idle_bytes: u64,
    /// Transmit calls inside the idle window.
    pub idle_tx: u64,
    /// Wire bytes sent on stream carriers.
    pub tcp_bytes: u64,
    /// Wire bytes sent per node.
    pub node_tx_bytes: BTreeMap<usize, u64>,
    /// The intents, by id.
    pub intents: BTreeMap<u32, IntentRec>,
    /// The next intent id.
    pub next_iid: u32,
    /// Bytes the application saw delivered.
    pub app_bytes: u64,
    /// Bytes already held when they arrived again.
    pub redundant: u64,
    /// Resume records.
    pub resumes: Vec<Resume>,
    open_resumes: BTreeMap<usize, Vec<usize>>,
    /// Membership events seen by the nodes.
    pub membership: Vec<MemberRec>,
    /// Ground-truth membership changes (the world's, plus every address change observed).
    pub changes: Vec<Change>,
    /// Per node, the `[start, end)` intervals it was alive; an open interval has no end.
    pub alive_iv: BTreeMap<usize, Vec<(u64, Option<u64>)>>,
    /// Per node, the `[start, end)` intervals it was suspended.
    pub susp_iv: BTreeMap<usize, Vec<(u64, u64)>>,
    /// The last view epoch per `(node, incarnation)`.
    pub view_epochs: BTreeMap<(usize, u64), u64>,
    /// Access answers per `(asking node, principal)`: `(time, allow, valid until)`.
    pub acp_log: BTreeMap<(usize, usize), Vec<AcpAnswer>>,
    /// Denied nodes.
    pub denied: BTreeSet<usize>,
    /// Revoked nodes with their revocation time.
    pub revoked: BTreeMap<usize, u64>,
    /// Delivery checks that failed.
    pub acp_violations: u64,
    /// The revocation bound of the delivery check: defaults to the world's cap; the host lowers it to its own bound.
    pub revocation_bound_ns: u64,
    /// Per spoofed address, `[bytes received from it, bytes sent to it]`.
    pub amp: BTreeMap<SocketAddr, [u64; 2]>,
    /// The node each spoofed address targets.
    pub amp_targets: BTreeMap<SocketAddr, usize>,
    /// Adversary actions by kind (`replay`, `modify`, `inject`).
    pub adv: BTreeMap<String, u64>,
    /// Peak sampled state per node.
    pub state_peaks: BTreeMap<usize, u64>,
    /// Carriers opened.
    pub carriers: u64,
    /// Store writes of values.
    pub value_events: Vec<ValueEvent>,
    /// Echo timelines by intent id.
    pub echo: BTreeMap<u32, EchoRec>,
    /// Protocol crashes (G-SPEC).
    pub crashes: u64,
    /// Punched paths counted by the NATs at the end of the run.
    pub punched_paths: u64,
    /// `(node, value id)` of broadcast messages delivered, for duplicate detection.
    pub delivered_msgs: BTreeSet<(usize, u64)>,
    /// The idle window.
    pub idle: Option<(u64, u64)>,
    /// Total metered CPU nanoseconds, set by [`Rec::finish`].
    pub cpu_ns: f64,
    /// The first four `(node, time)` of payload seen in plaintext on the wire.
    pub plaintext_payload: Vec<(usize, u64)>,
    /// Soak: per node, the state peak in each third of the run.
    pub state_thirds: BTreeMap<usize, [u64; 3]>,
    /// S14: `(bytes both ends sent during the session, items in the difference)`.
    pub reconcile_cost: Vec<(u64, u64)>,
    /// Delivered push sequence numbers per `(origin, replicator)`.
    pub pushlog_order: BTreeMap<(usize, usize), Vec<u64>>,
    /// The end of the run, set by [`Rec::finish`].
    pub end: u64,
}

fn int(v: impl Into<i128>) -> Py<'static> {
    Py::Int(v.into())
}

fn idx_py(i: usize) -> Py<'static> {
    int(i as u64)
}

impl Rec {
    /// A recorder for `world`: ground-truth changes, the denied set and the idle window come from the world.
    pub fn new(world: Rc<World>) -> Self {
        let denied = world.denied.iter().copied().collect();
        let changes = world.changes.clone();
        let idle = Some(world.idle_window);
        let revocation_bound_ns = world.revocation_bound_cap_ns;
        let adv = ["replay", "modify", "inject"]
            .iter()
            .map(|k| ((*k).to_owned(), 0))
            .collect();
        Self {
            world,
            h: Blake2b::<U16>::new(),
            violations: Vec::new(),
            vcount: BTreeMap::new(),
            tx_count: 0,
            wire_bytes: 0,
            third_bytes: 0,
            idle_bytes: 0,
            idle_tx: 0,
            tcp_bytes: 0,
            node_tx_bytes: BTreeMap::new(),
            intents: BTreeMap::new(),
            next_iid: 1,
            app_bytes: 0,
            redundant: 0,
            resumes: Vec::new(),
            open_resumes: BTreeMap::new(),
            membership: Vec::new(),
            changes,
            alive_iv: BTreeMap::new(),
            susp_iv: BTreeMap::new(),
            view_epochs: BTreeMap::new(),
            acp_log: BTreeMap::new(),
            denied,
            revoked: BTreeMap::new(),
            acp_violations: 0,
            revocation_bound_ns,
            amp: BTreeMap::new(),
            amp_targets: BTreeMap::new(),
            adv,
            state_peaks: BTreeMap::new(),
            carriers: 0,
            value_events: Vec::new(),
            echo: BTreeMap::new(),
            crashes: 0,
            punched_paths: 0,
            delivered_msgs: BTreeSet::new(),
            idle,
            cpu_ns: 0.0,
            plaintext_payload: Vec::new(),
            state_thirds: BTreeMap::new(),
            reconcile_cost: Vec::new(),
            pushlog_order: BTreeMap::new(),
            end: 0,
        }
    }

    /// Feeds `repr(parts)` to the trace hash.
    pub(crate) fn hash(&mut self, parts: &[Py<'_>]) {
        self.h.update(Py::Tuple(parts).repr().as_bytes());
    }

    /// Records a violation: the first three per `(gate, msg)` are kept; every one enters the trace hash.
    pub fn violation(&mut self, now: u64, gate: &str, idx: usize, msg: &str) {
        let n = self.vcount.entry((gate.to_owned(), msg.to_owned())).or_insert(0);
        *n += 1;
        if *n <= 3 {
            self.violations.push(Violation {
                gate: gate.to_owned(),
                node: idx,
                msg: msg.to_owned(),
                t: now,
            });
        }
        self.hash(&[Py::Str("V"), Py::Str(gate), idx_py(idx), Py::Str(msg)]);
    }

    /// A protocol raised on peer input: G-SPEC, counted in `crashes`.
    pub fn crash(&mut self, now: u64, idx: usize, where_: &str, what: &str) {
        self.crashes += 1;
        let msg = format!("protocol raised {what} in {where_} (never raise on peer input)");
        self.violation(now, "G-SPEC", idx, &msg);
    }

    /// A G-INT violation.
    pub fn integrity_violation(&mut self, now: u64, idx: usize, msg: &str) {
        self.violation(now, "G-INT", idx, msg);
    }

    /// Whether `t` is inside the idle window.
    pub fn in_idle(&self, t: u64) -> bool {
        self.idle.is_some_and(|(a, b)| a <= t && t < b)
    }

    // ------------------------------------------------------------------ wire

    /// One Transmit call at `t`.
    pub fn transmit_call(&mut self, _idx: usize, t: u64) {
        self.tx_count += 1;
        if self.in_idle(t) {
            self.idle_tx += 1;
        }
    }

    /// One send of `size` bytes by `idx` at `t` (counted before any drop). `third`: the message carries another
    /// node's data; `plaintext`: it carries payload outside any seal; `tcp`: a stream-carrier segment;
    /// `carrier_payload`: the record length counted for B5 when `size` is zero; `dst`: the destination, counted
    /// toward `amp` when it is a spoofed address.
    #[allow(clippy::too_many_arguments)]
    pub fn wire(
        &mut self,
        idx: usize,
        t: u64,
        size: u64,
        third: bool,
        plaintext: bool,
        tcp: bool,
        carrier_payload: u64,
        dst: Option<SocketAddr>,
    ) {
        if size != 0 {
            self.wire_bytes += size;
            *self.node_tx_bytes.entry(idx).or_insert(0) += size;
            if tcp {
                self.tcp_bytes += size;
            }
            if self.in_idle(t) {
                self.idle_bytes += size;
            }
            if let Some(open) = self.open_resumes.get(&idx) {
                for &r in open {
                    if let Some(rs) = self.resumes.get_mut(r) {
                        rs.bytes += size;
                    }
                }
            }
            self.hash(&[Py::Str("W"), idx_py(idx), int(t), int(size)]);
        }
        if plaintext && self.plaintext_payload.len() < 4 {
            self.plaintext_payload.push((idx, t));
        }
        if third {
            self.third_bytes += if size != 0 { size } else { carrier_payload };
        }
        if let Some(a) = dst.and_then(|d| self.amp.get_mut(&d)) {
            a[1] += size;
        }
    }

    /// A datagram of `size` bytes from `src` reached `idx`; `redundant_bytes` of its value payload were already held.
    pub fn udp_received(&mut self, _idx: usize, _t: u64, src: SocketAddr, size: u64, redundant_bytes: u64) {
        self.redundant += redundant_bytes;
        if let Some(a) = self.amp.get_mut(&src) {
            a[0] += size;
        }
    }

    /// A carrier record reached `idx`; `redundant_bytes` of its value payload were already held.
    pub fn carrier_received(&mut self, _idx: usize, _t: u64, redundant_bytes: u64) {
        self.redundant += redundant_bytes;
    }

    /// A carrier was opened.
    pub fn carrier_opened(&mut self) {
        self.carriers += 1;
    }

    /// The adversary replayed or modified a datagram (`kind`: `replay`, `modify`, `inject`).
    pub fn adversary_action(&mut self, kind: &str) {
        *self.adv.entry(kind.to_owned()).or_insert(0) += 1;
    }

    /// The adversary injected a datagram of `n` payload bytes from `src`.
    pub fn adversary_injected(&mut self, _idx: usize, _t: u64, n: u64, src: SocketAddr) {
        *self.adv.entry("inject".to_owned()).or_insert(0) += 1;
        if let Some(a) = self.amp.get_mut(&src) {
            a[0] += n + 28;
        }
    }

    /// An amplification probe from `spoof` against `idx` begins.
    pub fn amp_probe(&mut self, idx: usize, spoof: SocketAddr) {
        self.amp.entry(spoof).or_insert([0, 0]);
        self.amp_targets.insert(spoof, idx);
    }

    // ------------------------------------------------------------------ nodes / env

    /// A node started.
    pub fn node_started(&mut self, idx: usize, t: u64) {
        self.alive_iv.entry(idx).or_default().push((t, None));
        self.hash(&[Py::Str("start"), idx_py(idx), int(t)]);
    }

    /// A node stopped (crashed or left).
    pub fn node_stopped(&mut self, idx: usize, t: u64, graceful: bool) {
        if let Some(last) = self.alive_iv.get_mut(&idx).and_then(|v| v.last_mut())
            && last.1.is_none()
        {
            last.1 = Some(t);
        }
        self.hash(&[Py::Str("stop"), idx_py(idx), int(t), Py::Bool(graceful)]);
    }

    /// A node was suspended at `t` for `dur`.
    pub fn suspended(&mut self, idx: usize, t: u64, dur: u64) {
        self.susp_iv.entry(idx).or_default().push((t, t + dur));
    }

    /// A suspension ended; `has_open` is the application's `has_open_intents(t)`.
    pub fn resumed(&mut self, idx: usize, t: u64, has_open: bool) {
        self.resume_event(idx, t, ResumeKind::Resume, has_open);
    }

    /// A node's address changed: a ground-truth `addr` change.
    pub fn address_change(&mut self, idx: usize, t: u64) {
        self.changes.push(Change {
            t,
            kind: ChangeKind::Addr,
            node: idx,
            version: None,
        });
    }

    /// A node's link returned (handover or outage end).
    pub fn link_returned(&mut self, idx: usize, t: u64, has_open: bool) {
        self.resume_event(idx, t, ResumeKind::Link, has_open);
    }

    /// A NAT rebound.
    pub fn nat_rebind(&mut self, nid: usize, t: u64) {
        self.hash(&[Py::Str("rebind"), idx_py(nid), int(t)]);
    }

    fn resume_event(&mut self, idx: usize, t: u64, kind: ResumeKind, has_open: bool) {
        if !has_open {
            return;
        }
        self.open_resumes.entry(idx).or_default().push(self.resumes.len());
        self.resumes.push(Resume {
            node: idx,
            t,
            kind,
            first: None,
            bytes: 0,
        });
    }

    /// A node restarted keeping its state.
    pub fn restarted_with_state(&mut self, idx: usize, t: u64, has_open: bool) {
        self.resume_event(idx, t, ResumeKind::Restart, has_open);
    }

    /// A node was revoked at `t`.
    pub fn revoke(&mut self, idx: usize, t: u64) {
        self.revoked.insert(idx, t);
    }

    /// Was `idx` alive at `t`?
    pub fn alive_at(&self, idx: usize, t: u64) -> bool {
        self.alive_at_i(idx, i128::from(t))
    }

    /// `alive_at` for a time that may be negative (a bound before the start of the run).
    pub(crate) fn alive_at_i(&self, idx: usize, t: i128) -> bool {
        self.alive_iv.get(&idx).is_some_and(|iv| {
            iv.iter()
                .any(|&(a, b)| i128::from(a) <= t && b.is_none_or(|b| t < i128::from(b)))
        })
    }

    /// Was `idx` suspended at `t`?
    pub fn suspended_at(&self, idx: usize, t: u64) -> bool {
        self.suspended_at_i(idx, i128::from(t))
    }

    /// `suspended_at` for a time that may be negative.
    pub(crate) fn suspended_at_i(&self, idx: usize, t: i128) -> bool {
        self.susp_iv
            .get(&idx)
            .is_some_and(|iv| iv.iter().any(|&(a, b)| i128::from(a) <= t && t < i128::from(b)))
    }

    /// Was `idx` alive during the whole of `[t0, t1]`?
    pub fn alive_through(&self, idx: usize, t0: u64, t1: u64) -> bool {
        self.alive_through_i(idx, i128::from(t0), i128::from(t1))
    }

    /// `alive_through` for bounds that may be negative.
    pub(crate) fn alive_through_i(&self, idx: usize, t0: i128, t1: i128) -> bool {
        self.alive_iv.get(&idx).is_some_and(|iv| {
            iv.iter()
                .any(|&(a, b)| i128::from(a) <= t0 && b.is_none_or(|b| i128::from(b) >= t1))
        })
    }

    // ------------------------------------------------------------------ intents

    /// Records an intent and returns its id (0 and a G-SPEC violation for a kind string the reference does not
    /// know). `deadline` is absolute.
    #[allow(clippy::too_many_arguments)]
    pub fn intent(
        &mut self,
        kind: impl AsIntentKind,
        node: usize,
        t: u64,
        deadline: impl Into<Option<u64>>,
        receivers: &[usize],
        size: u64,
        must: MustArg,
        meta: IntentMeta,
    ) -> u32 {
        let Some(kind) = kind.into_intent_kind() else {
            self.violation(t, "G-SPEC", node, "an intent of an unknown kind was recorded");
            return 0;
        };
        let iid = self.next_iid;
        self.next_iid += 1;
        let it = IntentRec::new(iid, kind, node, t, deadline.into(), receivers, size, must, meta);
        self.intents.insert(iid, it);
        self.hash(&[Py::Str("I"), int(iid), Py::Str(kind_name(kind)), idx_py(node), int(t)]);
        iid
    }

    /// Marks an intent as running under bulk transfers.
    pub fn set_under_bulk(&mut self, iid: u32, under_bulk: bool) {
        if let Some(it) = self.intents.get_mut(&iid) {
            it.under_bulk = under_bulk;
        }
    }

    /// `node` received intent `iid` at `t` (`nbytes` application bytes). A second delivery of a broadcast message
    /// is a G-INT violation; of any other kind it is ignored.
    pub fn delivered(&mut self, iid: u32, node: usize, t: u64, nbytes: u64) {
        let Some(it) = self.intents.get_mut(&iid) else { return };
        if it.delivered.contains_key(&node) {
            if it.kind == IntentKind::Publish {
                self.violation(
                    t,
                    "G-INT",
                    node,
                    "duplicate delivery of a broadcast message to the application",
                );
            }
            return;
        }
        it.delivered.insert(node, t);
        let (origin, is_echo) = (it.node, it.kind == IntentKind::Echo);
        if is_echo && node == origin {
            self.echo.entry(iid).or_default().done = Some(t);
        }
        self.app_bytes += nbytes;
        self.app_byte(node, t);
        self.app_byte(origin, t);
        self.hash(&[Py::Str("D"), int(iid), idx_py(node), int(t)]);
    }

    /// Notes that broadcast message `vid` reached `node`; returns false (and records a G-INT violation) when it
    /// had already reached it.
    pub fn message_first_delivery(&mut self, now: u64, node: usize, vid: u64) -> bool {
        if self.delivered_msgs.insert((node, vid)) {
            return true;
        }
        self.violation(
            now,
            "G-INT",
            node,
            "duplicate delivery of a broadcast message to the application",
        );
        false
    }

    fn app_byte(&mut self, node: usize, t: u64) {
        let Some(open) = self.open_resumes.get_mut(&node) else {
            return;
        };
        let resumes = &mut self.resumes;
        open.retain(|&r| match resumes.get_mut(r) {
            Some(rs) if t >= rs.t => {
                rs.first = Some(t);
                false
            }
            _ => true,
        });
    }

    /// An echo's connection was reported (first report only).
    pub fn echo_connected(&mut self, iid: u32, now: u64) {
        self.echo.entry(iid).or_default().connected.get_or_insert(now);
    }

    /// An echo's request was written (the last write counts).
    pub fn echo_written(&mut self, iid: u32, now: u64) {
        self.echo.entry(iid).or_default().written = Some(now);
    }

    /// An echo was served (first serve only).
    pub fn echo_served(&mut self, iid: u32, now: u64) {
        self.echo.entry(iid).or_default().served.get_or_insert(now);
    }

    /// A store write: `len` bytes at `off` of value `vid` by `idx`, `new` of them newly verified. The caller then
    /// invokes the application's value progress itself.
    pub fn value_bytes_written(&mut self, now: u64, idx: usize, vid: u64, off: u64, len: u64, new: u64) {
        self.value_events.push(ValueEvent {
            t: now,
            node: idx,
            vid,
            off,
            len,
            new,
        });
        if new != 0 {
            self.app_bytes += new;
            self.app_byte(idx, now);
        }
        self.hash(&[Py::Str("VW"), idx_py(idx), int(vid), int(off), int(len), int(new)]);
    }

    /// A delivered push: `seq` reached `replicator` from `origin`.
    pub fn pushlog_delivered(&mut self, origin: usize, replicator: usize, seq: u64) {
        self.pushlog_order.entry((origin, replicator)).or_default().push(seq);
    }

    /// A reconcile session finished: both ends sent `bytes` during it and the difference had `diff` items.
    pub fn reconcile_done(&mut self, bytes: u64, diff: u64) {
        self.reconcile_cost.push((bytes, diff.max(1)));
    }

    // ------------------------------------------------------------------ state

    /// A state-size sample of `idx` at `now`.
    pub fn state_sample(&mut self, now: u64, idx: usize, size: u64) {
        let cur = self.state_peaks.entry(idx).or_insert(0);
        if size > *cur {
            *cur = size;
        }
        if self.world.soak {
            let k = (u128::from(now) * 3 / u128::from(self.world.duration_ns.max(1))).min(2) as usize;
            let w = self.state_thirds.entry(idx).or_insert([0; 3]);
            if let Some(slot) = w.get_mut(k)
                && size > *slot
            {
                *slot = size;
            }
        }
    }

    // ------------------------------------------------------------------ finish

    /// Closes the run at `until`. `cpu_ns` is the total metered CPU of all nodes, `punched_paths` the NATs' count.
    /// The host samples the state of every live node (with [`Rec::state_sample`]) before calling this.
    pub fn finish(&mut self, until: u64, cpu_ns: f64, punched_paths: u64) {
        self.end = until;
        self.cpu_ns = cpu_ns;
        self.punched_paths = punched_paths;
    }

    /// The trace hash: blake2b-128 over the hashed tuples and the final `(wire, app, violations, cpu)` tuple.
    pub fn trace_hash(&self) -> String {
        let mut h = self.h.clone();
        let fin = Py::Tuple(&[
            int(self.wire_bytes),
            int(self.app_bytes),
            int(self.violations.len() as u64),
            Py::Float(self.cpu_ns),
        ]);
        h.update(fin.repr().as_bytes());
        h.finalize().iter().fold(String::with_capacity(32), |mut acc, b| {
            let _ = write!(acc, "{b:02x}");
            acc
        })
    }
}

#[cfg(test)]
mod tests;
