//! Late timers of one `pinc_membership::Membership`, driven by hand-made hub frames.
//!
//! The expectation is the module invariant of `timers.rs`: "a tick that arrives later than [`WAKE_GAP`] after it was
//! due is a suspension: the node renews every hub at once with a snapshot request and opens a quiet window, so
//! removals queued while it slept are re-checked, not believed". The first tick is due at the node's start:
//! `poll_timeout` returns `next_tick.unwrap_or(self.born)`. A member is used; the late-tick path is the member's
//! (`!self.is_hub` in `on_timeout`), and nothing in the docs gives a hub a quiet window, so hubs are not checked.
//!
//! The host model: one hub A with a session and fresh transport evidence; A's frames are built with the crate's own
//! codec, as `repro_membership.rs` does.

use std::collections::{BTreeMap, BTreeSet};

use ephyra::prelude::*;
use pinc_membership::codec::{Alive, Snap, entry_bytes};
use pinc_membership::consts::{NODE_TICK, WAKE_GAP};
use pinc_membership::event::QuietCause;
use pinc_membership::session::StoreError;
use pinc_membership::{
    Broadcast, Carrier, CloseReason, Config, Evidence, Frame, Local, Membership, NodeId, Record, Route, Session, Trace,
};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000 * MS;
const T0: u64 = 1_000 * SEC;

fn id(i: u8) -> NodeId {
    [i + 1; 32]
}

#[derive(Default)]
struct Host {
    sessions: BTreeSet<NodeId>,
    ev: BTreeMap<NodeId, Evidence>,
}

impl Session for Host {
    fn send(&mut self, peer: &NodeId, _route: Route, _frame: &[u8]) -> bool {
        self.sessions.contains(peer)
    }
    fn evidence(&self, peer: &NodeId) -> Option<Evidence> {
        self.ev.get(peer).copied()
    }
    fn carrier(&self, _member: &NodeId) -> Carrier {
        Carrier::Unknown
    }
    fn close(&mut self, _peer: &NodeId, _reason: CloseReason) {}
}

impl Broadcast for Host {
    fn floor(&mut self, _member: &NodeId, _out: &mut [u8]) -> usize {
        0
    }
    fn frame(&mut self, _from: &NodeId, _ty: u8, _topic: &[u8], _rest: &[u8]) {}
    fn hold(&mut self, _member: &NodeId) {}
    fn restore(&mut self, _member: &NodeId) {}
    fn release(&mut self, _member: &NodeId) {}
    fn resubscribe(&mut self, _hub: &NodeId) {}
    fn primary_changed(&mut self, _old: Option<&NodeId>, _new: &NodeId) {}
}

impl Local for Host {
    fn version(&self) -> u16 {
        7
    }
    fn reflexive_known(&self) -> bool {
        true
    }
    fn address_hash(&self, moves: u8) -> [u8; 8] {
        [moves, 0, 0, 0, 0, 0, 0, 9]
    }
    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        Ok(None)
    }
}

/// A member with hub A, started at `T0`, with A's session up and A's complete snapshot listing `x`.
fn member_with_home() -> (Membership, Host) {
    let a = id(1);
    let hubs = [a];
    let cfg = Config { me: id(0), is_hub: false, hubs: &hubs, trace: true };
    let mut h = Host::default();
    let mut m = Membership::start(&cfg, &mut h, T0, 0, 0).expect("starts");
    h.sessions.insert(a);
    m.session_up(&mut h, T0, &a, false);
    h.ev.insert(a, Evidence { last_rx: T0, srtt: 20 * MS, pto: 0, inflight: 0, direct: true });
    snap(&mut m, &mut h, T0, &[id(2)]);
    (m, h)
}

/// A's complete snapshot listing `members`.
fn snap(m: &mut Membership, h: &mut Host, now: u64, members: &[NodeId]) {
    let rec = Record { inc: 5 << 16, ver: 7, thash: [1; 8] };
    let entries: Vec<u8> = members.iter().flat_map(|x| entry_bytes(x, &rec, Alive::Alive)).collect();
    let mut out = vec![0u8; 4096];
    let f = Frame::Snap(Snap::new(false, false, &entries).expect("alive entries"));
    let b = f.encode(&mut out).expect("encodes").to_vec();
    assert_eq!(m.on_bytes(h, now, &id(1), &b), Ok(b.len()));
}

/// `timers.rs`: "a tick that arrives later than WAKE_GAP after it was due is a suspension: the node ... opens a quiet
/// window". The host serves `on_time` ticks on time (the first at the start, when `poll_timeout` says the first tick
/// is due, then every NODE_TICK), then the next tick arrives `late_ms` after it was due, with `late_ms` above
/// WAKE_GAP. That call must open a quiet window for a late timer, whether or not a tick ran before it.
#[ephyra::test(gen = (gens::int(0u8..=3), gens::int(2_001u32..=300_000)), tests = 200)]
fn a_late_tick_opens_a_quiet_window(case: (u8, u32)) {
    let (on_time, late_ms) = case;
    let (mut m, mut h) = member_with_home();
    assert_eq!(m.poll_timeout(), T0, "the first tick is due at the start");
    let mut due = T0;
    for k in 0..u64::from(on_time) {
        let t = T0 + k * NODE_TICK;
        m.on_timeout(&mut h, t);
        due = t + NODE_TICK;
    }
    let _ = std::iter::from_fn(|| m.poll_trace()).count();
    let at = due + u64::from(late_ms) * MS;
    assert!(at - due > WAKE_GAP);
    h.ev.insert(id(1), Evidence { last_rx: at, srtt: 20 * MS, pto: 0, inflight: 0, direct: true });
    m.on_timeout(&mut h, at);
    let traces: Vec<Trace> = std::iter::from_fn(|| m.poll_trace()).collect();
    let quiet = traces.iter().any(|t| matches!(t, Trace::Quiet { cause: QuietCause::LateTimer }));
    assert!(quiet, "a tick {late_ms} ms late after {on_time} on-time ticks opened no quiet window: {traces:?}");
}
