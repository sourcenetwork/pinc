//! Reproductions of membership bugs found by the properties in `membership.rs`, each a plain test that fails on the
//! unmodified code.

use std::collections::BTreeSet;

use pinc_membership::codec::{Alive, Snap, entry_bytes};
use pinc_membership::session::StoreError;
use pinc_membership::{
    Broadcast, Carrier, CloseReason, Config, Evidence, Frame, Local, Membership, NodeId, Record, Route, Session,
};

const SEC: u64 = 1_000_000_000;

fn id(i: u8) -> NodeId {
    [i + 1; 32]
}

/// A host whose sessions are the set given, with fresh transport evidence for every peer it is told of.
#[derive(Default)]
struct Host {
    sessions: BTreeSet<NodeId>,
    ev: std::collections::BTreeMap<NodeId, Evidence>,
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

/// A complete or partial snapshot frame from `hub` listing `members`, all alive with `rec`.
fn snap(m: &mut Membership, h: &mut Host, now: u64, hub: NodeId, partial: bool, more: bool, members: &[NodeId], rec: Record) {
    let entries: Vec<u8> = members.iter().flat_map(|x| entry_bytes(x, &rec, Alive::Alive)).collect();
    let mut out = vec![0u8; 4096];
    let f = Frame::Snap(Snap::new(partial, more, &entries).expect("alive entries"));
    let b = f.encode(&mut out).expect("encodes").to_vec();
    assert_eq!(m.on_bytes(h, now, &hub, &b), Ok(b.len()));
}

/// This node dials `hub`, the transport hears it, and the hub answers with a complete snapshot of `members`.
fn link(m: &mut Membership, h: &mut Host, now: u64, hub: NodeId, members: &[NodeId], rec: Record) {
    h.sessions.insert(hub);
    m.session_up(h, now, &hub, false);
    h.ev.insert(hub, Evidence { last_rx: now, srtt: 20_000_000, pto: 0, inflight: 0, direct: true });
    snap(m, h, now, hub, false, false, members, rec);
}

fn trace(m: &mut Membership) -> Vec<String> {
    std::iter::from_fn(|| m.poll_trace()).map(|t| format!("{t:?}")).collect()
}

/// `view.rs`: "A snapshot never removes a member on its own. A complete snapshot that omits a member starts that
/// member's lease clock ...; the member stays in the view, with no event, and leaves it only when the hub reports it
/// down (a delta or a DOWN of the same or a newer incarnation), or when a full lease passes without any hub listing it
/// again."
///
/// Actual: a member node with hubs A, B, C. Hub A lists member X; hub B sends an empty snapshot; A's session goes
/// down; B starts a multi-frame snapshot (`more` set, no entries yet); A's session comes back and A sends a complete
/// snapshot without X. X leaves the view at once, at the same instant, with no lease passed and no hub reporting it
/// down; the application gets `Event::MemberConfirmedDown` for a live member (trace `Removed { why: Reported }`).
/// The same happens when the home's snapshot is complete but marked `partial` (a hub younger than a lease): seeds 4
/// to 6 of the property found both shapes. Found by `machine_keeps_its_invariants` (EPHYRA_SEED=3, replay 3:3055).
///
/// Suspected fault: `apply_snap` sets `home_ok` on any snapshot frame from the primary (view.rs:316-318), so
/// `source` (view.rs:189-192) makes the home's copy the only source at once, while only the last frame of a complete,
/// non-partial home snapshot gives the view members it omits their lease clock (`mark_view_absent`, view.rs:359-361).
/// In between, `recompute_one` (view.rs:497-498) finds no eligible entry for a member that only another hub's copy
/// holds and removes it. Who can trigger it: any hub (an authenticated peer) by sending a multi-frame or partial
/// snapshot, which hubs do in normal operation (SNAP_CHUNK, a young hub), together with ordinary session churn.
#[test]
fn snapshot_omitting_a_member_removes_it_at_once() {
    let (a, b, c, x) = (id(2), id(3), id(1), id(4));
    let hubs = [c, a, b];
    let cfg = Config { me: id(0), is_hub: false, hubs: &hubs, trace: true };
    let mut h = Host::default();
    let now = 1_000 * SEC;
    let mut m = Membership::start(&cfg, &mut h, now, 0, 0).expect("starts");
    let rec = Record { inc: 5 << 16, ver: 7, thash: [1; 8] };
    link(&mut m, &mut h, now, a, &[x], rec);
    assert!(m.in_view(&x), "A's snapshot adds X");
    link(&mut m, &mut h, now, b, &[], rec);
    h.sessions.remove(&a);
    m.session_down(&mut h, now, &a, 0);
    snap(&mut m, &mut h, now, b, true, true, &[], rec);
    let before = trace(&mut m);
    link(&mut m, &mut h, now, a, &[], rec);
    let step = trace(&mut m);
    let events: Vec<_> = std::iter::from_fn(|| m.poll_event()).collect();
    assert!(m.in_view(&x), "X left the view on a snapshot\nbefore: {before:?}\nstep: {step:?}\nevents: {events:?}");
}
