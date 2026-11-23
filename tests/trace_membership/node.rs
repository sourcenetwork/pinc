//! The node trace: the real hub and member state machines of `pinc-membership`, exchanging frames over the membership
//! test world (`membership_world.rs`), recorded call by call as ndjson (`membership.ndjson`) for the TLA+ trace check
//! (`TraceMembership.tla`) and the Lean replay (`Pinc.TraceMembership`).
//!
//! A line is `{"t":"mem","run":R,"n":K,"op":OP, ...inputs..., "env":ENV, "out":OUT, "st":ST}`: the call, the host as
//! the call found it (transport evidence, carriers, which peers take a send, the store), what the machine asked of
//! the host (every send with its route and whether a session took it, every broadcast-layer call, every close, every
//! event and trace record, the store afterwards) and the public state after. The schema of the fields is in
//! `node_rec.rs`; the models apply the same call to their own full state and compare all of it.
//!
//! The runs are the scenarios of the design: attachment and PULSE, churn, loss, partitions and heals, slow members,
//! carrier drops with probes on every path, DOWN with every refusal, carrier returns, leave, revocation, crash and
//! restart on a persistent counter and on the clock, suspension, a heal and a late timer while a removal waits (#284),
//! the primary switch, a home switch to a hub that never
//! heard of a member that then crashes (#343), the address move, snapshots of several frames, and malformed input.
//! Every scenario asserts what the real code did, so the test is meaningful without the proof tools.

use std::cell::RefCell;
use std::rc::Rc;

use pinc_membership::codec::{Alive, Down, Entry, Frame, Hello, Path, Probe, Proof, Record, Snap};
use pinc_membership::event::{QuietCause, Refusal};
use pinc_membership::{Carrier, CloseReason, Event, NodeId, Trace};

use crate::common::TraceWriter;
use crate::node_rec::{JsonRec, Sink};
use crate::world::{Bc, LEAVE, MS, SEC, World, id};

const START: u64 = 100 * SEC;
const FILE: &str = "membership.ndjson";

struct Ctx {
    run: usize,
    sink: Sink,
}

impl Ctx {
    /// A recorded world of `hubs` hubs and `members` members, started at `start`.
    fn world(&mut self, hubs: usize, members: usize, start: u64) -> World {
        self.run += 1;
        let mut w = World::new(hubs, members, start);
        w.set_recorder(Box::new(JsonRec {
            run: self.run,
            sink: Rc::clone(&self.sink),
        }));
        w
    }

    fn started(&mut self, hubs: usize, members: usize) -> World {
        let mut w = self.world(hubs, members, START);
        w.attach_all();
        w.run(3 * SEC);
        w
    }
}

fn traces(w: &World, i: usize, f: impl Fn(&Trace) -> bool) -> usize {
    w.traces[i].iter().filter(|t| f(t)).count()
}

fn rec(epoch: u64, seq: u16, ver: u16) -> Record {
    Record {
        inc: (epoch << 16) | u64::from(seq),
        ver,
        thash: [7; 8],
    }
}

fn hub_of(w: &World, m: usize) -> usize {
    usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1
}

/// The attachment of members, the replay floor and snapshot, PULSE keeping leases without HELLOs.
fn steady(c: &mut Ctx) {
    let mut w = c.started(2, 3);
    w.run(100 * SEC);
    for m in 2..5 {
        for x in 0..5 {
            assert_eq!(w.has(m, x), x != m, "member {m} lists {x}");
        }
    }
    let suppressed: usize = (2..5)
        .map(|m| traces(&w, m, |t| matches!(t, Trace::HelloSuppressed { .. })))
        .sum();
    assert!(suppressed > 0, "PULSE skipped periodic HELLOs");
    assert!(w.nodes[0].m.roster_len() >= 4, "leases stay alive");
}

/// Churn: a graceful leave, a crash with a carrier drop, a member that rejoins on a new life.
fn churn(c: &mut Ctx) {
    let mut w = c.started(2, 4);
    w.run(10 * SEC);
    assert!(w.has(3, 2) && w.has(4, 2));
    w.leave(2);
    for hub in 0..2 {
        w.close_session(2, hub, LEAVE);
    }
    w.run(5 * SEC);
    for i in [3, 4, 5] {
        assert!(!w.has(i, 2), "member {i} dropped the leaver");
        assert_eq!(
            w.count_events(i, |e| matches!(e, Event::MemberLeft { member } if *member == id(2))),
            1
        );
        assert_eq!(w.count_events(i, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
    }
    assert!(w.nodes[0].h.bc.contains(&Bc::Release(id(2))) && !w.nodes[0].h.bc.contains(&Bc::Hold(id(2))));
    // A crash with a carrier drop at both hubs.
    w.run(20 * SEC);
    w.crash(3);
    for hub in 0..2 {
        w.set_carrier_gone(hub, 3);
    }
    assert!(w.run_until(20 * SEC, |w| !w.has(4, 3) && !w.has(5, 3)));
    assert!(w.nodes[0].h.bc.contains(&Bc::Hold(id(3))), "held, not dropped");
    // The member restarts on a new life, rejoins, and is listed again.
    w.restart(3, 1_000_003, 0);
    w.set_carrier_open(0, 3);
    w.set_carrier_open(1, 3);
    for hub in 0..2 {
        w.connect(3, hub);
    }
    w.run(30 * SEC);
    assert!(w.has(4, 3) && w.has(5, 3), "the member is back");
}

/// A lossy network and dropped frames; the awareness bound.
fn lossy(c: &mut Ctx) {
    let mut w = c.world(2, 6, START);
    w.rng = pinc_tests::SplitMix64::traced(3);
    w.loss_pct = 20;
    w.attach_all();
    w.run(120 * SEC);
    w.drop_once.push((0, 4, 1));
    w.drop_once.push((4, 0, 3));
    let victim = 5;
    let t = w.now;
    w.crash(victim);
    for hub in 0..2 {
        w.set_carrier_gone(hub, victim);
    }
    let live: Vec<usize> = (2..8).filter(|&i| i != victim).collect();
    assert!(
        w.run_until(145 * SEC, |w| live.iter().all(|&i| !w.has(i, victim))),
        "within the awareness bound"
    );
    assert!(w.now - t < 145 * SEC);
}

/// A crash without a carrier event: the lease ends it.
fn lease_end(c: &mut Ctx) {
    let mut w = c.started(2, 3);
    w.run(40 * SEC);
    w.crash(3);
    let t = w.now;
    assert!(w.run_until(145 * SEC, |w| !w.has(2, 3) && !w.has(4, 3)));
    assert!(w.now - t > 30 * SEC, "no carrier event: the lease decides");
}

/// A partition that outlasts the lease, a heal, a snapshot before the partition mate says HELLO again.
fn partition_heal(c: &mut Ctx) {
    let mut w = c.started(2, 3);
    let (m, p) = (2, 3);
    assert!(w.has(m, p));
    for hub in 0..2 {
        w.cut.insert((hub, m));
        w.cut.insert((hub, p));
    }
    w.run(100 * SEC);
    assert_eq!(w.nodes[0].m.lease_of(&id(p)), None, "the hubs let both leases go");
    assert!(w.has(m, p), "isolated, the member keeps its view");
    for hub in 0..2 {
        w.cut.remove(&(hub, m));
        w.cut.remove(&(hub, p));
        w.close_session(m, hub, 0);
    }
    w.run(SEC);
    for hub in 0..2 {
        w.connect(m, hub);
    }
    w.run(2 * SEC);
    assert!(w.has(m, p), "a snapshot never removes a member");
    assert_eq!(
        w.count_events(
            m,
            |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(p))
        ),
        0
    );
    for hub in 0..2 {
        w.close_session(p, hub, 0);
    }
    w.run(SEC);
    for hub in 0..2 {
        w.connect(p, hub);
    }
    w.run(150 * SEC);
    assert!(w.has(m, p));
    assert_eq!(w.count_events(m, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
}

/// A hub that goes quiet for longer than the stale bound while another is fresh, and returns (a heal).
fn hub_stale_heal(c: &mut Ctx) {
    let mut w = c.started(2, 2);
    w.run(10 * SEC);
    let m = 2;
    w.cut.insert((1, m));
    w.cut.insert((1, 0));
    w.run(90 * SEC);
    assert!(
        traces(&w, m, |t| matches!(t, Trace::HubStale { .. })) >= 1,
        "the silent hub's copy was dropped"
    );
    w.cut.remove(&(1, m));
    w.cut.remove(&(1, 0));
    w.close_session(m, 1, 0);
    w.run(SEC);
    w.connect(m, 1);
    w.run(40 * SEC);
    assert!(
        traces(&w, m, |t| matches!(
            t,
            Trace::Quiet {
                cause: QuietCause::Heal
            }
        )) >= 1
    );
}

/// A slow member (twelve times too slow to answer a probe) whose transport still answers; probes on every path.
fn slow_member(c: &mut Ctx) {
    let mut w = c.started(2, 2);
    w.direct.insert((0, 2));
    w.nodes[2].cpu = 5 * SEC;
    w.run(40 * SEC);
    w.set_carrier_gone(0, 2);
    w.run(8 * SEC);
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 0);
    // A member that answers on either path is never confirmed.
    w.direct.insert((0, 3));
    w.set_carrier_gone(0, 3);
    w.run(10 * SEC);
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 0);
}

/// A single lost probe does not confirm; two lost probes of a member that is gone do.
fn lost_probe(c: &mut Ctx) {
    let mut w = c.started(2, 2);
    w.run(40 * SEC);
    w.drop_once.push((0, 2, 12));
    w.nodes[0].h.carriers.insert(
        id(2),
        Carrier::Gone {
            since: w.now,
            sleep: None,
        },
    );
    w.notice_gone(0, 2);
    w.run(10 * SEC);
    assert_eq!(
        traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })),
        0,
        "the other probe was answered"
    );
    // Now the member really is gone and a hub's relay path to it is dead too.
    w.crash(3);
    w.direct.insert((0, 3));
    w.set_carrier_gone(0, 3);
    assert!(w.run_until(10 * SEC, |w| w.nodes[0].m.lease_of(&id(3)).is_none()));
    assert_eq!(
        traces(
            &w,
            0,
            |t| matches!(t, Trace::Confirmed { member, .. } if *member == id(3))
        ),
        1
    );
}

/// A confirmation with the session on a direct path, with none, and the lone hub that has no independent path: the
/// second probe takes another hub's relay in every case.
fn probe_paths(c: &mut Ctx) {
    for (hubs, direct) in [(2, true), (2, false), (1, false)] {
        let mut w = c.started(hubs, 1);
        if direct {
            w.direct.insert((0, hubs));
        }
        w.run(40 * SEC);
        w.crash(hubs);
        let t = w.now;
        w.set_carrier_gone(0, hubs);
        if hubs == 1 {
            w.run(60 * SEC);
            assert_eq!(traces(&w, 0, |t| matches!(t, Trace::NoIndependentPath { .. })), 1);
            assert!(w.run_until(60 * SEC, |w| w.nodes[0].m.roster_len() == 0));
            assert!(w.now - t > 60 * SEC);
        } else {
            assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.lease_of(&id(hubs)).is_none()));
            assert!(w.now - t >= SEC);
            assert!(w.nodes[0].h.bc.contains(&Bc::Hold(id(hubs))));
        }
    }
}

/// A sleeping member's carrier drop is not a failure.
fn sleeper(c: &mut Ctx) {
    let mut w = c.started(2, 1);
    w.run(30 * SEC);
    let since = w.now;
    w.nodes[0].h.carriers.insert(
        id(2),
        Carrier::Gone {
            since,
            sleep: Some(since - SEC),
        },
    );
    w.notice_gone(0, 2);
    w.run(30 * SEC);
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 0);
}

fn probe(age_ms: u32, path: Path) -> Probe {
    Probe { age_ms, path }
}

/// DOWN from another hub: accepted, and refused for every reason.
fn down_proofs(c: &mut Ctx) {
    let mut w = c.started(3, 2);
    w.run(10 * SEC);
    w.crash(3);
    w.run(40 * SEC);
    let m = id(3);
    let inc = w.nodes[3].m.incarnation();
    let two = Proof::new(5000, &[probe(1000, Path::Session), probe(900, Path::Relay)]).unwrap();
    let one = Proof::new(5000, &[probe(1000, Path::Session)]).unwrap();
    let liar = Proof::new(10, &[probe(1000, Path::Session), probe(900, Path::Relay)]).unwrap();
    fn down(member: &NodeId, inc: u64, proof: Proof) -> Frame<'_> {
        Frame::Down(Down { member, inc, proof })
    }
    // Not independent.
    w.inject(1, 0, &down(&m, inc, one));
    assert_eq!(w.nodes[1].m.roster_len(), 4, "a proof of one path is not enough");
    // An open carrier to this hub.
    w.nodes[1].h.carriers.insert(m, Carrier::Open);
    w.inject(1, 0, &down(&m, inc, two));
    w.nodes[1].h.carriers.insert(m, Carrier::Unknown);
    // A proof that claims less silence than its probes span.
    w.inject(1, 0, &down(&m, inc, liar));
    // A member this hub does not know, and one of another incarnation.
    let stranger = id(9);
    w.inject(1, 0, &down(&stranger, inc, two));
    w.inject(1, 0, &down(&m, inc + (1 << 16), two));
    // A hub is never reported down this way.
    let hub2 = id(2);
    w.inject(1, 0, &down(&hub2, w.nodes[2].m.incarnation(), two));
    // A fresh lease refuses (the other member's lease is fresh).
    let fresh = id(4);
    w.inject(1, 0, &down(&fresh, w.nodes[4].m.incarnation(), two));
    assert!(w.has(1, 4));
    // A DOWN from a member (not a hub) is ignored.
    w.inject(1, 4, &down(&m, inc, two));
    assert_eq!(w.nodes[1].m.roster_len(), 4);
    // Accepted: two paths, no carrier, a stale lease.
    w.inject(1, 0, &down(&m, inc, two));
    assert_eq!(w.nodes[1].m.roster_len(), 3, "accepted");
    let why = |r: Refusal| traces(&w, 1, move |t| matches!(t, Trace::DownRefused { why, .. } if *why == r));
    for r in [
        Refusal::NotApplicable,
        Refusal::Unknown,
        Refusal::LeaseFresh,
        Refusal::CarrierOpen,
        Refusal::NotIndependent,
        Refusal::BadProof,
    ] {
        assert!(why(r) >= 1, "refusal {r:?} happened");
    }
    assert_eq!(traces(&w, 1, |t| matches!(t, Trace::DownAccepted { .. })), 1);
    // The member's DOWN reaches the members as a delta.
    w.run(3 * SEC);
}

/// A returning carrier within the lease restores the entry, the subscriptions and tells the member; after the lease
/// nothing is restored.
fn carrier_return(c: &mut Ctx) {
    let mut w = c.started(2, 1);
    w.run(30 * SEC);
    w.cut.insert((1, 2));
    w.set_carrier_gone(0, 2);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.roster_len() == 1));
    assert!(w.nodes[0].h.bc.contains(&Bc::Hold(id(2))));
    w.cut.remove(&(1, 2));
    w.set_carrier_open(0, 2);
    assert_eq!(w.nodes[0].m.roster_len(), 2, "the entry is back");
    assert!(w.nodes[0].h.bc.contains(&Bc::Restore(id(2))));
    w.run(2 * SEC);
    assert!(
        w.nodes[2].h.bc.contains(&Bc::Resub(id(0))),
        "the member subscribed again"
    );
    assert_eq!(
        traces(&w, 0, |t| matches!(t, Trace::CarrierReturned { restored: true, .. })),
        1
    );
    // A second drop, with the lease running out before the carrier returns.
    w.run(30 * SEC);
    w.cut.insert((1, 2));
    w.set_carrier_gone(0, 2);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.roster_len() == 1));
    w.run(85 * SEC);
    w.set_carrier_open(0, 2);
    assert!(
        w.nodes[0].h.bc.contains(&Bc::Release(id(2))),
        "released at the lease end"
    );
    assert!(traces(&w, 0, |t| matches!(t, Trace::CarrierReturned { restored: false, .. })) >= 1);
    // A return that nothing was held for.
    w.set_carrier_open(0, 2);
}

/// Revocation: effective at once, sessions closed, frames dropped unread, sessions refused.
fn revocation(c: &mut Ctx) {
    let mut w = c.started(1, 3);
    w.run(5 * SEC);
    assert!(w.has(1, 2));
    assert!(w.revoke(0, 2));
    assert!(w.nodes[0].h.closed.contains(&(id(2), CloseReason::Revoked)));
    assert!(w.nodes[0].h.bc.contains(&Bc::Release(id(2))));
    assert_eq!(w.count_events(0, |e| matches!(e, Event::MemberRevoked { .. })), 1);
    w.run(2 * SEC);
    assert!(!w.has(1, 2), "the other member learned from the hub's delta");
    // Revoking again, and revoking a stranger.
    assert!(w.revoke(0, 2));
    assert!(w.revoke(0, 7));
    w.inject(
        0,
        2,
        &Frame::Hello(Hello {
            rec: rec(5, 0, 1),
            snap: true,
            homed: false,
        }),
    );
    w.connect(2, 0);
    w.run(SEC);
    // A member revokes a hub's member too, and a hub it does not know.
    assert!(w.revoke(1, 3));
    w.run(5 * SEC);
    assert!(!w.has(1, 3));
}

/// The table-full branch of the revocation: the entry past the bound is refused, the earlier ones are not.
fn revoke_full(c: &mut Ctx) {
    let mut w = c.world(1, 1, START);
    w.attach_all();
    w.run(2 * SEC);
    let max = u16::try_from(pinc_membership::consts::MAX_TABLE).unwrap();
    let mut refused = 0;
    for k in 0..=max {
        if !w.revoke_raw(0, 256 + k) {
            refused += 1;
        }
    }
    assert_eq!(refused, 1, "only the entry past the bound is refused");
    // A known revocation is still accepted when the table is full.
    assert!(w.revoke_raw(0, 256));
}

/// Crash and restart: the persistent counter and the clock, wall clock jumps back and forward, a hub that holds a
/// higher incarnation tells the node, which moves above it.
fn restarts(c: &mut Ctx) {
    let mut w = c.world(2, 2, START);
    for (i, node) in w.nodes.iter_mut().enumerate().take(4) {
        node.h.persistent = i % 2 == 0;
    }
    w.attach_all();
    w.run(20 * SEC);
    // The counter: restarts go up whatever the wall clock does.
    let mut last = w.nodes[2].m.incarnation();
    for (k, wall) in [5u64, 0, 1_700_000_000_000, 3].into_iter().enumerate() {
        // The first restart switches the host to a persistent counter: it passes the epoch it remembers as the floor.
        let floor = if k == 0 { last >> 16 } else { 0 };
        w.crash(2);
        for hub in 0..2 {
            w.close_session(2, hub, 0);
        }
        w.run(SEC);
        assert_eq!(w.restart(2, wall, floor), "ok");
        assert!(w.nodes[2].m.incarnation() > last, "restart {k}");
        last = w.nodes[2].m.incarnation();
        for hub in 0..2 {
            w.connect(2, hub);
        }
        w.run(8 * SEC);
        assert!(w.has(0, 2) || w.nodes[0].m.lease_of(&id(2)).is_some());
    }
    // The clock: a restart whose wall clock went back is above nothing, the hub tells the node, which moves above.
    let before = w.nodes[3].m.incarnation();
    w.crash(3);
    for hub in 0..2 {
        w.close_session(3, hub, 0);
    }
    w.run(SEC);
    assert_eq!(w.restart(3, 1, 0), "ok");
    for hub in 0..2 {
        w.connect(3, hub);
    }
    w.run(10 * SEC);
    assert!(w.nodes[3].m.incarnation() > before || w.nodes[3].m.incarnation() > 1 << 16);
    // A store that cannot be read refuses the start; one that cannot be written too.
    w.nodes[2].h.fail_unseal = true;
    assert_eq!(w.restart(2, 9, 0), "store");
    w.nodes[2].h.fail_unseal = false;
    w.nodes[2].h.fail_seal = true;
    assert_eq!(w.restart(2, 9, 0), "store");
    w.nodes[2].h.fail_seal = false;
    assert_eq!(w.restart(2, 9, 0), "ok");
    // A floor the host remembers by other means.
    assert_eq!(w.restart(3, 2, 1 << 40), "ok");
    assert!(w.nodes[3].m.incarnation() >> 16 > 1 << 40);
}

/// A node that is told its own incarnation is higher than its own moves above it.
fn reincarnated(c: &mut Ctx) {
    let mut w = c.started(1, 1);
    w.run(5 * SEC);
    let own = w.nodes[1].m.incarnation();
    let me = id(1);
    // The hub reports the node at a much higher incarnation (a lost store), then a lower one, then the same.
    for inc in [own + (500 << 16), own - 1, own] {
        let e = Entry {
            member: &me,
            rec: Record {
                inc,
                ver: 1,
                thash: [0; 8],
            },
            alive: Alive::Alive,
        };
        w.inject(1, 0, &Frame::Delta(e));
    }
    assert!(w.nodes[1].m.incarnation() > own + (500 << 16));
    let e = Entry {
        member: &me,
        rec: rec(1, 0, 1),
        alive: Alive::Down,
    };
    w.inject(1, 0, &Frame::Delta(e));
    // An exhausted epoch space: a hub reports the node at the end of the 48-bit space.
    let e = Entry {
        member: &me,
        rec: Record {
            inc: u64::MAX,
            ver: 1,
            thash: [0; 8],
        },
        alive: Alive::Alive,
    };
    w.inject(1, 0, &Frame::Delta(e));
    assert!(w.nodes[1].m.seal_failed());
    w.run(5 * SEC);
}

/// A suspension (a late timer) opens a quiet window; removals are re-checked at its end.
fn suspension(c: &mut Ctx) {
    let mut w = c.started(2, 3);
    let (m, x) = (2, 3);
    let hub = hub_of(&w, m);
    w.jump(20 * SEC);
    w.run(50 * MS);
    assert_eq!(
        traces(&w, m, |t| matches!(
            t,
            Trace::Quiet {
                cause: QuietCause::LateTimer
            }
        )),
        1
    );
    assert!(w.revoke(hub, x));
    w.run(100 * MS);
    assert!(w.has(m, x), "the removal is queued, not believed");
    w.run(9 * SEC);
    assert!(w.has(m, x));
    assert!(w.run_until(10 * SEC, |w| !w.has(m, x)));
    // A member that is back when the window ends is never reported.
    let mut w = c.started(2, 3);
    w.jump(20 * SEC);
    w.run(50 * MS);
    w.crash(3);
    w.run(2 * SEC);
    w.restart(3, 7, 0);
    for hub in 0..2 {
        w.connect(3, hub);
    }
    w.run(30 * SEC);
}

/// #284: a heal while a removal waits. Member 3 of a three-hub world is homed on hub 3 and has hubs 1 and 2 cut for a
/// minute, then hears hub 1 again (a heal); hub 3 revokes member 4 just after, so the removal waits for that window, and
/// hub 2 is heard again 3 s later (a second heal): the removal keeps its own instant and its extra look.
fn heal_while_waiting(c: &mut Ctx) {
    let mut w = c.world(3, 3, START);
    w.keepalive = 5 * SEC;
    let (m, x) = (3, 4);
    w.set_rtt(m, 0, 100 * MS);
    w.set_rtt(m, 1, 100 * MS);
    w.set_rtt(m, 2, 20 * MS);
    w.attach_all();
    w.run(5 * SEC);
    assert_eq!(w.nodes[m].m.primary(), Some(&id(2)));
    w.cut.insert((0, m));
    w.cut.insert((1, m));
    w.run(64 * SEC);
    w.cut.remove(&(0, m));
    assert!(w.run_until(20 * SEC, |w| traces(w, m, |t| matches!(t, Trace::Quiet { .. })) == 1));
    let healed = w.now;
    assert!(w.revoke(2, x));
    w.run(3 * SEC);
    w.cut.remove(&(1, m));
    assert!(w.run_until(30 * SEC, |w| traces(w, m, |t| matches!(t, Trace::Quiet { .. })) == 2));
    assert!(traces(&w, m, |t| matches!(t, Trace::Deferred { .. })) >= 1);
    assert!(w.has(m, x), "the removal waits while the windows are open");
    assert!(w.run_until(60 * SEC, |w| !w.has(m, x)));
    let left = w
        .first_event_time(m, |e| matches!(e, Event::MemberConfirmedDown { .. }))
        .unwrap();
    assert!(
        left - healed <= 16 * SEC,
        "the removal left {} ms after the first heal, not at the end of that window plus the extra look",
        (left - healed) / MS
    );
    w.run(5 * SEC);
}

/// #284: a late timer while a removal waits defers it again to the new window's end (the reference model's rule).
fn late_timer_while_waiting(c: &mut Ctx) {
    let mut w = c.started(2, 3);
    let (m, x) = (2, 3);
    let hub = hub_of(&w, m);
    w.jump(20 * SEC);
    w.run(50 * MS);
    assert!(w.revoke(hub, x));
    w.run(8 * SEC);
    assert!(w.has(m, x), "the removal waits for the window");
    w.jump(20 * SEC);
    w.run(50 * MS);
    let second = w.now;
    assert_eq!(
        traces(&w, m, |t| matches!(
            t,
            Trace::Quiet {
                cause: QuietCause::LateTimer
            }
        )),
        2
    );
    w.run(9 * SEC);
    assert!(w.has(m, x), "the second late timer deferred the waiting removal again");
    assert!(w.run_until(20 * SEC, |w| !w.has(m, x)));
    let left = w
        .first_event_time(m, |e| matches!(e, Event::MemberConfirmedDown { .. }))
        .unwrap();
    assert!(
        left - second >= 14 * SEC,
        "left {} ms after the second late timer",
        (left - second) / MS
    );
    w.run(5 * SEC);
}

/// The primary: the nearest hub, switching only past the hysteresis of 20 ms and a quarter, and when it goes down.
fn primary_switch(c: &mut Ctx) {
    let mut w = c.world(3, 1, START);
    let m = 3;
    for (hub, ms) in [(0, 200), (1, 150), (2, 400)] {
        w.set_rtt(m, hub, ms * MS);
    }
    w.attach_all();
    w.run(20 * SEC);
    assert_eq!(w.nodes[m].m.primary(), Some(&id(1)));
    w.set_rtt(m, 0, 120 * MS);
    w.run(20 * SEC);
    assert_eq!(
        w.nodes[m].m.primary(),
        Some(&id(1)),
        "120 + 20 is not under three quarters of 150"
    );
    w.set_rtt(m, 0, 70 * MS);
    w.run(20 * SEC);
    assert_eq!(w.nodes[m].m.primary(), Some(&id(0)));
    assert!(w.nodes[m].h.bc.contains(&Bc::Primary(Some(id(1)), id(0))));
    w.set_rtt(m, 1, 60 * MS);
    w.run(40 * SEC);
    assert_eq!(w.nodes[m].m.primary(), Some(&id(0)), "no flapping back");
    // The primary hub goes down: the node moves to the next.
    w.crash(0);
    w.close_session(m, 0, 0);
    w.run(10 * SEC);
    assert_ne!(w.nodes[m].m.primary(), Some(&id(0)));
}

/// #343: a member whose new home never heard of a member that later crashes lets it go. Hub 1 is cut from hub 2 and hub 2
/// from member 4; member 3 homes on hub 1 and lists 4; when 3 moves its home to hub 2, hub 2's complete snapshot starts
/// the omission lease for 4 at 3 although only hub 1's copy listed it; 4 crashes, every cut heals, and 3 lets 4 go.
fn stale_view(c: &mut Ctx) {
    let (h1, h2, n, m) = (0, 1, 2, 3);
    let mut w = c.world(2, 2, START);
    w.cut.insert((h1, h2));
    w.cut.insert((h2, m));
    w.set_rtt(n, h1, 100 * MS);
    w.set_rtt(n, h2, 120 * MS);
    w.attach_all();
    w.run(100 * SEC);
    assert_eq!(w.nodes[n].m.primary(), Some(&id(h1)), "member 3 homes on hub 1");
    assert!(
        w.has(n, m) && !w.has(h2, m),
        "member 3 lists member 4, which hub 2 never heard of"
    );
    w.set_rtt(n, h2, 40 * MS);
    w.run(30 * SEC);
    assert_eq!(
        w.nodes[n].m.primary(),
        Some(&id(h2)),
        "member 3 moved its home to hub 2"
    );
    w.crash(m);
    w.run(120 * SEC);
    w.cut.clear();
    w.connect(h2, h1);
    w.run(150 * SEC);
    let gone = id(m);
    assert!(
        w.traces[n]
            .iter()
            .any(|t| matches!(t, Trace::Absent { member } if *member == gone)),
        "hub 2's snapshot started the omission clock for member 4 at member 3"
    );
    assert!(!w.has(n, m), "member 3 let member 4 go");
}

/// The address tag: a move changes it once, and the previous one is kept while the reflexive address is unknown.
fn address_move(c: &mut Ctx) {
    let mut w = c.started(2, 2);
    let m = 2;
    w.run(10 * SEC);
    w.nodes[m].h.reflexive = false;
    w.moved(m);
    w.moved(m);
    w.run(2 * SEC);
    w.nodes[m].h.reflexive = true;
    w.run(8 * SEC);
    w.moved(m);
    w.run(4 * SEC);
    w.nodes[m].h.version = 2;
    w.run(8 * SEC);
    assert!(w.count_events(0, |e| matches!(e, Event::AddressChanged { .. })) >= 1);
    assert!(w.count_events(0, |e| matches!(e, Event::StackChanged { .. })) >= 1);
}

/// Snapshots of several frames: 70 members at one hub.
fn big_snapshot(c: &mut Ctx) {
    let mut w = c.world(1, 70, START);
    w.attach_all();
    w.run(6 * SEC);
    assert_eq!(w.nodes[1].m.member_count(), 70);
    assert!(
        w.frames
            .iter()
            .any(|(_, _, _, bytes)| bytes[4] == 4 && bytes[6] & 2 != 0),
        "a snapshot of several frames"
    );
}

/// Malformed input, frames of other types, frames a node has no use for, frames from a revoked peer.
fn garbage(c: &mut Ctx) {
    let mut w = c.started(1, 2);
    w.run(5 * SEC);
    let mut buf = [0u8; 512];
    let hello = Frame::Hello(Hello {
        rec: rec(9, 1, 1),
        snap: false,
        homed: false,
    });
    let hb = hello.encode(&mut buf).unwrap().to_vec();
    // Whole, truncated at every length, and two frames with a partial third.
    assert_eq!(w.inject_bytes(0, 1, &hb), Ok(hb.len()));
    for cut in 0..hb.len() {
        assert_eq!(w.inject_bytes(0, 1, &hb[..cut]), Ok(0));
    }
    let mut two = hb.clone();
    two.extend_from_slice(&hb);
    two.extend_from_slice(&hb[..7]);
    assert_eq!(w.inject_bytes(0, 1, &two), Ok(2 * hb.len()));
    // Malformed: reserved flag, an unknown alive byte, a topic on a membership frame, an oversize length, a bad body.
    let mut bad = hb.clone();
    *bad.last_mut().unwrap() = 0x80;
    assert!(w.inject_bytes(0, 1, &bad).is_err());
    let mut bad = hb.clone();
    bad[5] = 3;
    assert!(w.inject_bytes(0, 1, &bad).is_err());
    assert!(w.inject_bytes(0, 1, &[0xff, 0xff, 0xff, 0xff, 1, 0]).is_err());
    assert!(w.inject_bytes(0, 1, &[0, 0, 0, 2, 2, 1, 9]).is_err());
    assert!(w.inject_bytes(0, 1, &[0, 0, 0, 3, 13, 0, 0]).is_err());
    // Good frames then a bad one in the same buffer: the good ones took effect.
    let mut mixed = hb.clone();
    mixed.extend_from_slice(&[0, 0, 0, 2, 2, 1, 9]);
    assert!(w.inject_bytes(0, 1, &mixed).is_err());
    // Frames of other types reach the broadcast layer; a HELLO to a member and a DELTA from a non-hub are ignored.
    w.inject(
        0,
        1,
        &Frame::Other(pinc_membership::codec::Other {
            ty: 20,
            topic: b"t/a",
            rest: &[1, 2, 3],
        }),
    );
    w.inject(1, 2, &hello);
    let e = Entry {
        member: &id(2),
        rec: rec(1, 0, 1),
        alive: Alive::Down,
    };
    w.inject(1, 2, &Frame::Delta(e));
    w.inject(1, 0, &Frame::Ack);
    w.inject(1, 0, &Frame::Probe);
    // A snapshot with a continuation, then the rest, from the hub.
    let me = id(1);
    let es1 = pinc_membership::codec::entry_bytes(&id(7), &rec(3, 0, 1), Alive::Alive);
    let es2 = pinc_membership::codec::entry_bytes(&me, &rec(4, 0, 1), Alive::Alive);
    w.inject(1, 0, &Frame::Snap(Snap::new(false, true, &es1).unwrap()));
    w.inject(1, 0, &Frame::Snap(Snap::new(true, false, &es2).unwrap()));
    w.run(5 * SEC);
    // A revoked peer's frames are dropped unread.
    assert!(w.revoke(0, 2));
    assert!(w.inject_bytes(0, 2, &[1, 2, 3]).is_ok());
    assert!(traces(&w, 0, |t| matches!(t, Trace::BadFrame { .. })) >= 4);
}

/// The leave of a node itself: it renews no more and ignores frames.
fn leaving(c: &mut Ctx) {
    let mut w = c.started(1, 1);
    w.run(5 * SEC);
    w.leave(1);
    w.run(10 * SEC);
    w.inject(1, 0, &Frame::Ack);
    w.revoke(1, 0);
}

/// A hub told by another hub that a member left: the notices it refuses (an open carrier, another life of the member,
/// a member's word) and the one it takes, then a member that leaves with its close to one hub lost.
fn leave_notice(c: &mut Ctx) {
    let mut w = c.started(3, 2);
    w.run(10 * SEC);
    let m = id(3);
    let inc = w.nodes[3].m.incarnation();
    let notice = |inc| {
        Frame::Delta(Entry {
            member: &m,
            rec: Record {
                inc,
                ver: 1,
                thash: [3; 8],
            },
            alive: Alive::Left,
        })
    };
    w.nodes[0].h.carriers.insert(m, Carrier::Open);
    w.inject(0, 1, &notice(inc));
    assert!(
        w.nodes[0].m.lease_of(&m).is_some(),
        "an open carrier refuses the notice"
    );
    w.nodes[0].h.carriers.insert(m, Carrier::Unknown);
    w.inject(0, 1, &notice(inc + (1 << 16)));
    assert!(w.nodes[0].m.lease_of(&m).is_some(), "another life is not this one");
    w.inject(0, 4, &notice(inc));
    assert!(w.nodes[0].m.lease_of(&m).is_some(), "a member's notice is not a hub's");
    w.inject(0, 1, &notice(inc));
    assert!(
        w.nodes[0].m.lease_of(&m).is_none(),
        "the same life, no carrier: dropped as left"
    );
    // The member leaves and the close to hub 2 is lost: the hubs that saw it tell hub 2.
    w.leave(4);
    w.close_session(4, 0, LEAVE);
    w.close_session(4, 1, LEAVE);
    w.crash(4);
    w.run(10 * SEC);
    assert!(w.nodes[2].m.lease_of(&id(4)).is_none(), "hub 2 was told");
    for i in 0..3 {
        assert!(!w.has(i, 4), "hub {i} dropped the leaver");
    }
    assert_eq!(
        w.count_events(2, |e| matches!(e, Event::MemberLeft { member } if *member == id(4))),
        1
    );
    w.run(100 * SEC);
    assert_eq!(
        w.count_events(
            2,
            |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(4))
        ),
        0
    );
}

/// The transport's give-up bound decides what a heal is: a hub heard again after longer than the bound.
fn give_up_bound(c: &mut Ctx) {
    let mut w = c.started(2, 2);
    let m = 2;
    for hub in 0..2 {
        w.nodes[m].h.gu.insert(id(hub), 8 * SEC);
    }
    w.run(10 * SEC);
    w.cut.insert((1, m));
    w.cut.insert((1, 0));
    w.run(20 * SEC);
    w.cut.remove(&(1, m));
    w.cut.remove(&(1, 0));
    w.close_session(m, 1, 0);
    w.run(SEC);
    w.connect(m, 1);
    w.run(10 * SEC);
    assert!(
        traces(&w, m, |t| matches!(
            t,
            Trace::Quiet {
                cause: QuietCause::Heal
            }
        )) >= 1,
        "silence past the transport's bound is a heal"
    );
}

/// A node that left sends no HELLO on a new session, and a hub sends a snapshot again only to an attached member.
fn leave_and_resend(c: &mut Ctx) {
    let mut w = c.started(2, 2);
    w.run(5 * SEC);
    w.snapshot_to(0, 2);
    w.snapshot_to(3, 2);
    w.snapshot_to(0, 0);
    w.run(2 * SEC);
    w.leave(3);
    let before = w.nodes[3].h.sent_log.len();
    w.close_session(3, 0, LEAVE);
    w.run(SEC);
    w.connect(3, 0);
    w.run(5 * SEC);
    assert_eq!(w.nodes[3].h.sent_log.len(), before, "a node that left sends nothing");
}

/// The frame body limit a node reads: refused at the default, a partial frame once raised, never below the default.
fn wide_frames(c: &mut Ctx) {
    let mut w = c.started(1, 1);
    w.run(2 * SEC);
    let long = [0u8, 4, 0, 1, 1, 0];
    assert!(w.inject_bytes(0, 1, &long).is_err());
    w.set_max_frame(0, 1 << 20);
    assert_eq!(w.nodes[0].m.max_frame(), 1 << 20);
    assert_eq!(w.inject_bytes(0, 1, &long), Ok(0));
    assert!(w.inject_bytes(0, 1, &[0, 16, 0, 1, 1, 0]).is_err());
    w.set_max_frame(0, 100);
    assert_eq!(w.nodes[0].m.max_frame(), pinc_membership::codec::MAX_BODY);
    assert!(w.inject_bytes(0, 1, &long).is_err());
    w.run(2 * SEC);
}

/// Record every node scenario into `membership.ndjson`.
pub fn run(tw: &mut TraceWriter) {
    let sink: Sink = Rc::new(RefCell::new(Vec::new()));
    let mut c = Ctx {
        run: 0,
        sink: Rc::clone(&sink),
    };
    steady(&mut c);
    churn(&mut c);
    lossy(&mut c);
    lease_end(&mut c);
    partition_heal(&mut c);
    hub_stale_heal(&mut c);
    slow_member(&mut c);
    lost_probe(&mut c);
    probe_paths(&mut c);
    sleeper(&mut c);
    down_proofs(&mut c);
    carrier_return(&mut c);
    revocation(&mut c);
    restarts(&mut c);
    reincarnated(&mut c);
    suspension(&mut c);
    heal_while_waiting(&mut c);
    late_timer_while_waiting(&mut c);
    primary_switch(&mut c);
    stale_view(&mut c);
    address_move(&mut c);
    big_snapshot(&mut c);
    garbage(&mut c);
    leaving(&mut c);
    revoke_full(&mut c);
    give_up_bound(&mut c);
    leave_and_resend(&mut c);
    leave_notice(&mut c);
    wide_frames(&mut c);
    for line in sink.borrow().iter() {
        tw.line(FILE, line);
    }
}
