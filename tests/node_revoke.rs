//! Revocation, graceful leave and incarnations over real sessions.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod node_common;

use node_common::{World, big, secs};
use vinc_core::{Answer, Query};
use vinc_membership::Event;
use vinc_sim::{NodeId as SimId, SEC};
use vinc_tests::NCmd;

/// How many sessions of `n` are with the node `peer`.
fn sessions_with(w: &World, n: SimId, peer: &[u8; 32]) -> usize {
    let node = &w.sim.node(n).node;
    let mut i = 0;
    let mut count = 0;
    while let Answer::Stats(st) = node.endpoint().query(Query::SessionAt(i)) {
        i += 1;
        if st.node.is_some_and(|x| x.bytes == *peer) {
            count += 1;
        }
    }
    count
}

#[test]
fn a_revoked_member_loses_every_session_within_five_seconds() {
    big(|| {
        for seed in [111u64, 112, 113] {
            let mut w = World::build(seed, 3, 5);
            let target = w.members[0];
            let id = w.id(target);
            let others: Vec<SimId> = w.hubs.iter().map(|(n, _)| *n).chain(w.members[1..].iter().copied()).collect();
            w.run(secs(40));
            for n in &others {
                assert!(w.view(*n).contains(&id), "seed {seed}: {n:?} does not list the member before the revocation");
            }
            for n in &others {
                w.sim.command(secs(40), *n, NCmd::Revoke(id));
            }
            w.run(secs(45));
            for n in &others {
                assert!(!w.view(*n).contains(&id), "seed {seed}: {n:?} still lists the revoked member");
                assert!(
                    w.member_events(*n).iter().any(|(t, e)| matches!(e, Event::MemberRevoked { member } if *member == id) && *t <= secs(40) + 5 * SEC),
                    "seed {seed}: {n:?} did not report the revocation within 5 s"
                );
                assert_eq!(sessions_with(&w, *n, &id), 0, "seed {seed}: {n:?} still holds a session with the revoked member");
            }
            // The revoked member does not come back.
            w.run(secs(160));
            for n in &others {
                assert!(!w.view(*n).contains(&id), "seed {seed}: {n:?} lists the revoked member again");
                assert_eq!(sessions_with(&w, *n, &id), 0, "seed {seed}: {n:?} accepted a session from the revoked member");
            }
        }
    });
}

#[test]
fn a_graceful_leave_is_reported_as_left_within_seconds() {
    big(|| {
        for seed in [121u64, 122] {
            let mut w = World::build(seed, 3, 5);
            let leaver = w.members[2];
            let id = w.id(leaver);
            let others: Vec<SimId> = w.hubs.iter().map(|(n, _)| *n).chain(w.members.iter().copied().filter(|m| *m != leaver)).collect();
            w.sim.command(secs(40), leaver, NCmd::Leave);
            w.run(secs(60));
            for n in &others {
                let left = w.left(*n, &id);
                assert_eq!(left.len(), 1, "seed {seed}: {n:?} reported the leave {left:?}");
                assert!(left[0] <= secs(40) + 3 * SEC, "seed {seed}: {n:?} reported the leave at {:?}", left[0]);
                assert!(w.confirmed_down(*n, &id).is_empty(), "seed {seed}: {n:?} reported the leave as a failure");
                assert!(!w.view(*n).contains(&id));
            }
        }
    });
}

#[test]
fn incarnations_only_go_up_across_restarts_and_clock_jumps() {
    big(|| {
        for seed in [131u64, 132] {
            // A counter sealed in the key store for the first member, a hybrid logical clock for the second.
            let mut w = World::build_with(seed, 3, 0, |w| w.persist = false);
            let hubs = w.hub_addrs();
            let counted = {
                w.persist = true;
                w.add_member(0x60, &hubs, 0)
            };
            let clocked = {
                w.persist = false;
                w.add_member(0x61, &hubs, 0)
            };
            for t in [40u64, 70, 100] {
                w.sim.crash(secs(t), counted);
                w.sim.restart(secs(t + 5), counted);
            }
            // The clock goes back an hour while the second member is down; it restarts without state.
            w.sim.crash(secs(50), clocked);
            w.sim.clock_jump(secs(52), clocked, -3_600 * SEC.cast_signed());
            w.sim.restart(secs(60), clocked);
            // And forward two hours while it runs.
            w.sim.clock_jump(secs(90), clocked, 7_200 * SEC.cast_signed());
            w.run(secs(200));
            for n in [counted, clocked] {
                let incs = &w.sim.node(n).incarnations;
                let epochs: Vec<u64> = incs.iter().map(|i| i >> 16).collect();
                let last = *incs.last().unwrap();
                // Whatever the node announced at the start of a life, it ends above everything it announced before.
                assert!(incs.iter().all(|i| *i <= last || (*i >> 16) <= (last >> 16)), "seed {seed}: {n:?} {epochs:?}");
                let id = w.id(n);
                // And the hubs hold the node's current record, never an older one.
                for (h, _) in &w.hubs {
                    let held = w.sim.node(*h).node.membership().members().find(|(m, _)| **m == id).map(|(_, r)| r.inc);
                    assert_eq!(held.map(|i| i >> 16), Some(last >> 16), "seed {seed}: hub {h:?} holds an old life of {n:?}");
                }
            }
            // The sealed counter goes up by exactly one per restart.
            let epochs: Vec<u64> = w.sim.node(counted).incarnations.iter().map(|i| i >> 16).collect();
            let mut lives = epochs.clone();
            lives.dedup();
            for pair in lives.windows(2) {
                assert!(pair[1] > pair[0], "seed {seed}: the sealed counter went back: {lives:?}");
            }
            assert_eq!(lives.len(), 4, "seed {seed}: {lives:?}");
        }
    });
}
