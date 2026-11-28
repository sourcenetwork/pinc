//! The paths a responder owes its first flight to: the ones its first message completed on, never given back to the
//! host, never kept for a path that left the table, and the only ones the Finish validates.
#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{PathId, PathInfo};
use pinc_transport::recovery::PathKind;

/// A pair whose first flight leaves on paths 1 and 3, so the responder owes its Reply to its paths 2 and 4, stopped
/// when the responder holds both and has not seen the Finish.
fn owed_two<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store, seed: u64) -> Net<'a, 'a> {
    let mut link = Link::new(seed, Params::new(10 * MS));
    link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
    link.add_route(PathId(5), PathId(6), Params::new(10 * MS), Params::new(10 * MS));
    link.add_route(PathId(7), PathId(8), Params::new(10 * MS), Params::new(10 * MS));
    let mut net = setup(w, sa, sb, link);
    let now = net.now;
    net.a
        .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
        .unwrap();
    net.a.conn.set_flight_fanout(&[PathId(3)]);
    assert!(net.run(now + SEC, |n| n.b.conn.has_path(PathId(4))));
    assert!(!net.b.conn.is_connected());
    net
}

/// An owed path the host removed is not owed any more: the Finish finds one owed path and validates it.
#[test]
fn a_removed_owed_path_is_not_owed_at_the_finish() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = owed_two(&mut w, &mut sa, &mut sb, 96);
        let now = net.now;
        net.b.conn.remove_path(PathId(4)).unwrap();
        assert!(net.run(now + 5 * SEC, |n| n.b.conn.is_connected()));
        assert!(
            net.b.conn.path_validated(PathId(2)),
            "the lone owed path is not validated"
        );
    });
}

/// An owed path that left the table does not stay owed: the path that takes its slot is not validated by the Finish
/// and gets no copy of the flight.
#[test]
fn a_path_that_took_the_slot_of_an_owed_path_is_not_owed() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = owed_two(&mut w, &mut sa, &mut sb, 91);
        let now = net.now;
        net.b.conn.remove_path(PathId(4)).unwrap();
        net.b
            .with_env(now, |c, env| c.add_path(env, PathId(6), PathInfo::default()))
            .unwrap();
        assert!(net.run(now + 5 * SEC, |n| n.b.conn.is_connected()));
        // The one path still owed is the one the Finish answered, so it is validated and the other is not.
        assert!(
            net.b.conn.path_validated(PathId(2)),
            "the lone owed path is not validated"
        );
        assert!(!net.b.conn.path_validated(PathId(6)));
        assert!(
            net.b.tx_log.iter().all(|(_, _, p)| *p != PathId(6)),
            "the path that took the slot got a packet"
        );
    });
}

/// An owed path whose local address is gone leaves the table with its owed bit: the path that takes its slot is not
/// validated by the Finish and gets no copy of the flight.
#[test]
fn a_gone_local_address_clears_what_its_path_was_owed() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = owed_two(&mut w, &mut sa, &mut sb, 97);
        let now = net.now;
        net.b.conn.path_lost(PathId(4)).unwrap();
        assert!(!net.b.conn.has_path(PathId(4)), "the gone path stayed in the table");
        net.b
            .with_env(now, |c, env| c.add_path(env, PathId(6), PathInfo::default()))
            .unwrap();
        assert!(net.run(now + 5 * SEC, |n| n.b.conn.is_connected()));
        assert!(
            net.b.conn.path_validated(PathId(2)),
            "the lone owed path is not validated"
        );
        assert!(!net.b.conn.path_validated(PathId(6)));
        assert!(
            net.b.tx_log.iter().all(|(_, _, p)| *p != PathId(6)),
            "the path that took the slot got a packet"
        );
    });
}

/// With two paths owed, a copy of the Finish proves neither (any source can repeat it): none is validated by it, and
/// the active path is not validated in their place.
#[test]
fn a_finish_with_two_owed_paths_validates_none() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = owed_two(&mut w, &mut sa, &mut sb, 95);
        let now = net.now;
        assert!(net.run(now + 5 * SEC, |n| n.b.conn.is_connected()));
        assert!(
            !net.b.conn.path_validated(PathId(2)),
            "the active path was validated by the Finish"
        );
        assert!(
            !net.b.conn.path_validated(PathId(4)),
            "an owed path was validated by the Finish"
        );
    });
}

/// An owed relay path is valid from the moment it is tracked and is never challenged: of two owed paths, one through a
/// relay, the Finish challenges only the direct one, and from the establishment on nothing leaves on the relay path at
/// either end (its slow way back keeps the Reply's copy there behind the Finish, which leaves on the direct path).
#[test]
fn an_owed_relay_path_is_not_challenged_at_the_finish() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(95, Params::new(10 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(40 * MS));
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let relay = PathInfo {
            kind: PathKind::Relay,
            ..PathInfo::default()
        };
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), relay)).unwrap();
        net.a.conn.set_flight_fanout(&[PathId(3)]);
        assert!(net.run(now + SEC, |n| n.b.conn.has_path(PathId(4))));
        net.b.conn.set_path_info(PathId(4), relay);
        assert!(net.run(net.now + 5 * SEC, |n| n.b.conn.is_connected()));
        let at = net.now;
        assert!(
            net.run(at + 5 * SEC, |n| n.b.conn.path_validated(PathId(2))),
            "the direct path is validated"
        );
        net.run(net.now + SEC, |_| false);
        assert!(net.b.conn.path_validated(PathId(4)), "the relay path is valid");
        let after = |log: &[(u64, usize, PathId)], p| log.iter().filter(|(t, _, q)| *t >= at && *q == p).count();
        assert_eq!(after(&net.b.tx_log, PathId(4)), 0, "the relay path was challenged");
        assert_eq!(
            after(&net.a.tx_log, PathId(3)),
            0,
            "a challenge was answered on the relay path"
        );
    });
}

/// The host names a path for the flight: the paths the first message completed on stay owed, so the Finish proves
/// none of the owed paths and a path only the host named is never validated by it.
#[test]
fn a_path_only_the_host_named_is_not_validated_by_the_finish() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(92, Params::new(10 * MS));
        link.add_route(PathId(7), PathId(8), Params::new(10 * MS), Params::new(10 * MS));
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        assert!(net.run(now + SEC, |n| n.b.conn.has_path(PathId(2))));
        let t = net.now;
        net.b
            .with_env(t, |c, env| c.add_path(env, PathId(8), PathInfo::default()))
            .unwrap();
        net.b.conn.set_flight_fanout(&[PathId(8)]);
        assert!(net.run(t + 5 * SEC, |n| n.b.conn.is_connected()));
        assert!(
            !net.b.conn.path_validated(PathId(8)),
            "a path only the host named is validated"
        );
    });
}

/// The flight reaches both paths its first message completed on, each within three times what arrived on it: the
/// dialer's resend is the second copy, and the Reply it did not get on the first path is sent again.
#[test]
fn the_flight_leaves_on_both_owed_paths_within_both_budgets() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(94, Params::new(10 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
        // The Reply never comes back on the first path, so the dialer sends its flight again.
        link.route(PathId(1)).ba.p.loss_ppm = 1_000_000;
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        net.a.conn.set_flight_fanout(&[PathId(3)]);
        assert!(net.run(now + 5 * SEC, |n| n.b.tx_log.iter().any(|(_, _, q)| *q == PathId(4))));
        for p in [PathId(2), PathId(4)] {
            assert!(
                net.b.tx_log.iter().any(|(_, _, q)| *q == p),
                "path {p:?} got no copy of the flight"
            );
            let s = net
                .b
                .conn
                .trace_paths()
                .slots
                .into_iter()
                .flatten()
                .find(|s| s.id == p.0)
                .unwrap();
            assert!(
                s.amp_sent <= 3 * s.amp_received,
                "{p:?}: {} sent on {} received",
                s.amp_sent,
                s.amp_received
            );
        }
    });
}

/// Every path of a full table is owed the flight (the host named them): none is given up for a new one, the new one
/// is refused and the refusal is counted.
#[test]
fn an_owed_path_is_never_given_up_for_a_new_one() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(93, Params::new(10 * MS)));
        let now = net.now;
        assert!(net.run(now + SEC, |n| n.b.conn.has_path(PathId(2))));
        let t = net.now;
        let ids: Vec<PathId> = (21..24).map(PathId).collect();
        for id in &ids {
            net.b
                .with_env(t, |c, env| c.add_path(env, *id, PathInfo::default()))
                .unwrap();
        }
        net.b.conn.set_flight_fanout(&ids);
        assert_eq!(net.b.conn.stats().paths_owed_full, 0);
        let r = net
            .b
            .with_env(t, |c, env| c.add_path(env, PathId(100), PathInfo::default()));
        assert!(r.is_err(), "a new path took the place of an owed one");
        assert!(
            ids.iter().all(|id| net.b.conn.has_path(*id)),
            "an owed path was given up"
        );
        assert_eq!(net.b.conn.stats().paths_owed_full, 1);
    });
}

/// A responder whose only owed target is its active path never skips it for want of budget. The first message
/// completes on path 3 (its first datagram lost there, its second lost on path 1), where only 1173 bytes arrived, so
/// the Hybrid Reply is larger than the room of that path and stops after three datagrams. When the dialer repeats its
/// first flight the Reply goes on on that path from where it stopped (its next datagrams there are the rest of the
/// flight, not the first 1200 bytes again) and leaves on it before any other path. Pins the `fan_step` rule that the
/// only target is never skipped: without it the flight is stopped for the other path and starts again from its
/// first byte.
#[test]
fn the_only_owed_target_is_never_skipped_for_want_of_budget() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Hybrid);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(98, Params::new(10 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
        link.route(PathId(1)).ab.drop_index(2);
        link.route(PathId(3)).ab.drop_index(1);
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        net.a.conn.set_flight_fanout(&[PathId(3)]);
        assert!(net.run(now + 5 * SEC, |n| n.a.conn.is_connected() && n.b.conn.is_connected()));
        let repeat = now + 100 * MS;
        let before: Vec<usize> = net
            .b
            .tx_log
            .iter()
            .filter(|(t, _, _)| *t < repeat)
            .map(|(_, l, _)| *l)
            .collect();
        assert_eq!(before.len(), 3, "the Reply did not stop for want of room: {before:?}");
        let after: Vec<(usize, PathId)> = net
            .b
            .tx_log
            .iter()
            .filter(|(t, _, _)| *t >= repeat)
            .map(|(_, l, p)| (*l, *p))
            .collect();
        assert_eq!(
            after[0].1,
            PathId(4),
            "the flight did not go on on the only owed path first: {after:?}"
        );
        // A flight that started again would begin with full datagrams of its first bytes: it goes on with the rest.
        assert_ne!(
            after[2].0, 1200,
            "the flight started again from its first byte: {after:?}"
        );
    });
}
