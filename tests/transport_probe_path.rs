//! A datagram size probe's outcome belongs to the path the probe left on: its acknowledgement raises that path, its
//! loss bars that path from probing and clears its mark, and neither touches the path the session moved to meanwhile;
//! an outcome for a path that is gone, or for a slot a new path took, changes no path and is counted; an echo of a
//! probe that is no longer in flight changes nothing. The first path's probe is held back until the second path is
//! validated, and the session moves to the second path while the probe is out.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{PathId, PathInfo};

vinc_tests::install_counting_allocator!();

/// The size of a path MTU probe on a 1500-byte interface.
const PROBE: usize = 1452;
const PROBE_MTU: u16 = 1452;

/// A connected pair on three routes, the second path added and validated; the first path's size probe waits until 6 s
/// after the start. The first route takes `slow` one way, the second path's interface carries `second` bytes, and the
/// third route (not added yet) takes `third` one way from the first endpoint.
fn two_paths<'a>(
    w: &'a mut World,
    sa: &'a mut Store,
    sb: &'a mut Store,
    seed: u64,
    second: u16,
    (slow, third): (u64, u64),
) -> Net<'a, 'a> {
    // The first path is slower: what the session sends on the second path after the move arrives before the probe.
    let slow = Params::new(slow).mtu(1500);
    let fast = Params::new(10 * MS).mtu(1500);
    let mut link = Link::new(seed, slow);
    link.add_route(PathId(3), PathId(4), fast, fast);
    link.add_route(PathId(5), PathId(6), Params::new(third).mtu(1500), fast);
    let mut net = setup(w, sa, sb, link);
    net.a.conn.defer_mtu_probe(T0 + 6 * SEC);
    assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
    add(&mut net, 3, second);
    assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(3))));
    assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1200));
    assert_eq!(net.a.conn.path_mtu(PathId(3)), Some(1200));
    net
}

/// Add path `id` on an interface of `iface` bytes.
fn add(net: &mut Net<'_, '_>, id: u64, iface: u16) {
    let now = net.now;
    net.a
        .with_env(now, |c, env| {
            c.add_path(
                env,
                PathId(id),
                PathInfo {
                    interface_mtu: iface,
                    ..PathInfo::default()
                },
            )
        })
        .unwrap();
}

/// Run until a size probe has left on path `id`.
fn probe_leaves(net: &mut Net<'_, '_>, id: u64) {
    net.run(T0 + 7 * SEC, |_| false);
    assert!(
        net.run(net.now + 30 * SEC, |n| n
            .a
            .tx_log
            .iter()
            .any(|t| t.1 == PROBE && t.2 == PathId(id))),
        "the size probe never left on path {id}"
    );
}

/// Nothing more is sent on the first route, so the first path cannot be learned again once it is removed. What is
/// already on the way (the probe) still arrives.
fn cut_first_route(net: &mut Net<'_, '_>) {
    net.link.route(PathId(1)).up = false;
}

/// The session moves to the second path and sends on it.
fn move_to_second(net: &mut Net<'_, '_>) {
    net.a.conn.set_active(PathId(3)).unwrap();
    write_on_second(net);
}

/// The large datagrams the first endpoint sent, as (milliseconds, size, path), for the messages of a failure.
fn big_sends(net: &Net<'_, '_>) -> Vec<(u64, usize, PathId)> {
    net.a
        .tx_log
        .iter()
        .filter(|t| t.0 >= T0 + 7 * SEC)
        .map(|t| (t.0 / MS, t.1, t.2))
        .collect()
}

/// (what, milliseconds, packets lost, probe outcomes dropped), for the messages of a failure.
fn snap(net: &Net<'_, '_>, what: &'static str) -> (&'static str, u64, u64, u64) {
    let st = net.a.conn.stats();
    (what, net.now / MS, st.packets_lost, st.probe_outcomes_dropped)
}

/// How many probes the first endpoint sent on the new path.
fn new_path_probes(net: &Net<'_, '_>) -> usize {
    net.a.tx_log.iter().filter(|t| t.1 == PROBE && t.2 == PathId(5)).count()
}

/// Send a little on the active path.
fn write_on_second(net: &mut Net<'_, '_>) {
    let id = net.a.conn.open_uni().unwrap();
    net.a.conn.write(id, &pattern(100, 3)).unwrap();
}

#[test]
fn a_probe_acknowledged_after_the_session_moved_raises_the_path_it_left_on() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // The second path's interface carries 1372 bytes: it is never probed, so any rise of it is a misrouted one.
        let mut net = two_paths(&mut w, &mut sa, &mut sb, 61, 1400, (40 * MS, 10 * MS));
        probe_leaves(&mut net, 1);
        net.a.conn.set_active(PathId(3)).unwrap();
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(
            net.a.conn.path_mtu(PathId(3)),
            Some(1200),
            "the path the session moved to was raised by a probe it never sent"
        );
        assert_eq!(
            net.a.conn.path_mtu(PathId(1)),
            Some(PROBE_MTU),
            "the path the probe left on was not raised"
        );
        assert_eq!(net.a.conn.stats().probe_outcomes_dropped, 0);
    });
}

#[test]
fn a_probe_lost_after_the_session_moved_bars_the_path_it_left_on_and_not_the_new_one() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = two_paths(&mut w, &mut sa, &mut sb, 62, 1500, (40 * MS, 10 * MS));
        // The first path carries 1200 bytes from now on: the probe is dropped by the link.
        let small = Params::new(40 * MS).mtu(1200);
        net.link.set(PathId(1), small, small);
        probe_leaves(&mut net, 1);
        let lost_before = net.a.conn.stats().packets_lost;
        let mut trail = vec![snap(&net, "probe left")];
        move_to_second(&mut net);
        // The probe is declared lost on the first path; the second path is not barred for 600 s and probes.
        assert!(
            net.run(net.now + 5 * SEC, |n| n.a.conn.path_mtu(PathId(3)) == Some(PROBE_MTU)),
            "the path the session moved to was barred by a probe it never sent (size {:?})",
            net.a.conn.path_mtu(PathId(3))
        );
        trail.push(snap(&net, "second path probed"));
        assert_eq!(
            net.a.conn.stats().probe_outcomes_dropped,
            0,
            "after the second path probed: {trail:?}, {:?}",
            big_sends(&net)
        );
        assert!(
            net.run(net.now + 5 * SEC, |n| n.a.conn.stats().packets_lost > lost_before),
            "the probe of the first path was never declared lost"
        );
        trail.push(snap(&net, "loss seen"));
        // The first path's mark was cleared by that loss: after a path event it probes again.
        let big = Params::new(40 * MS).mtu(1500);
        net.link.set(PathId(1), big, big);
        net.a.conn.set_active(PathId(1)).unwrap();
        trail.push(snap(&net, "first path active"));
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        trail.push(snap(&net, "link toggled"));
        assert!(
            net.run(net.now + 30 * SEC, |n| n.a.conn.path_mtu(PathId(1)) == Some(PROBE_MTU)),
            "the first path never probed again (size {:?})",
            net.a.conn.path_mtu(PathId(1))
        );
        trail.push(snap(&net, "first path probed"));
        // Dropped: the flush of the link return declares the second path's probe lost, and its echo had already raised
        // that path and cleared the mark. The first path's own loss matched its probe, so it is not counted.
        assert_eq!(net.a.conn.stats().probe_outcomes_dropped, 1, "{trail:?}");
    });
}

/// The session moved to the second path, the first path was removed while its probe is out, and a new path took its
/// slot, became the active path and sent a probe of the same size (500 ms from the peer). The first path's probe is not
/// resolved yet.
fn replace_first_path(net: &mut Net<'_, '_>) {
    net.a.conn.set_active(PathId(3)).unwrap();
    net.a.conn.remove_path(PathId(1)).unwrap();
    assert!(!net.a.conn.has_path(PathId(1)));
    add(net, 5, 1500);
    assert!(
        net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(5))),
        "the new path never validated"
    );
    // The new path's own probe reaches the peer 500 ms later, so it stays in flight while the first path's outcome
    // arrives, and its own acknowledgement comes last (before the probe timeout declares anything lost).
    let (to_peer, back) = (Params::new(500 * MS).mtu(1500), Params::new(10 * MS).mtu(1500));
    net.link.set(PathId(5), to_peer, back);
    net.a.conn.set_active(PathId(5)).unwrap();
    assert!(
        net.run(net.now + 2 * SEC, |n| n
            .a
            .tx_log
            .iter()
            .any(|t| t.1 == PROBE && t.2 == PathId(5))),
        "the new path never sent its probe (size {:?}, {:?})",
        net.a.conn.path_mtu(PathId(5)),
        net.a.conn.stats()
    );
    assert_eq!(net.a.conn.path_mtu(PathId(5)), Some(1200));
    assert_eq!(net.a.conn.stats().probe_outcomes_dropped, 0);
}

#[test]
fn a_probe_acknowledged_for_a_path_that_is_gone_is_counted_and_changes_no_path() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = two_paths(&mut w, &mut sa, &mut sb, 63, 1400, (40 * MS, 10 * MS));
        probe_leaves(&mut net, 1);
        cut_first_route(&mut net);
        // The peer follows the session onto the second path before the probe reaches it and answers there.
        move_to_second(&mut net);
        net.a.conn.remove_path(PathId(1)).unwrap();
        net.run(net.now + 2 * SEC, |_| false);
        assert!(!net.a.conn.has_path(PathId(1)));
        assert_eq!(
            net.a.conn.path_mtu(PathId(3)),
            Some(1200),
            "a probe of a path that is gone raised the path that is left"
        );
        assert_eq!(net.a.conn.stats().probe_outcomes_dropped, 1, "{:?}", net.a.conn.stats());
    });
}

#[test]
fn a_probe_lost_for_a_path_that_is_gone_is_counted_and_bars_no_path() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = two_paths(&mut w, &mut sa, &mut sb, 64, 1500, (40 * MS, 10 * MS));
        let small = Params::new(40 * MS).mtu(1200);
        net.link.set(PathId(1), small, small);
        probe_leaves(&mut net, 1);
        cut_first_route(&mut net);
        move_to_second(&mut net);
        net.a.conn.remove_path(PathId(1)).unwrap();
        assert!(
            net.run(net.now + 5 * SEC, |n| n.a.conn.path_mtu(PathId(3)) == Some(PROBE_MTU)),
            "the path that is left was barred by a probe of a path that is gone (size {:?})",
            net.a.conn.path_mtu(PathId(3))
        );
        assert_eq!(net.a.conn.stats().probe_outcomes_dropped, 1, "{:?}", net.a.conn.stats());
    });
}

#[test]
fn the_acknowledgement_of_a_probe_of_a_path_that_is_gone_does_not_raise_the_new_path_in_its_slot() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // The first probe's acknowledgement comes after the new path's probe left and before that probe's own.
        let mut net = two_paths(&mut w, &mut sa, &mut sb, 65, 1400, (40 * MS, 10 * MS));
        // The peer answers on the route the probe came on, which takes 250 ms to come back.
        net.link.set(
            PathId(1),
            Params::new(40 * MS).mtu(1500),
            Params::new(250 * MS).mtu(1500),
        );
        probe_leaves(&mut net, 1);
        replace_first_path(&mut net);
        assert!(
            net.run(net.now + 5 * SEC, |n| n.a.conn.stats().probe_outcomes_dropped == 1),
            "the first probe's acknowledgement never arrived or was applied to the new path: {:?}",
            net.a.conn.stats()
        );
        assert_eq!(
            net.a.conn.path_mtu(PathId(5)),
            Some(1200),
            "the new path was raised by the acknowledgement of the probe of the path that was in its slot, now {} ms, {:?}",
            net.now / MS,
            big_sends(&net)
        );
        // The new path's own probe is still in flight: its own acknowledgement raises it, and it is not sent again.
        assert!(
            net.run(net.now + 10 * SEC, |n| n.a.conn.path_mtu(PathId(5)) == Some(PROBE_MTU)),
            "the new path's own probe was cleared by the other path's acknowledgement (size {:?}), now {} ms, {:?}, {:?}",
            net.a.conn.path_mtu(PathId(5)),
            net.now / MS,
            net.a.conn.stats(),
            big_sends(&net)
        );
        assert_eq!(net.a.conn.stats().probe_outcomes_dropped, 1);
        assert_eq!(new_path_probes(&net), 1);
    });
}

#[test]
fn the_loss_of_a_probe_of_a_path_that_is_gone_does_not_bar_the_new_path_in_its_slot() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = two_paths(&mut w, &mut sa, &mut sb, 66, 1500, (200 * MS, 10 * MS));
        // The first probe is dropped by the link.
        let small = Params::new(200 * MS).mtu(1200);
        net.link.set(PathId(1), small, small);
        probe_leaves(&mut net, 1);
        // The session sends on the second path, whose acknowledgements take 300 ms: they declare the first probe lost
        // only after the new path took the first path's slot and sent its own probe.
        let slow = Params::new(10 * MS).mtu(1500);
        net.link.set(PathId(3), slow, Params::new(300 * MS).mtu(1500));
        move_to_second(&mut net);
        replace_first_path(&mut net);
        assert!(
            net.run(net.now + 5 * SEC, |n| n.a.conn.stats().probe_outcomes_dropped == 1),
            "the first probe's loss never arrived or was applied to the new path: {:?}",
            net.a.conn.stats()
        );
        assert_eq!(net.a.conn.path_mtu(PathId(5)), Some(1200));
        // The new path's own probe is still in flight: its own acknowledgement raises it, which a bar would prevent.
        assert!(
            net.run(net.now + 10 * SEC, |n| n.a.conn.path_mtu(PathId(5)) == Some(PROBE_MTU)),
            "the new path was barred or its probe cleared by the loss of the other path's probe (size {:?}), now {} ms, {:?}, {:?}",
            net.a.conn.path_mtu(PathId(5)),
            net.now / MS,
            net.a.conn.stats(),
            big_sends(&net)
        );
        assert_eq!(net.a.conn.stats().probe_outcomes_dropped, 1);
        assert_eq!(new_path_probes(&net), 1);
    });
}

#[test]
fn an_echo_that_arrives_after_its_probe_was_declared_lost_changes_no_size() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = two_paths(&mut w, &mut sa, &mut sb, 67, 1400, (40 * MS, 10 * MS));
        probe_leaves(&mut net, 1);
        // The peer answers the probe on the first path, but the answer (the acknowledgement and the echo) takes 1.5 s;
        // meanwhile the link returns, which declares every packet in flight lost and keeps the path from probing again
        // for a while.
        net.link.set(
            PathId(1),
            Params::new(40 * MS).mtu(1500),
            Params::new(1500 * MS).mtu(1500),
        );
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        net.run(net.now + 4 * SEC, |_| false);
        assert_eq!(
            net.a.conn.path_mtu(PathId(1)),
            Some(1200),
            "an echo of a probe that was no longer in flight raised the path"
        );
    });
}
