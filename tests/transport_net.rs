//! Network events of the VINCER connection: path MTU discovery, key updates, migration, NAT rebinding, path
//! validation, and the choice between relay and direct paths.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::manual_assert_eq, // a failing comparison of megabytes must not print them
    clippy::cast_precision_loss
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{PathId, PathInfo};
use vinc_transport::frame::ext;
use vinc_transport::recovery::PathKind;

fn connected<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store, link: Link) -> Net<'a, 'a> {
    let mut net = setup(w, sa, sb, link);
    assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
    net
}

#[test]
fn pmtu_rises_to_1452() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(1, Params::new(10 * MS).mtu(1500)));
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1452));
        assert_eq!(net.b.conn.path_mtu(PathId(2)), Some(1452));
        assert_eq!(net.a.conn.stats().mtu, 1452);
    });
}

#[test]
fn pmtu_stays_when_the_link_is_smaller() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(2, Params::new(10 * MS).mtu(1300)));
        net.run(net.now + 5 * SEC, |_| false);
        assert_eq!(
            net.a.conn.path_mtu(PathId(1)),
            Some(1200),
            "a lost probe is not a reason to grow, nor a congestion event"
        );
        let data = pattern(1 << 20, 3);
        bulk(&mut net, &data, 60 * SEC);
        assert!(
            net.a.conn.stats().cwnd >= 40_000,
            "a lost probe is not a congestion event"
        );
    });
}

#[test]
fn pmtu_jumbo_on_a_low_latency_path() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(3, Params::new(MS / 2).mtu(9000)));
        let jumbo = PathInfo {
            interface_mtu: 9000,
            ..PathInfo::default()
        };
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(1), jumbo)).unwrap();
        net.b.with_env(now, |c, env| c.add_path(env, PathId(2), jumbo)).unwrap();
        net.run(net.now + 3 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(8952));
        let data = pattern(4 << 20, 4);
        bulk(&mut net, &data, 60 * SEC);
        assert!(
            net.a.tx_log.iter().any(|t| t.1 > 8000),
            "large datagrams carry the data"
        );
    });
}

#[test]
fn black_hole_falls_back_to_the_minimum_size() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(5, Params::new(10 * MS).mtu(1500)));
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1452));
        // The path shrinks under a running transfer: full-size packets vanish.
        let data = pattern(3 << 20, 6);
        let id = net.a.conn.open_bi().unwrap();
        let mut off = 0;
        let mut shrunk = false;
        let mut finished = false;
        let ok = net.run(net.now + 120 * SEC, |n| {
            if !shrunk && n.b.read.get(&id).map_or(0, Vec::len) > (1 << 20) {
                n.link.set(
                    PathId(1),
                    Params::new(10 * MS).mtu(1300),
                    Params::new(10 * MS).mtu(1300),
                );
                shrunk = true;
            }
            while off < data.len() {
                let k = n.a.conn.write(id, &data[off..]).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            if off == data.len() && !finished {
                n.a.conn.finish(id).unwrap();
                finished = true;
            }
            n.b.fin.contains(&id)
        });
        assert!(ok && shrunk, "the transfer must survive the shrink");
        assert!(net.b.read[&id] == data);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1200));
    });
}

#[test]
fn key_update_during_a_transfer() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.key_update_after = 300;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let p = Params::new(5 * MS).loss(1.0).reorder(2.0, 4 * MS);
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(7, p));
        let data = pattern(12 << 20, 8);
        let (_, id) = bulk(&mut net, &data, 600 * SEC);
        let back = pattern(3 << 20, 9);
        // And the other way, so both directions update.
        let id2 = net.b.conn.open_bi().unwrap();
        let mut off = 0;
        let ok = net.run(net.now + 600 * SEC, |n| {
            while off < back.len() {
                let k = n.b.conn.write(id2, &back[off..]).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            if off == back.len() {
                n.b.conn.finish(id2).ok();
            }
            n.a.fin.contains(&id2)
        });
        assert!(ok && net.a.read[&id2] == back && net.b.read[&id] == data);
        let (sa, sb) = (net.a.conn.stats(), net.b.conn.stats());
        assert!(
            sa.key_updates >= 4 && sb.key_updates >= 4,
            "{} {}",
            sa.key_updates,
            sb.key_updates
        );
        assert_eq!(
            sa.undecryptable + sb.undecryptable,
            0,
            "no packet may be lost to a key change"
        );
    });
}

fn two_routes(seed: u64, second: Params) -> Link {
    let mut link = Link::new(seed, Params::new(10 * MS));
    link.add_route(PathId(3), PathId(4), second, second);
    link
}

#[test]
fn migration_to_a_new_validated_path() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, two_routes(10, Params::new(10 * MS)));
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        assert!(net.run(net.now + 5 * SEC, |n| n.a.saw(|r| *r == Rec::PathValidated(PathId(3)))));
        // The server validated the client's new address too, and nothing moved on its own.
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        net.a.conn.set_active(PathId(3)).unwrap();
        let data = pattern(3 << 20, 11);
        bulk(&mut net, &data, 60 * SEC);
        assert_eq!(
            net.b.conn.active_path(),
            Some(PathId(4)),
            "the server follows the packets"
        );
        let used = net.link.routes[1].ab.sent;
        assert!(used > 1000, "the new route carries the data: {used}");
        assert!(
            net.link.routes[0].ab.sent < 400,
            "the old route went quiet: {}",
            net.link.routes[0].ab.sent
        );
    });
}

#[test]
fn a_path_rebound_to_a_new_local_address_carries_the_wake_and_the_resent_data_at_once() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(14, Params::new(150 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(150 * MS), Params::new(150 * MS));
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let (up, down) = (net.a.conn.open_bi().unwrap(), net.b.conn.open_bi().unwrap());
        let (to_server, to_client) = (pattern(3000, 5), pattern(3000, 6));
        // Both sides send, and the client's old address then goes away: both segments are lost on the old route.
        net.link.route(PathId(1)).up = false;
        net.a.conn.write(up, &to_server).unwrap();
        net.b.conn.write(down, &to_client).unwrap();
        net.run(net.now + MS, |_| false);
        let ptos_before = (net.a.conn.stats().ptos, net.b.conn.stats().ptos);
        let now = net.now;
        let sent_before = net.a.tx_log.len();
        // The client's address changes and the link returns in one step: its path keeps everything it knows and leaves
        // from the new address.
        net.a.with_env(now, |c, env| {
            c.rebind_path(PathId(1), PathId(3)).unwrap();
            c.set_link_down(env, true);
            c.set_link_down(env, false);
        });
        net.run(now, |_| false);
        assert!(net.a.conn.path_validated(PathId(3)), "the path keeps its state");
        assert_eq!(net.a.conn.active_path(), Some(PathId(3)));
        let first: Vec<_> = net.a.tx_log[sent_before..].iter().filter(|t| t.0 == now).collect();
        assert!(
            first.len() >= 2,
            "the wake and the client's own data leave in the step of the move: {first:?}"
        );
        assert!(
            first.iter().all(|t| t.2 == PathId(3)),
            "nothing leaves from the old address: {first:?}"
        );
        // One round trip is 300 ms: the server resends on the wake at once, and neither probe timeout could have fired.
        assert!(
            net.run(now + 450 * MS, |n| {
                n.a.read.get(&down).is_some_and(|d| d.len() == to_client.len())
                    && n.b.read.get(&up).is_some_and(|d| d.len() == to_server.len())
            }),
            "both segments arrive within one round trip of the move"
        );
        assert_eq!(
            (net.a.conn.stats().ptos, net.b.conn.stats().ptos),
            ptos_before,
            "no probe timeout fired"
        );
    });
}

#[test]
fn nat_rebinding_keeps_the_transfer_alive() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(12, Params::new(10 * MS).loss(0.5)));
        let data = pattern(6 << 20, 13);
        let id = net.a.conn.open_bi().unwrap();
        let (mut off, mut rebound, mut finished) = (0, false, false);
        let ok = net.run(net.now + 120 * SEC, |n| {
            if !rebound && n.b.read.get(&id).map_or(0, Vec::len) > (1 << 20) {
                n.link.rebind(PathId(1), PathId(9));
                rebound = true;
            }
            while off < data.len() {
                let k = n.a.conn.write(id, &data[off..]).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            if off == data.len() && !finished {
                n.a.conn.finish(id).unwrap();
                finished = true;
            }
            n.b.fin.contains(&id)
        });
        assert!(ok && rebound);
        assert!(net.b.read[&id] == data);
        assert_eq!(net.b.conn.active_path(), Some(PathId(9)));
        assert!(net.b.saw(|r| *r == Rec::PathValidated(PathId(9))));
    });
}

#[test]
fn a_path_that_never_answers_gets_nine_small_probes_and_stays_unvalidated() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = two_routes(14, Params::new(10 * MS));
        link.route(PathId(3)).up = false;
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        net.run(net.now + 30 * SEC, |_| false);
        // There is no failed state: nine probes on the doubling cadence, then the path just stays unvalidated.
        assert!(!net.a.saw(|r| *r == Rec::PathFailed(PathId(3))));
        assert!(!net.a.conn.path_validated(PathId(3)));
        assert!(net.a.conn.set_active(PathId(3)).is_err());
        let probes: Vec<usize> = net.a.tx_log.iter().filter(|t| t.2 == PathId(3)).map(|t| t.1).collect();
        assert_eq!(probes.len(), 9, "{probes:?}");
        assert!(
            probes.iter().all(|len| *len < 100),
            "challenges are not padded: {probes:?}"
        );
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        let data = pattern(1 << 20, 15);
        bulk(&mut net, &data, 60 * SEC);
    });
}

#[test]
fn a_ping_on_a_standby_path_keeps_it_alive_and_leaves_its_round_trip_and_the_choice_alone() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(18, Params::new(100 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(100 * MS), Params::new(100 * MS));
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        net.b
            .with_env(now, |c, env| c.add_path(env, PathId(4), PathInfo::default()))
            .unwrap();
        assert!(net.run(net.now + 10 * SEC, |n| n.a.saw(|r| *r == Rec::PathValidated(PathId(3)))));
        net.run(net.now + SEC, |_| false);
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        let slow = net.a.conn.path_rtt(PathId(3)).unwrap();
        assert!(slow > 150 * MS, "{slow}");
        // The standby path gets much faster; a keepalive on it must not notice.
        net.link.set(PathId(3), Params::new(10 * MS), Params::new(10 * MS));
        let sent = net.a.tx_log.iter().filter(|t| t.2 == PathId(3)).count();
        net.a.conn.ping_path(PathId(3)).unwrap();
        net.run(net.now + 3 * SEC, |_| false);
        assert!(
            net.a.tx_log.iter().filter(|t| t.2 == PathId(3)).count() > sent,
            "the ping left on the standby path"
        );
        assert_eq!(net.a.conn.path_rtt(PathId(3)), Some(slow));
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        // A challenge on it does measure the new round trip, and the faster path takes over.
        let now = net.now;
        net.a.with_env(now, |c, env| c.probe(env, PathId(3))).unwrap();
        assert!(net.run(net.now + 10 * SEC, |n| n.a.conn.active_path() == Some(PathId(3))));
    });
}

#[test]
fn relay_carries_a_penalty_and_takes_over_when_the_direct_path_dies() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // Direct: 200 ms round trip. Relay: 20 ms round trip, but a one second penalty.
        let mut link = Link::new(16, Params::new(100 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let relay = PathInfo {
            kind: PathKind::Relay,
            ..PathInfo::default()
        };
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), relay)).unwrap();
        net.b.with_env(now, |c, env| c.add_path(env, PathId(4), relay)).unwrap();
        assert!(net.run(net.now + 10 * SEC, |n| n.a.saw(|r| *r == Rec::PathValidated(PathId(3)))));
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(1)),
            "a faster relay does not beat a direct path"
        );
        assert!(net.a.conn.path_rtt(PathId(3)).unwrap() < 30 * MS);
        // The direct path dies under a transfer: after three probe timeouts the relay takes over.
        net.link.route(PathId(1)).up = false;
        let data = pattern(2 << 20, 17);
        bulk(&mut net, &data, 300 * SEC);
        assert_eq!(net.a.conn.active_path(), Some(PathId(3)));
        assert!(net.a.saw(|r| *r == Rec::PathFailed(PathId(1))), "the endpoint is told");
        // The direct path comes back; a probe shows it is cheaper again.
        net.link.route(PathId(1)).up = true;
        let now = net.now;
        net.a.with_env(now, |c, env| c.probe(env, PathId(1))).unwrap();
        assert!(
            net.run(net.now + 60 * SEC, |n| n.a.conn.active_path() == Some(PathId(1))),
            "back to direct"
        );
    });
}

/// A session on a relay path that stops answering, with the relay's carrier heard at every step or never, and a
/// keepalive answer of the carrier received at every step or never: how long the session lives.
fn relay_path_goes_silent(carrier_answers: bool, pulses: bool) -> Option<u64> {
    let mut w = World::new(IdentityAlg::Ed25519);
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut link = Link::new(16, Params::new(100 * MS));
    link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
    let mut net = connected(&mut w, &mut sa, &mut sb, link);
    let relay = PathInfo {
        kind: PathKind::Relay,
        ..PathInfo::default()
    };
    let now = net.now;
    net.a.with_env(now, |c, env| c.add_path(env, PathId(3), relay)).unwrap();
    net.b.with_env(now, |c, env| c.add_path(env, PathId(4), relay)).unwrap();
    assert!(net.run(net.now + 10 * SEC, |n| n.a.saw(|r| *r == Rec::PathValidated(PathId(3)))));
    // The direct path dies under a transfer and the relay takes over.
    net.link.route(PathId(1)).up = false;
    bulk(&mut net, &pattern(2 << 20, 21), 300 * SEC);
    assert_eq!(net.a.conn.active_path(), Some(PathId(3)));
    // The relay path stops answering while data is in flight.
    net.link.route(PathId(3)).up = false;
    let id = net.a.conn.open_uni().unwrap();
    net.a.conn.write(id, &pattern(50_000, 22)).unwrap();
    let start = net.now;
    while net.now < start + 8 * SEC && net.a.closed().is_none() {
        if carrier_answers {
            net.a.conn.set_carrier_heard(Some(net.now));
        }
        if pulses {
            net.a.conn.pulse(net.now, false);
        }
        let until = (net.now + 10 * MS).min(start + 8 * SEC);
        net.run(until, |n| n.a.closed().is_some());
    }
    net.a.closed().map(|_| net.now - start)
}

#[test]
fn a_relay_session_whose_probes_time_out_behind_an_answering_carrier_is_closed() {
    big_stack(|| {
        let closed = relay_path_goes_silent(true, false);
        assert!(closed.is_some_and(|t| t < 8 * SEC), "{closed:?}");
        assert_eq!(
            relay_path_goes_silent(false, false),
            None,
            "without the carrier's word the session lives on"
        );
    });
}

#[test]
fn a_keepalive_answer_of_the_carrier_counts_as_hearing_the_peer() {
    big_stack(|| {
        assert_eq!(
            relay_path_goes_silent(true, true),
            None,
            "a peer heard through its carrier is not silent"
        );
    });
}

#[test]
fn a_session_with_a_long_round_trip_challenges_its_lost_direct_path_at_most_once_a_second() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // The direct path takes 600 ms round trip: this session is thin although the node is not configured so.
        let mut link = Link::new(16, Params::new(300 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let relay = PathInfo {
            kind: PathKind::Relay,
            ..PathInfo::default()
        };
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), relay)).unwrap();
        net.b.with_env(now, |c, env| c.add_path(env, PathId(4), relay)).unwrap();
        assert!(net.run(net.now + 10 * SEC, |n| n.a.saw(|r| *r == Rec::PathValidated(PathId(3)))));
        net.link.route(PathId(1)).up = false;
        let id = net.a.conn.open_uni().unwrap();
        net.a.conn.write(id, &pattern(100_000, 23)).unwrap();
        assert!(net.run(net.now + 120 * SEC, |n| n.a.conn.active_path() == Some(PathId(3))));
        let mark = net.a.tx_log.len();
        net.run(net.now + 15 * SEC, |_| false);
        let challenges: Vec<u64> = net.a.tx_log[mark..]
            .iter()
            .filter(|t| t.2 == PathId(1) && t.1 < 100)
            .map(|t| t.0)
            .collect();
        assert!(challenges.len() >= 2, "{challenges:?}");
        assert!(
            challenges[1] - challenges[0] >= 900 * MS,
            "the first two re-join challenges were {} ms apart",
            (challenges[1] - challenges[0]) / MS
        );
    });
}

#[test]
fn switching_needs_a_gain_above_5_ms_on_the_raw_round_trip() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // Active path: 20 ms round trip. A challenge is repeated every 33 ms, so candidates answer within that.
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(18, Params::new(10 * MS)));
        // Some traffic so the active path has a smoothed round trip; that is the number a candidate must beat.
        bulk(&mut net, &pattern(200_000, 19), 30 * SEC);
        net.run(net.now + SEC, |_| false);
        let cur = net.a.conn.path_rtt(PathId(1)).unwrap();
        assert!((19 * MS..23 * MS).contains(&cur), "{cur}");
        let add = |net: &mut Net<'_, '_>, id: u64, rtt: u64, v6: bool| -> u64 {
            let p = Params::new(rtt / 2);
            net.link.add_route(PathId(id), PathId(id + 1), p, p);
            let now = net.now;
            let info = PathInfo {
                v6,
                ..PathInfo::default()
            };
            net.a.with_env(now, |c, env| c.add_path(env, PathId(id), info)).unwrap();
            assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(id))));
            let measured = net.a.conn.path_rtt(PathId(id)).unwrap();
            net.run(net.now + SEC, |_| false);
            measured
        };
        let r = add(&mut net, 3, 18 * MS, false);
        assert!(r + 5 * MS >= cur, "a gain of {} ns is not enough", cur - r);
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        let r = add(&mut net, 5, 26 * MS, true); // slower, and 3 ms of bonus does not make it faster
        assert!(r > cur - 5 * MS);
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        net.a.conn.remove_path(PathId(3)).unwrap();
        assert!(
            net.a.conn.remove_path(PathId(1)).is_err(),
            "the active path cannot be removed"
        );
        let r = add(&mut net, 7, 12 * MS, true);
        assert!(r + 5 * MS < cur, "a raw gain of {} ns", cur - r);
        assert_eq!(net.a.conn.active_path(), Some(PathId(7)));
    });
}

#[test]
fn a_slow_path_probed_faster_than_its_round_trip_reads_the_true_round_trip() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(18, Params::new(10 * MS)));
        bulk(&mut net, &pattern(200_000, 19), 30 * SEC);
        net.run(net.now + SEC, |_| false);
        let cur = net.a.conn.path_rtt(PathId(1)).unwrap();
        assert!((19 * MS..23 * MS).contains(&cur), "{cur}");
        // A new path with a 40 ms round trip is probed every 33 ms, so a new challenge leaves before the answer to
        // the last one arrives. The round trip is that of the challenge the answer echoes, not of the latest send.
        let p = Params::new(20 * MS);
        net.link.add_route(PathId(3), PathId(4), p, p);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(3))));
        let measured = net.a.conn.path_rtt(PathId(3)).unwrap();
        assert!((39 * MS..45 * MS).contains(&measured), "{measured}");
        net.run(net.now + SEC, |_| false);
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(1)),
            "a slower path does not win the switch"
        );
    });
}

#[test]
fn a_black_hole_is_detected_and_the_mtu_falls_to_the_minimum() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(12, Params::new(10 * MS).mtu(1500)));
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1452));
        let big = net.a.conn.max_extension_size(0x41);
        // After the raise the link drops every datagram above 1200 bytes. Each probe timeout sends the small PING and
        // then the full-size retransmission of the held frame.
        let p = Params::new(10 * MS).mtu(1200);
        net.link.set(PathId(1), p, p);
        net.a.conn.send_extension(ext::TEST_FIRST, &vec![5u8; big]).unwrap();
        assert!(net.run(net.now + 60 * SEC, |n| n.a.conn.path_mtu(PathId(1)) == Some(1200)));
        assert!(
            net.a.saw(|r| *r == Rec::ExtensionUndeliverable(ext::TEST_FIRST, big)),
            "the held frame is reported"
        );
        assert!(
            net.a.conn.stats().ptos <= 3,
            "after {} probe timeouts",
            net.a.conn.stats().ptos
        );
        // The path works at the new size: a frame that fits is delivered.
        let max = net.a.conn.max_extension_size(0x41);
        assert!(max < big);
        net.a.conn.send_extension(ext::TEST_FIRST + 1, &vec![6u8; max]).unwrap();
        assert!(net.run(net.now + 30 * SEC, |n| {
            n.b.saw(|r| *r == Rec::Extension(ext::TEST_FIRST + 1, vec![6u8; max]))
        }));
    });
}

#[test]
fn a_black_hole_drops_at_the_first_probe_timeout_and_the_next_probe_waits_for_a_path_event() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(5, Params::new(10 * MS).mtu(1500)));
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1452));
        net.a.conn.set_keepalive(Some(5 * SEC));
        // Full-size packets vanish under a running transfer; small ones still pass.
        net.link.set(
            PathId(1),
            Params::new(10 * MS).mtu(1300),
            Params::new(10 * MS).mtu(1300),
        );
        let data = pattern(2 << 20, 7);
        let id = net.a.conn.open_bi().unwrap();
        let mut off = 0;
        let ok = net.run(net.now + 60 * SEC, |n| {
            while off < data.len() {
                let k = n.a.conn.write(id, &data[off..]).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            n.a.conn.path_mtu(PathId(1)) == Some(1200)
        });
        assert!(ok, "the path must fall back");
        assert!(
            net.a.conn.stats().ptos <= 2,
            "after {} probe timeouts",
            net.a.conn.stats().ptos
        );
        // The failing probe timeouts also took the path through a re-join, which is a path event: one probe goes out
        // and is lost. After that a lost probe waits: nothing above 1200 bytes leaves for ten minutes.
        let sent_big = |n: &Net<'_, '_>, from: usize| n.a.tx_log[from..].iter().filter(|t| t.1 > 1200).count();
        net.run(net.now + 20 * SEC, |_| false);
        let mark = net.a.tx_log.len();
        net.run(net.now + 500 * SEC, |_| false);
        assert_eq!(sent_big(&net, mark), 0);
        net.run(net.now + 120 * SEC, |_| false);
        assert_eq!(sent_big(&net, mark), 1, "after ten minutes the path is probed again");
        // A link return is a path event: the path is probed again, and a lost probe is not retried.
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        net.link.set(
            PathId(1),
            Params::new(10 * MS).mtu(1500),
            Params::new(10 * MS).mtu(1500),
        );
        let mark = net.a.tx_log.len();
        net.run(net.now + 30 * SEC, |_| false);
        assert_eq!(sent_big(&net, mark), 1, "re-probed after the event");
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1452));
    });
}

#[test]
fn an_end_challenged_on_a_new_direct_path_answers_with_its_own_challenge_in_the_same_datagram() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // The session runs on a relay path; a direct route exists that neither end has used.
        let mut link = Link::new(41, Params::new(40 * MS));
        let direct = 25 * MS;
        link.add_route(PathId(3), PathId(4), Params::new(direct), Params::new(direct));
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let relay = PathInfo {
            kind: PathKind::Relay,
            ..PathInfo::default()
        };
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(1), relay)).unwrap();
        net.b.with_env(now, |c, env| c.add_path(env, PathId(2), relay)).unwrap();
        net.run(net.now + SEC, |_| false);
        // A challenges the direct path. B learns the path from that challenge alone: nothing else names it to B.
        let t0 = net.now;
        let (a_sent, b_sent) = (net.a.tx_log.len(), net.b.tx_log.len());
        net.a
            .with_env(t0, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        assert!(
            net.run(t0 + SEC, |n| n.b.saw(|r| *r == Rec::PathValidated(PathId(4)))),
            "B never validated the direct path"
        );
        // A's challenge, B's answer with its own challenge, A's answer: three one-way trips.
        assert_eq!(net.now - t0, 3 * direct, "B's challenge did not leave with its answer");
        assert!(net.a.saw(|r| *r == Rec::PathValidated(PathId(3))));
        // B's first datagram on the path carries both frames, nine bytes more than a challenge alone, and with the
        // 28 bytes of its headers it stays within three times the one datagram that arrived from that address.
        let challenge = net.a.tx_log[a_sent..]
            .iter()
            .find(|(_, _, p)| *p == PathId(3))
            .unwrap()
            .1;
        let both = net.b.tx_log[b_sent..]
            .iter()
            .find(|(_, _, p)| *p == PathId(4))
            .unwrap()
            .1;
        assert_eq!(both, challenge + 9);
        assert!(both + 28 <= 3 * challenge, "{both} bytes answer {challenge}");
        // Both ends leave the relay for the direct path.
        net.run(net.now + SEC, |_| false);
        assert_eq!(
            (net.a.conn.active_path(), net.b.conn.active_path()),
            (Some(PathId(3)), Some(PathId(4)))
        );
    });
}
