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
fn path_validation_failure_is_reported() {
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
        assert!(net.run(net.now + 30 * SEC, |n| n.a.saw(|r| *r == Rec::PathFailed(PathId(3)))));
        assert!(!net.a.conn.path_validated(PathId(3)));
        assert!(net.a.conn.set_active(PathId(3)).is_err());
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        let data = pattern(1 << 20, 15);
        bulk(&mut net, &data, 60 * SEC);
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

#[test]
fn switching_needs_a_gain_above_5_ms_and_ipv6_gets_a_bonus() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // Active path: 40 ms round trip.
        let mut link = Link::new(18, Params::new(20 * MS));
        for (a, rtt_ms) in [(3u64, 38u64), (5, 46), (7, 36)] {
            let p = Params::new(rtt_ms * MS / 2);
            link.add_route(PathId(a), PathId(a + 1), p, p);
        }
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        // Some traffic so the active path has a round-trip sample.
        bulk(&mut net, &pattern(200_000, 19), 30 * SEC);
        net.run(net.now + SEC, |_| false);
        // A clean round-trip measurement of the active path, from a challenge.
        net.a.with_env(net.now, |c, env| c.probe(env, PathId(1))).unwrap();
        net.run(net.now + SEC, |_| false);
        let add = |net: &mut Net<'_, '_>, id: u64, v6: bool| {
            let now = net.now;
            let info = PathInfo {
                v6,
                ..PathInfo::default()
            };
            net.a.with_env(now, |c, env| c.add_path(env, PathId(id), info)).unwrap();
            net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(id)));
            net.run(net.now + SEC, |_| false);
        };
        add(&mut net, 3, false); // 38 ms: a 2 ms gain is not enough
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        add(&mut net, 5, true); // 46 ms, minus the 3 ms bonus: still worse
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        net.a.conn.remove_path(PathId(3)).unwrap();
        assert!(
            net.a.conn.remove_path(PathId(1)).is_err(),
            "the active path cannot be removed"
        );
        add(&mut net, 7, true);
        // 36 ms, 33 with the bonus: a gain of 7 ms
        assert_eq!(net.a.conn.active_path(), Some(PathId(7)));
    });
}
