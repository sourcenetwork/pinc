//! The `pinc-sim` NATs: mapping and filtering for each kind, mapping timeouts, rebinding, address families.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::assert_is_empty,
    clippy::manual_assert_eq
)]

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use pinc_sim::toy::{Probe, ProbeCmd, ProbeEvent};
use pinc_sim::{DropReason, LinkConfig, MS, NatConfig, NatId, NatKind, NodeId, PortPolicy, SEC, Sim, SimConfig};

const EXT: IpAddr = IpAddr::V4(Ipv4Addr::new(203, 0, 113, 1));
const PRIV: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 0, 2)), 4000);
const S1: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 1, 1, 1)), 443);
const S2: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 1, 1, 2)), 443);

struct World {
    sim: Sim<Probe>,
    nat: NatId,
    a: NodeId,
    s1: NodeId,
    s2: NodeId,
}

fn world(kind: NatKind, timeout: u64, refresh_on_inbound: bool) -> World {
    let link = LinkConfig {
        delay: 5 * MS,
        ..LinkConfig::default()
    };
    let mut sim = Sim::with_config(
        1,
        SimConfig {
            default_link: Some(link),
            ..SimConfig::default()
        },
    );
    let nat = sim.add_nat(NatConfig {
        kind,
        ext_ip: EXT,
        mapping_timeout: timeout,
        tcp_timeout: 7200 * SEC,
        refresh_on_inbound,
        port_base: 20_000,
        ports: PortPolicy::Sequential,
        no_punch: false,
    });
    let a = sim.add_node(Probe::new());
    sim.add_iface_behind(a, PRIV.ip(), nat);
    let s1 = sim.add_node_at(Probe::new(), S1.ip());
    let s2 = sim.add_node_at(Probe::new(), S2.ip());
    World { sim, nat, a, s1, s2 }
}

impl World {
    fn send(&mut self, at: u64, from: NodeId, local: SocketAddr, remote: SocketAddr, tag: u8) {
        self.sim.command(
            at,
            from,
            ProbeCmd::Send {
                local,
                remote,
                data: vec![tag],
            },
        );
    }

    /// The (source address, tag) of every datagram a node received.
    fn got(&self, n: NodeId) -> Vec<(SocketAddr, u8)> {
        self.sim
            .events(n)
            .iter()
            .filter_map(|(_, e)| {
                if let ProbeEvent::Recv { remote, data, .. } = e {
                    Some((*remote, data[0]))
                } else {
                    None
                }
            })
            .collect()
    }

    /// The external address S1 saw for the datagram tagged `tag`.
    fn ext_seen_by(&self, n: NodeId, tag: u8) -> SocketAddr {
        self.got(n).into_iter().find(|(_, t)| *t == tag).unwrap().0
    }
}

/// Which of three outsiders get through after A sent to S1: S2 (never contacted), S1 from another port, S1 itself.
fn filter_matrix(kind: NatKind) -> [bool; 3] {
    let mut w = world(kind, 60 * SEC, false);
    w.send(0, w.a, PRIV, S1, 1);
    w.sim.run_until(SEC);
    let ext = w.ext_seen_by(w.s1, 1);
    assert_eq!(ext.ip(), EXT);
    assert_eq!(ext.port(), 20_000);
    w.send(SEC, w.s2, S2, ext, 2);
    w.send(SEC, w.s1, SocketAddr::new(S1.ip(), 9999), ext, 3);
    w.send(SEC, w.s1, S1, ext, 4);
    w.sim.run_until(2 * SEC);
    let tags: Vec<u8> = w.got(w.a).iter().map(|g| g.1).collect();
    // The private host sees the datagram addressed to its private socket.
    for e in w.sim.events(w.a) {
        if let ProbeEvent::Recv { local, .. } = &e.1 {
            assert_eq!(*local, PRIV);
        }
    }
    [tags.contains(&2), tags.contains(&3), tags.contains(&4)]
}

#[test]
fn full_cone_accepts_anyone() {
    assert_eq!(filter_matrix(NatKind::FullCone), [true, true, true]);
}

#[test]
fn address_restricted_accepts_contacted_addresses_on_any_port() {
    assert_eq!(filter_matrix(NatKind::AddressRestricted), [false, true, true]);
}

#[test]
fn port_restricted_accepts_only_the_contacted_address_and_port() {
    assert_eq!(filter_matrix(NatKind::PortRestricted), [false, false, true]);
}

#[test]
fn symmetric_accepts_only_the_contacted_destination() {
    assert_eq!(filter_matrix(NatKind::Symmetric), [false, false, true]);
}

#[test]
fn refused_datagrams_are_counted_as_nat_drops() {
    let mut w = world(NatKind::PortRestricted, 60 * SEC, false);
    w.send(0, w.a, PRIV, S1, 1);
    w.sim.run_until(SEC);
    let ext = w.ext_seen_by(w.s1, 1);
    w.send(SEC, w.s2, S2, ext, 2);
    w.send(SEC, w.s2, S2, SocketAddr::new(EXT, 1), 3);
    w.sim.run_until(2 * SEC);
    assert_eq!(w.sim.metrics().dropped(DropReason::NatFilter), 2);
}

#[test]
fn cone_nats_reuse_one_port_and_symmetric_uses_one_per_destination() {
    for kind in [
        NatKind::FullCone,
        NatKind::AddressRestricted,
        NatKind::PortRestricted,
        NatKind::Symmetric,
    ] {
        let mut w = world(kind, 60 * SEC, false);
        w.send(0, w.a, PRIV, S1, 1);
        w.send(MS, w.a, PRIV, S2, 2);
        w.send(2 * MS, w.a, PRIV, S1, 3);
        w.sim.run_until(SEC);
        let (p1, p2) = (w.ext_seen_by(w.s1, 1), w.ext_seen_by(w.s2, 2));
        let p1_again = w.ext_seen_by(w.s1, 3);
        assert_eq!(p1, p1_again, "{kind:?}: same destination keeps its mapping");
        assert_eq!(p1 == p2, kind != NatKind::Symmetric, "{kind:?}: {p1} {p2}");
        assert_eq!(
            w.sim.nat_mappings(w.nat),
            if kind == NatKind::Symmetric { 2 } else { 1 }
        );
    }
}

#[test]
fn two_private_hosts_get_distinct_ports() {
    let mut w = world(NatKind::FullCone, 60 * SEC, false);
    let b = w.sim.add_node(Probe::new());
    let b_addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 0, 3)), 4000);
    w.sim.add_iface_behind(b, b_addr.ip(), w.nat);
    w.send(0, w.a, PRIV, S1, 1);
    w.send(0, b, b_addr, S1, 2);
    w.sim.run_until(SEC);
    let (pa, pb) = (w.ext_seen_by(w.s1, 1), w.ext_seen_by(w.s1, 2));
    assert_ne!(pa.port(), pb.port());
    w.send(SEC, w.s1, S1, pb, 3);
    w.sim.run_until(2 * SEC);
    assert_eq!(w.got(b), vec![(S1, 3)]);
    assert!(w.got(w.a).is_empty());
}

#[test]
fn mapping_times_out_and_rebinds_to_a_new_port() {
    let mut w = world(NatKind::FullCone, 30 * SEC, false);
    w.send(0, w.a, PRIV, S1, 1);
    // A keepalive inside the timeout keeps the mapping and the port.
    w.send(20 * SEC, w.a, PRIV, S1, 2);
    w.sim.run_until(21 * SEC);
    let ext = w.ext_seen_by(w.s1, 1);
    assert_eq!(ext, w.ext_seen_by(w.s1, 2));
    // Idle for longer than the timeout: the mapping is gone.
    w.send(60 * SEC, w.s1, S1, ext, 3);
    w.sim.run_until(61 * SEC);
    assert!(w.got(w.a).is_empty());
    assert_eq!(w.sim.metrics().dropped(DropReason::NatFilter), 1);
    // The next outbound datagram creates a fresh mapping on a different port.
    w.send(62 * SEC, w.a, PRIV, S1, 4);
    w.sim.run_until(63 * SEC);
    let ext2 = w.ext_seen_by(w.s1, 4);
    assert_ne!(ext, ext2);
    // The old port stays dead; the new one works.
    w.send(64 * SEC, w.s1, S1, ext, 5);
    w.send(64 * SEC, w.s1, S1, ext2, 6);
    w.sim.run_until(65 * SEC);
    assert_eq!(w.got(w.a), vec![(S1, 6)]);
}

#[test]
fn inbound_traffic_refreshes_a_mapping_only_when_configured() {
    for (refresh, expect) in [(false, false), (true, true)] {
        let mut w = world(NatKind::FullCone, 30 * SEC, refresh);
        w.send(0, w.a, PRIV, S1, 1);
        w.sim.run_until(SEC);
        let ext = w.ext_seen_by(w.s1, 1);
        w.send(20 * SEC, w.s1, S1, ext, 2);
        w.send(40 * SEC, w.s1, S1, ext, 3);
        w.sim.run_until(41 * SEC);
        let tags: Vec<u8> = w.got(w.a).iter().map(|g| g.1).collect();
        assert!(tags.contains(&2));
        assert_eq!(tags.contains(&3), expect, "refresh {refresh}");
    }
}

#[test]
fn rebind_clears_mappings_and_can_move_the_public_address() {
    let mut w = world(NatKind::FullCone, 600 * SEC, false);
    w.send(0, w.a, PRIV, S1, 1);
    w.sim.run_until(SEC);
    let ext = w.ext_seen_by(w.s1, 1);
    w.sim.nat_rebind(2 * SEC, w.nat, None);
    w.send(3 * SEC, w.s1, S1, ext, 2);
    w.send(4 * SEC, w.a, PRIV, S1, 3);
    w.sim.run_until(5 * SEC);
    assert!(w.got(w.a).is_empty(), "the old mapping died with the rebind");
    let ext2 = w.ext_seen_by(w.s1, 3);
    assert_eq!(ext2.ip(), EXT);
    assert_ne!(ext2.port(), ext.port());

    let new_ip = IpAddr::V4(Ipv4Addr::new(203, 0, 113, 77));
    w.sim.nat_rebind(6 * SEC, w.nat, Some(new_ip));
    w.send(7 * SEC, w.a, PRIV, S1, 4);
    w.sim.run_until(8 * SEC);
    assert_eq!(w.ext_seen_by(w.s1, 4).ip(), new_ip);
    assert_eq!(w.sim.nat_ext_ip(w.nat), new_ip);
    // Datagrams to the old public address have nowhere to go.
    w.send(9 * SEC, w.s1, S1, ext2, 5);
    w.sim.run_until(10 * SEC);
    assert_eq!(w.sim.metrics().dropped(DropReason::NoRoute), 1);
}

#[test]
fn a_changed_private_address_follows_the_nat() {
    let mut w = world(NatKind::PortRestricted, 600 * SEC, false);
    let new_priv = IpAddr::V4(Ipv4Addr::new(192, 168, 0, 9));
    w.sim.set_iface_addr(SEC, w.a, 0, new_priv);
    w.send(2 * SEC, w.a, SocketAddr::new(new_priv, 4000), S1, 1);
    w.sim.run_until(3 * SEC);
    let ext = w.ext_seen_by(w.s1, 1);
    w.send(3 * SEC, w.s1, S1, ext, 2);
    w.sim.run_until(4 * SEC);
    assert_eq!(w.got(w.a), vec![(S1, 2)]);
    assert_eq!(w.sim.events(w.a)[0].0, 3 * SEC + 5 * MS);
}

#[test]
fn nat_works_over_ipv6() {
    let ext = IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1));
    let link = LinkConfig {
        delay: MS,
        ..LinkConfig::default()
    };
    let mut sim: Sim<Probe> = Sim::with_config(
        1,
        SimConfig {
            default_link: Some(link),
            ..SimConfig::default()
        },
    );
    let nat = sim.add_nat(NatConfig {
        kind: NatKind::PortRestricted,
        ext_ip: ext,
        mapping_timeout: 60 * SEC,
        tcp_timeout: 7200 * SEC,
        refresh_on_inbound: false,
        port_base: 1024,
        ports: PortPolicy::Sequential,
        no_punch: false,
    });
    let (a, s) = (sim.add_node(Probe::new()), sim.add_node(Probe::new()));
    let a_addr = SocketAddr::new(IpAddr::V6(Ipv6Addr::new(0xfd00, 0, 0, 0, 0, 0, 0, 2)), 7);
    let s_addr = SocketAddr::new(IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 1, 0, 0, 0, 0, 2)), 443);
    sim.add_iface_behind(a, a_addr.ip(), nat);
    sim.add_iface(s, s_addr.ip());
    sim.command(
        0,
        a,
        ProbeCmd::Send {
            local: a_addr,
            remote: s_addr,
            data: vec![1],
        },
    );
    sim.run_until(SEC);
    let ProbeEvent::Recv { remote, .. } = &sim.events(s)[0].1 else {
        panic!()
    };
    assert_eq!(*remote, SocketAddr::new(ext, 1024));
    sim.command(
        SEC,
        s,
        ProbeCmd::Send {
            local: s_addr,
            remote: *remote,
            data: vec![2],
        },
    );
    sim.run_until(2 * SEC);
    assert_eq!(sim.events(a).len(), 1);
}

#[test]
fn short_udp_idle_timeouts_break_idle_flows() {
    // A firewall with a 5 s UDP timeout in front of a client: a flow idle for 8 s loses its inbound path.
    let mut w = world(NatKind::PortRestricted, 5 * SEC, false);
    w.send(0, w.a, PRIV, S1, 1);
    w.sim.run_until(SEC);
    let ext = w.ext_seen_by(w.s1, 1);
    w.send(2 * SEC, w.s1, S1, ext, 2);
    w.send(9 * SEC, w.s1, S1, ext, 3);
    w.sim.run_until(10 * SEC);
    let tags: Vec<u8> = w.got(w.a).iter().map(|g| g.1).collect();
    assert_eq!(tags, vec![2]);
}
