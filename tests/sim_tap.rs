//! The inbound adversary of `pinc-sim`: capture of large first flights, replay and bit flips at victims, and direct
//! injection at a node.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_sim::toy::{Probe, ProbeCmd, ProbeEvent};
use pinc_sim::{DropReason, LinkConfig, MS, NodeId, SEC, Sim, SimConfig, TapSpec};

const fn sa(d: u8) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, d)), 1)
}

fn world(spec: impl FnOnce(NodeId, NodeId) -> TapSpec) -> (Sim<Probe>, NodeId, NodeId) {
    let cfg = SimConfig {
        default_link: Some(LinkConfig {
            delay: MS,
            ..LinkConfig::default()
        }),
        ..SimConfig::default()
    };
    let mut sim = Sim::with_config(11, cfg);
    let a = sim.add_node_at(Probe::new(), sa(1).ip());
    let b = sim.add_node_at(Probe::new(), sa(2).ip());
    sim.tap_inbound(spec(a, b));
    (sim, a, b)
}

fn spec(victims: Vec<NodeId>, replay: f64, modify: f64) -> TapSpec {
    TapSpec {
        victims,
        replay,
        modify,
        capture_min: usize::MAX,
        capture_prob: 1.0,
        capture_max: 0,
        first_flights_only: false,
    }
}

fn send(sim: &mut Sim<Probe>, from: NodeId, from_a: u8, to_a: u8, data: Vec<u8>, at: u64) {
    sim.command(
        at,
        from,
        ProbeCmd::Send {
            local: sa(from_a),
            remote: sa(to_a),
            data,
        },
    );
}

fn received(sim: &Sim<Probe>, n: NodeId) -> Vec<(u64, Vec<u8>)> {
    sim.events(n)
        .iter()
        .filter_map(|(t, e)| match e {
            ProbeEvent::Recv { data, .. } => Some((*t, data.clone())),
            ProbeEvent::Timer(_) => None,
        })
        .collect()
}

#[test]
fn a_replayed_datagram_arrives_again_later_and_only_at_a_victim() {
    let (mut sim, a, b) = world(|_, b| spec(vec![b], 1.0, 0.0));
    for i in 0..5u8 {
        send(&mut sim, a, 1, 2, vec![i; 16], SEC + u64::from(i) * 10 * MS);
        send(&mut sim, b, 2, 1, vec![i; 16], SEC + u64::from(i) * 10 * MS);
    }
    sim.run_until(10 * SEC);
    assert_eq!(received(&sim, b).len(), 10, "each datagram at the victim comes twice");
    assert_eq!(received(&sim, a).len(), 5, "the other node is left alone");
    assert_eq!(sim.tap_stats().replayed, 5);
    let at_b = received(&sim, b);
    for i in 0..5u8 {
        let times: Vec<u64> = at_b.iter().filter(|(_, d)| d[0] == i).map(|(t, _)| *t).collect();
        assert_eq!(times.len(), 2);
        assert!(
            times[1] >= times[0] + MS && times[1] <= times[0] + MS + 2 * SEC,
            "{times:?}"
        );
    }
}

#[test]
fn a_modified_datagram_differs_by_exactly_one_bit() {
    let (mut sim, a, b) = world(|_, b| spec(vec![b], 0.0, 1.0));
    for i in 0..20u8 {
        send(&mut sim, a, 1, 2, vec![i; 32], SEC + u64::from(i) * MS);
    }
    sim.run_until(5 * SEC);
    let got = received(&sim, b);
    assert_eq!(got.len(), 20);
    assert_eq!(sim.tap_stats().modified, 20);
    for (i, (_, d)) in got.iter().enumerate() {
        let flips: u32 = d.iter().map(|x| (x ^ i as u8).count_ones()).sum();
        assert_eq!(flips, 1, "datagram {i}");
    }
}

#[test]
fn capture_keeps_large_first_flights_up_to_its_limit() {
    let (mut sim, a, b) = world(|_, _| TapSpec {
        capture_min: 100,
        capture_max: 3,
        first_flights_only: true,
        ..spec(Vec::new(), 0.0, 0.0)
    });
    let mut long = vec![0x80u8; 200];
    long[1] = 7;
    let short_header = vec![0x40u8; 200];
    let small = vec![0x80u8; 50];
    for i in 0..6u64 {
        send(&mut sim, a, 1, 2, long.clone(), SEC + i * MS);
    }
    send(&mut sim, a, 1, 2, short_header, 2 * SEC);
    send(&mut sim, a, 1, 2, small, 2 * SEC);
    sim.run_until(5 * SEC);
    let kept = sim.tap_captured();
    assert_eq!(kept.len(), 3, "limit");
    assert!(
        kept.iter()
            .all(|c| c.node == b && c.data == long && c.src == sa(1) && c.dst == sa(2))
    );
    assert_eq!(received(&sim, b).len(), 8, "capture does not stop delivery");
    assert_eq!(sim.tap_stats(), pinc_sim::TapStats::default());
}

#[test]
fn injection_reaches_a_running_node_directly_and_is_dropped_otherwise() {
    let (mut sim, _, b) = world(|_, _| spec(Vec::new(), 0.0, 0.0));
    sim.inject_at(SEC, b, sa(99), sa(2), vec![1, 2, 3]);
    sim.inject_at(2 * SEC, b, sa(99), sa(77), vec![4]);
    sim.crash(3 * SEC, b);
    sim.inject_at(4 * SEC, b, sa(99), sa(2), vec![5]);
    sim.run_until(5 * SEC);
    let got = received(&sim, b);
    assert_eq!(got, vec![(SEC, vec![1, 2, 3])]);
    assert_eq!(sim.metrics().dropped(DropReason::NoIface), 1);
    assert_eq!(sim.metrics().dropped(DropReason::NodeDown), 1);
}

#[test]
fn the_adversary_replays_the_same_run() {
    let run = || {
        let (mut sim, a, b) = world(|_, b| spec(vec![b], 0.3, 0.3));
        for i in 0..50u8 {
            send(&mut sim, a, 1, 2, vec![i; 24], SEC + u64::from(i) * MS);
        }
        sim.run_until(10 * SEC);
        (received(&sim, b), sim.tap_stats())
    };
    assert_eq!(run(), run());
}
