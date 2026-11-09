//! The `vinc-sim` engine: determinism, event order, timers, the toy node over lossy links, CPU metering, wall clocks
//! and the trace.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::assert_is_empty,
    clippy::manual_assert_eq
)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_sim::toy::{Probe, ProbeCmd, ProbeEvent, Toy, ToyCmd, ToyConfig, ToyEvent};
use vinc_sim::{Cpu, LinkConfig, Loss, MS, NodeId, SEC, Sim, SimConfig, WALL_EPOCH};

fn ip(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(a, b, c, d))
}

fn sa(a: u8, b: u8, c: u8, d: u8, port: u16) -> SocketAddr {
    SocketAddr::new(ip(a, b, c, d), port)
}

fn lossy() -> LinkConfig {
    LinkConfig {
        delay: 10 * MS,
        jitter: 4 * MS,
        loss: Loss::Bernoulli(0.1),
        dup_prob: 0.02,
        reorder_prob: 0.05,
        reorder_depth: 3,
        ..LinkConfig::default()
    }
}

/// A toy client and server over a lossy link; returns the simulator and the client.
fn toy_pair(seed: u64, total: u32, trace: bool) -> (Sim<Toy>, NodeId, NodeId) {
    let cfg = SimConfig {
        trace,
        trace_packets: trace,
        default_link: Some(lossy()),
        ..SimConfig::default()
    };
    let mut sim = Sim::with_config(seed, cfg);
    let (c, s) = (sa(10, 0, 0, 1, 5000), sa(10, 0, 0, 2, 443));
    let base = ToyConfig {
        local: c,
        peer: Some(s),
        total,
        window: 8,
        msg_len: 200,
        rto: 80 * MS,
    };
    let client = sim.add_node_at(Toy::new(base), c.ip());
    let server = sim.add_node_at(
        Toy::new(ToyConfig {
            local: s,
            peer: None,
            ..base
        }),
        s.ip(),
    );
    sim.command(0, client, ToyCmd::Start);
    (sim, client, server)
}

#[test]
fn same_seed_gives_identical_trace() {
    let run = |seed| {
        let (mut sim, ..) = toy_pair(seed, 100, true);
        sim.run_until(20 * SEC);
        sim.take_trace()
    };
    let a = run(7);
    assert!(a.lines().count() > 500, "the trace must be substantial");
    assert_eq!(a, run(7));
}

#[test]
fn different_seed_gives_different_trace() {
    let run = |seed| {
        let (mut sim, ..) = toy_pair(seed, 100, true);
        sim.run_until(20 * SEC);
        sim.take_trace()
    };
    assert_ne!(run(7), run(8));
}

#[test]
fn trace_is_ndjson() {
    let (mut sim, ..) = toy_pair(3, 20, true);
    sim.run_until(5 * SEC);
    let t = sim.take_trace();
    assert!(sim.trace().is_empty());
    for line in t.lines() {
        assert!(line.starts_with("{\"t\":") && line.ends_with('}'), "{line}");
        assert_eq!(line.matches('{').count(), 1, "{line}");
    }
    assert!(t.contains("\"k\":\"ev\"") && t.contains("Echoed(") && t.contains("\"k\":\"drop\""));
}

#[test]
fn toy_completes_over_lossy_links() {
    for seed in 0..10 {
        let (mut sim, client, server) = toy_pair(seed, 300, false);
        assert!(
            sim.run_until_pred(60 * SEC, |s| s.node(client).is_complete()),
            "seed {seed}"
        );
        let ev = sim.events(client);
        let echoed: Vec<u32> = ev
            .iter()
            .filter_map(|(_, e)| if let ToyEvent::Echoed(s) = e { Some(*s) } else { None })
            .collect();
        let mut sorted = echoed.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(
            sorted,
            (0..300).collect::<Vec<_>>(),
            "every message echoed exactly once"
        );
        assert_eq!(echoed.len(), 300);
        assert_eq!(ev.iter().filter(|(_, e)| *e == ToyEvent::Complete).count(), 1);
        assert!(
            ev.iter().any(|(_, e)| matches!(e, ToyEvent::Retransmit(_))),
            "10% loss must force retransmits"
        );
        assert_eq!(
            sim.events(server)
                .iter()
                .filter(|(_, e)| matches!(e, ToyEvent::Served(_)))
                .count(),
            300
        );
    }
}

#[test]
fn events_at_one_instant_run_in_scheduling_order() {
    let mut sim: Sim<Probe> = Sim::new(1);
    let n = sim.add_node_at(Probe::new(), ip(1, 1, 1, 1));
    sim.command(5, n, ProbeCmd::Timer(100));
    sim.command(5, n, ProbeCmd::Timer(50));
    sim.command(7, n, ProbeCmd::Timer(60));
    sim.run_until(1000);
    // The second command at time 5 replaced the first timer; the one at 7 replaced that.
    assert_eq!(sim.events(n), &[(60, ProbeEvent::Timer(60))]);
    assert_eq!(sim.now(), 1000);
}

#[test]
fn timers_fire_at_the_requested_time_and_stop_when_replaced() {
    let mut sim: Sim<Probe> = Sim::new(1);
    let n = sim.add_node_at(Probe::new(), ip(1, 1, 1, 1));
    sim.command(0, n, ProbeCmd::Timer(10 * MS));
    sim.command(MS, n, ProbeCmd::Timer(30 * MS));
    sim.run_until(SEC);
    assert_eq!(sim.events(n), &[(30 * MS, ProbeEvent::Timer(30 * MS))]);
}

#[test]
fn run_until_pred_stops_at_the_predicate_and_at_the_limit() {
    let (mut sim, client, _) = toy_pair(2, 50, false);
    assert!(sim.run_until_pred(60 * SEC, |s| s.node(client).done_count() >= 10));
    assert!(sim.node(client).done_count() >= 10 && !sim.node(client).is_complete());
    let t = sim.now();
    assert!(!sim.run_until_pred(t + 1, |_| false));
    assert_eq!(sim.now(), t + 1);
    assert!(sim.run_idle(120 * SEC));
}

#[test]
fn unroutable_datagrams_are_counted() {
    let mut sim: Sim<Probe> = Sim::new(1);
    let a = sim.add_node_at(Probe::new(), ip(1, 1, 1, 1));
    let send = |to| ProbeCmd::Send {
        local: sa(1, 1, 1, 1, 1),
        remote: to,
        data: vec![0; 10],
    };
    sim.command(0, a, send(sa(9, 9, 9, 9, 1)));
    sim.command(
        0,
        a,
        ProbeCmd::Send {
            local: sa(2, 2, 2, 2, 1),
            remote: sa(9, 9, 9, 9, 1),
            data: vec![],
        },
    );
    sim.run_until(MS);
    assert_eq!(sim.metrics().dropped(vinc_sim::DropReason::NoRoute), 1);
    assert_eq!(sim.metrics().dropped(vinc_sim::DropReason::NoIface), 1);
    assert_eq!(sim.metrics().total_dropped(), 2);
}

#[test]
fn cpu_metering_serialises_calls_and_scales_with_the_factor() {
    let spacing = |factor_milli| {
        let cfg = SimConfig {
            default_link: Some(LinkConfig::default()),
            ..SimConfig::default()
        };
        let mut sim: Sim<Probe> = Sim::with_config(1, cfg);
        let a = sim.add_node_at(Probe::new(), ip(1, 1, 1, 1));
        let b = sim.add_node_at(Probe::new(), ip(1, 1, 1, 2));
        sim.set_cpu(
            b,
            Cpu {
                factor_milli,
                per_call: MS,
                per_kib: 0,
            },
        );
        for _ in 0..4 {
            sim.command(
                0,
                a,
                ProbeCmd::Send {
                    local: sa(1, 1, 1, 1, 1),
                    remote: sa(1, 1, 1, 2, 1),
                    data: vec![1; 100],
                },
            );
        }
        sim.run_until(SEC);
        sim.node(b).call_times.clone()
    };
    assert_eq!(spacing(1000), vec![0, MS, 2 * MS, 3 * MS]);
    assert_eq!(spacing(4000), vec![0, 4 * MS, 8 * MS, 12 * MS]);
}

#[test]
fn cpu_cost_grows_with_bytes() {
    let cpu = Cpu {
        factor_milli: 1000,
        per_call: 0,
        per_kib: 1_000_000,
    };
    let cfg = SimConfig {
        default_link: Some(LinkConfig::default()),
        ..SimConfig::default()
    };
    let mut sim: Sim<Probe> = Sim::with_config(1, cfg);
    let a = sim.add_node_at(Probe::new(), ip(1, 1, 1, 1));
    let b = sim.add_node_at(Probe::new(), ip(1, 1, 1, 2));
    sim.set_cpu(b, cpu);
    for _ in 0..2 {
        sim.command(
            0,
            a,
            ProbeCmd::Send {
                local: sa(1, 1, 1, 1, 1),
                remote: sa(1, 1, 1, 2, 1),
                data: vec![0; 2048],
            },
        );
    }
    sim.run_until(SEC);
    assert_eq!(sim.node(b).call_times, vec![0, 2 * MS]);
}

#[test]
fn wall_clock_skew_drift_and_jumps_do_not_touch_timers() {
    let mut sim: Sim<Probe> = Sim::new(1);
    let n = sim.add_node_at(Probe::new(), ip(1, 1, 1, 1));
    let other = sim.add_node_at(Probe::new(), ip(1, 1, 1, 2));
    sim.clock_jump(0, n, -5 * SEC as i64);
    sim.clock_drift(0, n, 100);
    sim.command(0, n, ProbeCmd::Timer(10 * SEC));
    sim.run_until(10 * SEC);
    assert_eq!(sim.wall_time(other), WALL_EPOCH + 10 * SEC);
    assert_eq!(sim.wall_time(n), WALL_EPOCH - 5 * SEC + 10 * SEC + 1_000_000);
    // Monotonic timers fired exactly on time.
    assert_eq!(sim.events(n), &[(10 * SEC, ProbeEvent::Timer(10 * SEC))]);
    sim.clock_jump(10 * SEC, n, 7 * SEC as i64);
    sim.run_until(11 * SEC);
    assert_eq!(sim.wall_time(n), WALL_EPOCH - 5 * SEC + 11 * SEC + 7 * SEC + 1_100_000);
}
