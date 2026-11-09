//! The reference profile of `vinc-sim`: time-based burst loss, LAN uplinks and downlinks with region delays, wire
//! accounting before drops, driver modes, pluggable cost models and random sources, NAT details, middleboxes,
//! LAN partitions, the IPv6 firewall and the local clock.
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

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use vinc_sim::toy::{Probe, ProbeCmd, ProbeEvent};
use vinc_sim::{
    Call, Clock, CostModel, Cpu, Driver, DropReason, FlatCost, LanConfig, LanDir, LanId, LinkChange, LinkConfig, Loss,
    MS, NatConfig, NatKind, NodeId, PortPolicy, Random, Rng, SEC, Sim, SimConfig, Stream, Time, Work,
};

const fn ip(d: u8) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(10, 0, 0, d))
}

const fn sa(d: u8) -> SocketAddr {
    SocketAddr::new(ip(d), 1)
}

fn cfg(delay: Time) -> SimConfig {
    SimConfig {
        default_link: Some(LinkConfig {
            delay,
            ..LinkConfig::default()
        }),
        latency_samples: true,
        ..SimConfig::default()
    }
}

fn send(sim: &mut Sim<Probe>, at: Time, from: NodeId, a: u8, b: u8, tag: u8) {
    sim.command(
        at,
        from,
        ProbeCmd::Send {
            local: sa(a),
            remote: sa(b),
            data: vec![tag],
        },
    );
}

fn tags(sim: &Sim<Probe>, n: NodeId) -> Vec<u8> {
    sim.events(n)
        .iter()
        .filter_map(|(_, e)| {
            if let ProbeEvent::Recv { data, .. } = e {
                Some(data[0])
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn timed_burst_loss_has_its_rate_and_long_bursts() {
    let link = LinkConfig::reference(0, 0, 1 << 20, 0.05, 10 * MS);
    let run = |seed| {
        let mut sim: Sim<Probe> = Sim::with_config(
            seed,
            SimConfig {
                default_link: Some(link.clone()),
                ..SimConfig::default()
            },
        );
        let a = sim.add_node_at(Probe::new(), ip(1));
        let b = sim.add_node_at(Probe::new(), ip(2));
        for i in 0..100_000u32 {
            let mut data = vec![0; 8];
            data[..4].copy_from_slice(&i.to_le_bytes());
            sim.command(
                u64::from(i) * MS,
                a,
                ProbeCmd::Send {
                    local: sa(1),
                    remote: sa(2),
                    data,
                },
            );
        }
        sim.run_until(101 * SEC);
        let mut seen = vec![false; 100_000];
        for (_, e) in sim.events(b) {
            if let ProbeEvent::Recv { data, .. } = e {
                seen[u32::from_le_bytes(data[..4].try_into().unwrap()) as usize] = true;
            }
        }
        seen
    };
    let seen = run(5);
    let lost = seen.iter().filter(|s| !**s).count();
    let rate = lost as f64 / 100_000.0;
    assert!((0.03..0.07).contains(&rate), "rate {rate}");
    let (mut run_len, mut longest) = (0, 0);
    for s in &seen {
        run_len = if *s { 0 } else { run_len + 1 };
        longest = longest.max(run_len);
    }
    assert!(
        longest >= 15,
        "a mean burst of 10 ms at one datagram per ms must give long runs, longest {longest}"
    );
    assert_eq!(seen, run(5));
    assert_ne!(seen, run(6));
}

#[test]
fn a_lost_datagram_still_uses_line_time_and_the_queue_counts_the_backlog_ahead() {
    let link = LinkConfig {
        bandwidth_bps: 8_000_000,
        queue_bytes: 5000,
        loss: Loss::Bernoulli(1.0),
        ..LinkConfig::default()
    };
    let mut sim: Sim<Probe> = Sim::with_config(
        1,
        SimConfig {
            default_link: Some(link),
            ..SimConfig::default()
        },
    );
    let a = sim.add_node_at(Probe::new(), ip(1));
    sim.add_node_at(Probe::new(), ip(2));
    for _ in 0..20 {
        sim.command(
            0,
            a,
            ProbeCmd::Send {
                local: sa(1),
                remote: sa(2),
                data: vec![0; 1000],
            },
        );
    }
    sim.run_until(SEC);
    // Backlog ahead of the k-th datagram is k * 1000 bytes: k = 0..=5 are admitted (and then lost).
    assert_eq!(sim.metrics().dropped(DropReason::Loss), 6);
    assert_eq!(sim.metrics().dropped(DropReason::QueueFull), 14);
}

fn lans(sim: &mut Sim<Probe>, region_b: u32) -> (NodeId, NodeId, LanId, LanId) {
    let mk = |region| LanConfig {
        up: LinkConfig {
            bandwidth_bps: 8_000_000,
            delay: 5 * MS,
            ..LinkConfig::default()
        },
        down: LinkConfig {
            bandwidth_bps: 8_000_000,
            delay: 3 * MS,
            ..LinkConfig::default()
        },
        region,
        ..LanConfig::default()
    };
    let (la, lb) = (sim.add_lan(mk(0)), sim.add_lan(mk(region_b)));
    sim.set_region_delay(0, 1, 40 * MS);
    let (a, b) = (sim.add_node(Probe::new()), sim.add_node(Probe::new()));
    sim.add_iface_in(a, ip(1), la);
    sim.add_iface_in(b, ip(2), lb);
    (a, b, la, lb)
}

#[test]
fn a_datagram_crosses_uplink_region_and_downlink() {
    let mut sim: Sim<Probe> = Sim::new(1);
    let (a, b, ..) = lans(&mut sim, 1);
    send(&mut sim, 0, a, 1, 2, 1);
    sim.command(
        0,
        a,
        ProbeCmd::Send {
            local: sa(1),
            remote: sa(2),
            data: vec![0; 1000],
        },
    );
    sim.run_until(SEC);
    // The one-byte datagram takes 1 us of line time and the 1000-byte one waits for it on the uplink.
    let times: Vec<Time> = sim.events(b).iter().map(|(t, _)| *t).collect();
    assert_eq!(times.len(), 2);
    assert_eq!(
        times[1],
        50 * MS + 1000,
        "1 ms + 5 ms up, 40 ms region, 1 ms + 3 ms down, and 1 us behind the first datagram"
    );
    assert_eq!(sim.metrics().nodes[b.index()].latency.max, times[1]);
}

#[test]
fn wire_bytes_are_counted_before_drops_but_not_for_oversize_datagrams() {
    let mut sim: Sim<Probe> = Sim::new(1);
    let (a, _b, _la, lb) = lans(&mut sim, 1);
    let lossy = LinkConfig {
        loss: Loss::Bernoulli(1.0),
        ..LinkConfig::default()
    };
    sim.lan_link_change(0, lb, LanDir::Down, LinkChange::Config(lossy));
    sim.command(
        MS,
        a,
        ProbeCmd::Send {
            local: sa(1),
            remote: sa(2),
            data: vec![0; 1000],
        },
    );
    sim.command(
        MS,
        a,
        ProbeCmd::Send {
            local: sa(1),
            remote: sa(2),
            data: vec![0; 1473],
        },
    );
    sim.run_until(SEC);
    assert_eq!(sim.metrics().dropped(DropReason::Mtu), 1);
    assert_eq!(sim.metrics().nodes[a.index()].wire_bytes, 1000 + 28);
    assert_eq!(sim.metrics().wire_bytes(), 1028);
    assert_eq!(sim.metrics().nodes[a.index()].sent_packets, 1);
}

#[test]
fn reference_driver_leaves_intents_unpumped_until_the_next_pump() {
    for (driver, expect) in [(Driver::Vinc, vec![1]), (Driver::Reference, vec![])] {
        let mut sim: Sim<Probe> = Sim::with_config(1, SimConfig { driver, ..cfg(MS) });
        let (a, b) = (
            sim.add_node_at(Probe::new(), ip(1)),
            sim.add_node_at(Probe::new(), ip(2)),
        );
        sim.command_nopump(
            0,
            a,
            ProbeCmd::Send {
                local: sa(1),
                remote: sa(2),
                data: vec![1],
            },
        );
        sim.run_until(SEC);
        assert_eq!(tags(&sim, b), expect, "{driver:?}");
        // A pumped command makes the node poll, and the waiting datagram leaves.
        sim.command(2 * SEC, a, ProbeCmd::Timer(10 * SEC));
        sim.run_until(3 * SEC);
        assert_eq!(tags(&sim, b), vec![1], "{driver:?}");
    }
}

struct TickCost;

impl CostModel for TickCost {
    fn cost(&self, cpu: &Cpu, call: Call, _bytes: usize, work: Work) -> Time {
        match call {
            Call::Datagram => work.ticks * 100 * u64::from(cpu.factor_milli) / 1000,
            _ => 0,
        }
    }
}

#[test]
fn a_custom_cost_model_turns_reported_work_into_busy_time() {
    let mut sim = Sim::<Probe, Rng, TickCost>::with_parts(1, cfg(0), TickCost);
    let a = sim.add_node_at(Probe::new(), ip(1));
    let mut busy = Probe::new();
    busy.ticks_per_call = 10_000;
    let b = sim.add_node_at(busy, ip(2));
    sim.set_cpu(
        b,
        Cpu {
            factor_milli: 2000,
            per_call: 0,
            per_kib: 0,
        },
    );
    for t in 0..3 {
        sim.command(
            0,
            a,
            ProbeCmd::Send {
                local: sa(1),
                remote: sa(2),
                data: vec![t],
            },
        );
    }
    sim.run_until(SEC);
    assert_eq!(sim.node(b).call_times, vec![0, 2 * MS, 4 * MS]);
}

#[test]
fn transmits_leave_after_the_busy_period_and_honour_send_at() {
    let mut sim = Sim::<Probe, Rng, FlatCost>::with_parts(1, cfg(2 * MS), FlatCost);
    let (a, b) = (
        sim.add_node_at(Probe::new(), ip(1)),
        sim.add_node_at(Probe::new(), ip(2)),
    );
    sim.set_cpu(
        a,
        Cpu {
            factor_milli: 1000,
            per_call: 10 * MS,
            per_kib: 0,
        },
    );
    send(&mut sim, 0, a, 1, 2, 1);
    sim.command(
        SEC,
        a,
        ProbeCmd::SendAt {
            local: sa(1),
            remote: sa(2),
            data: vec![2],
            at: SEC + 50 * MS,
        },
    );
    sim.run_until(2 * SEC);
    let times: Vec<Time> = sim.events(b).iter().map(|(t, _)| *t).collect();
    // The command ran at 0 and finished at 10 ms, when its datagram left; 2 ms of delay on top.
    assert_eq!(times, vec![12 * MS, SEC + 50 * MS + 2 * MS]);
}

/// A random source that always draws the same number, to show the engine takes any source.
struct Fixed(f64);

impl Random for Fixed {
    fn derive(_: u64, _: Stream) -> Self {
        Self(0.5)
    }
    fn random(&mut self) -> f64 {
        self.0
    }
    fn below(&mut self, _: u64) -> u64 {
        0
    }
    fn fill(&mut self, buf: &mut [u8]) {
        buf.fill(0);
    }
}

#[test]
fn the_random_source_is_pluggable() {
    for (p, delivered) in [(0.6, 0), (0.4, 10)] {
        let link = LinkConfig {
            loss: Loss::Bernoulli(p),
            ..LinkConfig::default()
        };
        let c = SimConfig {
            default_link: Some(link),
            ..SimConfig::default()
        };
        let mut sim = Sim::<Probe, Fixed, FlatCost>::with_parts(1, c, FlatCost);
        let (a, b) = (
            sim.add_node_at(Probe::new(), ip(1)),
            sim.add_node_at(Probe::new(), ip(2)),
        );
        for t in 0..10 {
            sim.command(
                0,
                a,
                ProbeCmd::Send {
                    local: sa(1),
                    remote: sa(2),
                    data: vec![t],
                },
            );
        }
        sim.run_until(SEC);
        assert_eq!(sim.events(b).len(), delivered, "loss {p} with every draw 0.5");
    }
}

#[test]
fn timeouts_that_do_not_advance_are_counted_and_pushed_one_millisecond() {
    let mut sim: Sim<Probe> = Sim::new(1);
    let mut sticky = Probe::new();
    sticky.sticky = true;
    let a = sim.add_node_at(sticky, ip(1));
    sim.command(0, a, ProbeCmd::Timer(MS));
    sim.run_until(5 * MS + 500_000);
    let times: Vec<Time> = sim.events(a).iter().map(|(t, _)| *t).collect();
    assert_eq!(times, vec![MS, 2 * MS, 3 * MS, 4 * MS, 5 * MS]);
    assert_eq!(sim.metrics().timer_violations, 5);
}

const NAT_EXT: IpAddr = IpAddr::V4(Ipv4Addr::new(203, 0, 113, 1));
const PRIV: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 0, 2)), 4000);
const S1: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(1, 1, 1, 1)), 443);

fn nat_cfg(kind: NatKind, ports: PortPolicy, no_punch: bool) -> NatConfig {
    NatConfig {
        kind,
        ext_ip: NAT_EXT,
        mapping_timeout: 600 * SEC,
        refresh_on_inbound: false,
        port_base: 20_000,
        ports,
        no_punch,
    }
}

fn nat_world(seed: u64, c: NatConfig) -> (Sim<Probe>, vinc_sim::NatId, NodeId, NodeId) {
    let mut sim = Sim::with_config(seed, cfg(MS));
    let nat = sim.add_nat(c);
    let a = sim.add_node(Probe::new());
    sim.add_iface_behind(a, PRIV.ip(), nat);
    let s = sim.add_node_at(Probe::new(), S1.ip());
    (sim, nat, a, s)
}

fn ext_ports(sim: &Sim<Probe>, s: NodeId) -> Vec<u16> {
    sim.events(s)
        .iter()
        .filter_map(|(_, e)| {
            if let ProbeEvent::Recv { remote, .. } = e {
                Some(remote.port())
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn randomized_ports_start_in_range_and_advance_by_one_to_seven() {
    let run = |seed| {
        let (mut sim, _, a, s) = nat_world(seed, nat_cfg(NatKind::Symmetric, PortPolicy::Randomized, false));
        for i in 0..100u16 {
            let remote = SocketAddr::new(S1.ip(), 1000 + i);
            sim.command(
                u64::from(i) * MS,
                a,
                ProbeCmd::Send {
                    local: PRIV,
                    remote,
                    data: vec![0],
                },
            );
        }
        sim.run_until(SEC);
        ext_ports(&sim, s)
    };
    let ports = run(3);
    assert_eq!(ports.len(), 100);
    assert!((20_000..40_000).contains(&ports[0]));
    assert!(ports.windows(2).all(|w| (1..=7).contains(&(w[1] - w[0]))));
    assert_eq!(ports, run(3));
    assert_ne!(ports, run(4));
}

#[test]
fn a_mapping_remembers_at_most_64_contacted_remotes() {
    let (mut sim, _, a, s) = nat_world(1, nat_cfg(NatKind::PortRestricted, PortPolicy::Sequential, false));
    for p in 1..=65u16 {
        sim.command(
            0,
            a,
            ProbeCmd::Send {
                local: PRIV,
                remote: SocketAddr::new(S1.ip(), p),
                data: vec![0],
            },
        );
    }
    sim.run_until(SEC);
    let ext = SocketAddr::new(NAT_EXT, ext_ports(&sim, s)[0]);
    for p in [1u16, 64, 65] {
        sim.command(
            SEC,
            s,
            ProbeCmd::Send {
                local: SocketAddr::new(S1.ip(), p),
                remote: ext,
                data: vec![p as u8],
            },
        );
    }
    sim.run_until(2 * SEC);
    let (_, _, a2) = (0, 0, a);
    assert_eq!(tags(&sim, a2), vec![1, 64]);
}

#[test]
fn no_punch_admits_only_public_sources_and_punches_are_counted() {
    for no_punch in [false, true] {
        let mut sim: Sim<Probe> = Sim::with_config(1, cfg(MS));
        let nat1 = sim.add_nat(nat_cfg(NatKind::FullCone, PortPolicy::Sequential, no_punch));
        let ext2 = IpAddr::V4(Ipv4Addr::new(203, 0, 113, 2));
        let nat2 = sim.add_nat(NatConfig {
            ext_ip: ext2,
            ..nat_cfg(NatKind::FullCone, PortPolicy::Sequential, false)
        });
        let (a, b, s) = (
            sim.add_node(Probe::new()),
            sim.add_node(Probe::new()),
            sim.add_node_at(Probe::new(), S1.ip()),
        );
        let b_priv = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 2)), 4000);
        sim.add_iface_behind(a, PRIV.ip(), nat1);
        sim.add_iface_behind(b, b_priv.ip(), nat2);
        sim.command(
            0,
            a,
            ProbeCmd::Send {
                local: PRIV,
                remote: S1,
                data: vec![1],
            },
        );
        sim.run_until(SEC);
        let ext_a = SocketAddr::new(NAT_EXT, ext_ports(&sim, s)[0]);
        sim.command(
            SEC,
            s,
            ProbeCmd::Send {
                local: S1,
                remote: ext_a,
                data: vec![2],
            },
        );
        sim.command(
            SEC,
            b,
            ProbeCmd::Send {
                local: b_priv,
                remote: ext_a,
                data: vec![3],
            },
        );
        sim.run_until(2 * SEC);
        assert_eq!(tags(&sim, a), if no_punch { vec![2] } else { vec![2, 3] });
        assert_eq!(sim.nat_punched(nat1), u64::from(!no_punch));
        let _ = nat2;
    }
}

#[test]
fn rebind_moves_mappings_to_new_ports_and_keeps_their_filters() {
    let (mut sim, nat, a, s) = nat_world(1, nat_cfg(NatKind::PortRestricted, PortPolicy::Sequential, false));
    sim.command(
        0,
        a,
        ProbeCmd::Send {
            local: PRIV,
            remote: S1,
            data: vec![1],
        },
    );
    sim.nat_rebind(2 * SEC, nat, None);
    sim.run_until(3 * SEC);
    assert_eq!(ext_ports(&sim, s), vec![20_000]);
    // The mapping is now on 20001 and still lets S1 in, though the private host has sent nothing since.
    sim.command(
        3 * SEC,
        s,
        ProbeCmd::Send {
            local: S1,
            remote: SocketAddr::new(NAT_EXT, 20_000),
            data: vec![2],
        },
    );
    sim.command(
        3 * SEC,
        s,
        ProbeCmd::Send {
            local: S1,
            remote: SocketAddr::new(NAT_EXT, 20_001),
            data: vec![3],
        },
    );
    sim.run_until(4 * SEC);
    assert_eq!(tags(&sim, a), vec![3]);
    assert_eq!(sim.nat_mappings(nat), 1);
}

#[test]
fn udp_block_and_captive_portal_drop_udp_both_ways() {
    let mut sim: Sim<Probe> = Sim::with_config(1, cfg(MS));
    let (la, lb) = (sim.add_lan(LanConfig::default()), sim.add_lan(LanConfig::default()));
    let (a, b) = (sim.add_node(Probe::new()), sim.add_node(Probe::new()));
    sim.add_iface_in(a, ip(1), la);
    sim.add_iface_in(b, ip(2), lb);
    sim.set_udp_block(SEC, lb, true);
    sim.set_udp_block(3 * SEC, lb, false);
    send(&mut sim, 0, a, 1, 2, 1);
    send(&mut sim, 2 * SEC, a, 1, 2, 2);
    send(&mut sim, 2 * SEC, b, 2, 1, 3);
    send(&mut sim, 4 * SEC, a, 1, 2, 4);
    sim.run_until(5 * SEC);
    assert_eq!(tags(&sim, b), vec![1, 4]);
    assert!(tags(&sim, a).is_empty());
    assert_eq!(sim.metrics().dropped(DropReason::Middlebox), 2);

    sim.set_portal(b, 10 * SEC);
    sim.set_udp_block(5 * SEC, lb, false);
    send(&mut sim, 6 * SEC, a, 1, 2, 5);
    send(&mut sim, 7 * SEC, b, 2, 1, 6);
    send(&mut sim, 11 * SEC, a, 1, 2, 7);
    sim.crash(12 * SEC, b);
    sim.restart(13 * SEC, b);
    send(&mut sim, 14 * SEC, a, 1, 2, 8);
    send(&mut sim, 24 * SEC, a, 1, 2, 9);
    sim.run_until(30 * SEC);
    assert_eq!(tags(&sim, b), vec![1, 4, 7, 9]);
}

#[test]
fn lan_partitions_are_judged_at_the_uplink_send_time() {
    let mut sim: Sim<Probe> = Sim::with_config(1, cfg(MS));
    let (la, lb) = (sim.add_lan(LanConfig::default()), sim.add_lan(LanConfig::default()));
    let (a, b) = (sim.add_node(Probe::new()), sim.add_node(Probe::new()));
    sim.add_iface_in(a, ip(1), la);
    sim.add_iface_in(b, ip(2), lb);
    sim.partition_lans(SEC, 3 * SEC, &[la], &[lb], false);
    send(&mut sim, 2 * SEC, a, 1, 2, 1);
    send(&mut sim, 2 * SEC, b, 2, 1, 2);
    send(&mut sim, 4 * SEC, a, 1, 2, 3);
    sim.run_until(5 * SEC);
    assert_eq!(tags(&sim, b), vec![3]);
    assert_eq!(tags(&sim, a), vec![2]);
    assert_eq!(sim.metrics().dropped(DropReason::Partition), 1);
}

#[test]
fn the_ipv6_firewall_admits_only_remotes_the_host_sent_to() {
    let v6 = |d: u16| IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, d));
    let mut sim: Sim<Probe> = Sim::with_config(1, cfg(MS));
    let lan = sim.add_lan(LanConfig {
        v6_firewall: true,
        ..LanConfig::default()
    });
    let (x, h) = (sim.add_node(Probe::new()), sim.add_node_at(Probe::new(), v6(2)));
    sim.add_iface_in(x, v6(1), lan);
    let (xa, ha) = (SocketAddr::new(v6(1), 7), SocketAddr::new(v6(2), 443));
    let put = |sim: &mut Sim<Probe>, at, from, local, remote, tag| {
        sim.command(
            at,
            from,
            ProbeCmd::Send {
                local,
                remote,
                data: vec![tag],
            },
        );
    };
    put(&mut sim, SEC, h, ha, xa, 1);
    put(&mut sim, 2 * SEC, x, xa, ha, 2);
    put(&mut sim, 3 * SEC, h, ha, xa, 3);
    put(&mut sim, 3 * SEC, h, SocketAddr::new(v6(2), 444), xa, 4);
    sim.run_until(4 * SEC);
    assert_eq!(tags(&sim, x), vec![3]);
    assert_eq!(sim.metrics().dropped(DropReason::NatFilter), 2);
}

#[test]
fn the_local_clock_follows_offset_drift_and_jumps() {
    let clock = Clock {
        offset: -30 * SEC as i64,
        drift_ppm: 50,
        jumps: vec![(10 * SEC, 2 * SEC as i64)],
    };
    assert_eq!(clock.local(0), -30_000_000_000);
    assert_eq!(
        clock.local(20 * SEC),
        -30_000_000_000 + 20_000_000_000 + 1_000_000 + 2_000_000_000
    );
    assert_eq!(clock.to_true(0, -31 * SEC as i64), 0);
    assert_eq!(clock.to_true(0, -29 * SEC as i64), 999_950_003);

    let mut sim: Sim<Probe> = Sim::new(1);
    let n = sim.add_node_at(Probe::new(), ip(1));
    sim.set_clock(n, clock.clone());
    sim.run_until(20 * SEC);
    assert_eq!(sim.clock(n), &clock);
    assert_eq!(sim.local_time(n), clock.local(20 * SEC));
}
