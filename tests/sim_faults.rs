//! The `vinc-sim` faults and adversaries: partitions, crash and restart, suspension, interface changes, middleboxes,
//! spoofed floods, replays and the on-path observer.
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

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_sim::toy::{Probe, ProbeCmd, ProbeEvent, Toy, ToyCmd, ToyConfig, ToyEvent};
use vinc_sim::{
    DropReason, FloodPayload, FloodSpec, IfaceEvent, LinkChange, LinkConfig, MS, NodeId, NodeState, SEC, Sim, SimConfig,
};

const fn ip(d: u8) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(10, 0, 0, d))
}

const fn sa(d: u8) -> SocketAddr {
    SocketAddr::new(ip(d), 1)
}

fn cfg(delay: u64) -> SimConfig {
    SimConfig {
        default_link: Some(LinkConfig {
            delay,
            ..LinkConfig::default()
        }),
        ..SimConfig::default()
    }
}

fn send(sim: &mut Sim<Probe>, at: u64, from: NodeId, a: u8, b: u8, tag: u8) {
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

fn toy_pair(delay: u64, total: u32, msg_len: usize) -> (Sim<Toy>, NodeId, NodeId) {
    let mut sim = Sim::with_config(4, cfg(delay));
    let (c, s) = (SocketAddr::new(ip(1), 5000), SocketAddr::new(ip(2), 443));
    let base = ToyConfig {
        local: c,
        peer: Some(s),
        total,
        window: 4,
        msg_len,
        rto: 50 * MS,
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
    sim.command(MS, client, ToyCmd::Start);
    (sim, client, server)
}

#[test]
fn partition_blocks_across_groups_and_heal_restores() {
    let mut sim = Sim::with_config(1, cfg(MS));
    let ns: Vec<NodeId> = (1..=3).map(|d| sim.add_node_at(Probe::new(), ip(d))).collect();
    sim.partition(SEC, &[&[ns[0]], &[ns[1], ns[2]]]);
    sim.heal(3 * SEC);
    send(&mut sim, 0, ns[0], 1, 2, 1);
    send(&mut sim, 2 * SEC, ns[0], 1, 2, 2);
    send(&mut sim, 2 * SEC, ns[1], 2, 3, 3);
    send(&mut sim, 2 * SEC, ns[2], 3, 1, 4);
    send(&mut sim, 4 * SEC, ns[0], 1, 2, 5);
    sim.run_until(5 * SEC);
    assert_eq!(tags(&sim, ns[1]), vec![1, 5]);
    assert_eq!(tags(&sim, ns[2]), vec![3]);
    assert!(tags(&sim, ns[0]).is_empty());
    assert_eq!(sim.metrics().dropped(DropReason::Partition), 2);
}

#[test]
fn unlisted_nodes_form_their_own_group() {
    let mut sim = Sim::with_config(1, cfg(MS));
    let ns: Vec<NodeId> = (1..=3).map(|d| sim.add_node_at(Probe::new(), ip(d))).collect();
    sim.partition(0, &[&[ns[0]]]);
    send(&mut sim, SEC, ns[1], 2, 3, 1);
    send(&mut sim, SEC, ns[1], 2, 1, 2);
    sim.run_until(2 * SEC);
    assert_eq!(tags(&sim, ns[2]), vec![1]);
    assert!(tags(&sim, ns[0]).is_empty());
}

#[test]
fn a_transfer_stalls_across_a_partition_and_finishes_after_the_heal() {
    let (mut sim, client, server) = toy_pair(5 * MS, 100, 100);
    sim.partition(100 * MS, &[&[client], &[server]]);
    sim.heal(5 * SEC);
    assert!(sim.run_until_pred(60 * SEC, |s| s.node(client).is_complete()));
    let during: Vec<_> = sim
        .events(client)
        .iter()
        .filter(|(t, e)| *t > 150 * MS && *t < 5 * SEC && matches!(e, ToyEvent::Echoed(_)))
        .collect();
    assert!(during.is_empty(), "nothing is echoed while partitioned");
    assert!(sim.now() > 5 * SEC);
}

#[test]
fn crash_loses_volatile_state_and_restart_hands_back_the_persisted_bytes() {
    let mut sim = Sim::with_config(1, cfg(MS));
    let (a, b) = (
        sim.add_node_at(Probe::new(), ip(1)),
        sim.add_node_at(Probe::new(), ip(2)),
    );
    sim.command(0, b, ProbeCmd::Persist(vec![9, 8, 7]));
    sim.command(0, b, ProbeCmd::Timer(10 * SEC));
    sim.crash(SEC, b);
    send(&mut sim, 2 * SEC, a, 1, 2, 1);
    sim.command(2 * SEC, b, ProbeCmd::Persist(vec![1]));
    sim.restart(3 * SEC, b);
    send(&mut sim, 4 * SEC, a, 1, 2, 2);
    sim.run_until(20 * SEC);
    assert_eq!(sim.state(b), NodeState::Up);
    assert_eq!(sim.node(b).restarts, 1);
    assert_eq!(sim.node(b).restored, vec![9, 8, 7]);
    assert_eq!(tags(&sim, b), vec![2], "the datagram sent while it was down is lost");
    assert_eq!(sim.metrics().dropped(DropReason::NodeDown), 1);
    assert!(
        !sim.events(b).iter().any(|(_, e)| matches!(e, ProbeEvent::Timer(_))),
        "the timer died with the process"
    );
}

#[test]
fn restart_does_nothing_unless_crashed() {
    let mut sim: Sim<Probe> = Sim::new(1);
    let a = sim.add_node_at(Probe::new(), ip(1));
    sim.restart(SEC, a);
    sim.resume(SEC, a);
    sim.run_until(2 * SEC);
    assert_eq!(sim.node(a).restarts, 0);
    assert!(sim.node(a).sleeps.is_empty());
}

#[test]
fn a_crashed_client_resumes_from_its_persisted_progress() {
    let (mut sim, client, _server) = toy_pair(5 * MS, 400, 100);
    assert!(sim.run_until_pred(60 * SEC, |s| s.node(client).done_count() >= 150));
    let crash_at = sim.now();
    sim.crash(crash_at, client);
    sim.restart(crash_at + SEC, client);
    sim.run_until(crash_at + 500 * MS);
    assert_eq!(sim.state(client), NodeState::Crashed);
    assert!(sim.run_until_pred(crash_at + 60 * SEC, |s| s.node(client).is_complete()));
    assert_eq!(sim.node(client).restored_len, 1 + 400);
    let echoed_after: Vec<u32> = sim
        .events(client)
        .iter()
        .filter(|(t, _)| *t > crash_at)
        .filter_map(|(_, e)| if let ToyEvent::Echoed(s) = e { Some(*s) } else { None })
        .collect();
    let before: Vec<u32> = sim
        .events(client)
        .iter()
        .filter(|(t, _)| *t <= crash_at)
        .filter_map(|(_, e)| if let ToyEvent::Echoed(s) = e { Some(*s) } else { None })
        .collect();
    assert!(before.len() >= 150);
    assert!(
        echoed_after.iter().all(|s| !before.contains(s)),
        "persisted progress is not redone"
    );
    assert_eq!(before.len() + echoed_after.len(), 400);
}

#[test]
fn a_suspended_node_is_not_called_and_loses_arriving_datagrams() {
    let mut sim = Sim::with_config(1, cfg(MS));
    let (a, b) = (
        sim.add_node_at(Probe::new(), ip(1)),
        sim.add_node_at(Probe::new(), ip(2)),
    );
    sim.command(0, b, ProbeCmd::Timer(2 * SEC));
    sim.suspend(SEC, b);
    send(&mut sim, SEC + 500 * MS, a, 1, 2, 1);
    sim.command(SEC + 600 * MS, b, ProbeCmd::Persist(vec![1]));
    sim.resume(4 * SEC, b);
    send(&mut sim, 5 * SEC, a, 1, 2, 2);
    sim.run_until(6 * SEC);
    assert_eq!(sim.node(b).sleeps, vec![(SEC, true), (4 * SEC, false)]);
    assert_eq!(tags(&sim, b), vec![2]);
    assert_eq!(sim.metrics().dropped(DropReason::NodeAsleep), 1);
    // The timer that came due during the sleep fires as soon as the node runs again, on its monotonic clock.
    assert!(
        sim.events(b)
            .iter()
            .any(|(t, e)| *t == 4 * SEC && *e == ProbeEvent::Timer(4 * SEC))
    );
}

#[test]
fn interface_down_up_and_address_changes_reach_the_node() {
    let mut sim = Sim::with_config(1, cfg(MS));
    let (a, b) = (
        sim.add_node_at(Probe::new(), ip(1)),
        sim.add_node_at(Probe::new(), ip(2)),
    );
    sim.set_iface_up(SEC, a, 0, false);
    send(&mut sim, 2 * SEC, a, 1, 2, 1);
    send(&mut sim, 2 * SEC, b, 2, 1, 2);
    sim.set_iface_up(3 * SEC, a, 0, true);
    sim.set_iface_addr(4 * SEC, a, 0, ip(9));
    send(&mut sim, 5 * SEC, a, 9, 2, 3);
    send(&mut sim, 5 * SEC, b, 2, 1, 4);
    send(&mut sim, 5 * SEC, b, 2, 9, 5);
    sim.run_until(6 * SEC);
    assert_eq!(
        sim.node(a).ifaces,
        vec![
            IfaceEvent::Down(ip(1)),
            IfaceEvent::Up(ip(1)),
            IfaceEvent::Changed { old: ip(1), new: ip(9) }
        ]
    );
    assert_eq!(tags(&sim, b), vec![3]);
    assert_eq!(tags(&sim, a), vec![5]);
    assert_eq!(
        sim.metrics().dropped(DropReason::NoIface),
        2,
        "send from a down interface, receive on a down interface"
    );
    assert_eq!(sim.metrics().dropped(DropReason::NoRoute), 1, "the old address is gone");
}

#[test]
fn a_client_that_changes_address_finishes_its_transfer() {
    let (mut sim, client, server) = toy_pair(5 * MS, 200, 100);
    sim.set_iface_addr(100 * MS, client, 0, ip(9));
    assert!(sim.run_until_pred(60 * SEC, |s| s.node(client).is_complete()));
    assert_eq!(sim.node(client).local.ip(), ip(9));
    assert_eq!(sim.node(server).done_count(), 0);
}

#[test]
fn udp_blocked_until_the_block_lifts() {
    let (mut sim, client, server) = toy_pair(5 * MS, 50, 100);
    let (sc, ss) = (sim.site(client), sim.site(server));
    sim.link_change(0, sc, ss, LinkChange::Blocked(true));
    sim.link_change(5 * SEC, sc, ss, LinkChange::Blocked(false));
    sim.run_until(4 * SEC);
    assert_eq!(sim.node(client).done_count(), 0);
    assert!(sim.metrics().dropped(DropReason::Blocked) > 10);
    assert!(sim.run_until_pred(60 * SEC, |s| s.node(client).is_complete()));
}

#[test]
fn an_mtu_black_hole_swallows_big_datagrams_without_a_signal() {
    let (mut sim, client, server) = toy_pair(5 * MS, 20, 1400);
    let (sc, ss) = (sim.site(client), sim.site(server));
    sim.link_change(0, sc, ss, LinkChange::Mtu(1200));
    sim.run_until(10 * SEC);
    assert_eq!(sim.node(client).done_count(), 0);
    assert!(sim.metrics().dropped(DropReason::Mtu) > 20);
    sim.link_change(10 * SEC, sc, ss, LinkChange::Mtu(1500));
    assert!(sim.run_until_pred(60 * SEC, |s| s.node(client).is_complete()));
}

fn flood_world(rate: u64, payload: FloodPayload) -> (Sim<Probe>, NodeId) {
    let mut sim = Sim::with_config(6, cfg(2 * MS));
    let victim = sim.add_node_at(Probe::new(), ip(2));
    let host = sim.add_host(ip(66));
    let spoof = vec![sa(100), sa(101), sa(102)];
    sim.flood(
        host,
        FloodSpec {
            start: SEC,
            end: 3 * SEC,
            rate_pps: rate,
            dst: sa(2),
            spoof,
            payload,
        },
    );
    (sim, victim)
}

#[test]
fn a_spoofed_flood_arrives_at_its_rate_with_forged_sources() {
    let (mut sim, victim) = flood_world(1000, FloodPayload::Fixed(vec![0xAB; 64]));
    sim.run_until(5 * SEC);
    let evs = sim.events(victim);
    assert_eq!(evs.len(), 2000);
    assert_eq!(sim.metrics().injected, 2000);
    assert_eq!(evs[0].0, SEC + 2 * MS);
    assert_eq!(evs[1999].0, SEC + 1999 * MS + 2 * MS);
    for (i, (_, e)) in evs.iter().enumerate() {
        let ProbeEvent::Recv { remote, data, .. } = e else {
            panic!()
        };
        assert_eq!(*remote, sa(100 + (i % 3) as u8));
        assert_eq!(data, &vec![0xAB; 64]);
    }
    assert_eq!(sim.metrics().nodes[victim.index()].recv_packets, 2000);
}

#[test]
fn a_flood_can_carry_fresh_random_bytes() {
    let (mut sim, victim) = flood_world(100, FloodPayload::Random(32));
    sim.run_until(5 * SEC);
    let mut seen: Vec<Vec<u8>> = sim
        .events(victim)
        .iter()
        .map(|(_, e)| {
            if let ProbeEvent::Recv { data, .. } = e {
                data.clone()
            } else {
                vec![]
            }
        })
        .collect();
    assert_eq!(seen.len(), 200);
    seen.sort();
    seen.dedup();
    assert_eq!(seen.len(), 200);
}

#[test]
fn an_observer_records_time_size_and_header_and_replay_resends_captures() {
    let mut sim = Sim::with_config(2, cfg(3 * MS));
    let (a, b) = (
        sim.add_node_at(Probe::new(), ip(1)),
        sim.add_node_at(Probe::new(), ip(2)),
    );
    let host = sim.add_host(ip(66));
    let obs = sim.observe(a, b, 4, true).unwrap();
    assert!(sim.observe(b, a, 4, false).is_some());
    for i in 0..5u8 {
        let mut data = vec![i; 40 + usize::from(i)];
        data[..2].copy_from_slice(&[0xC0, i]);
        sim.command(
            u64::from(i) * 10 * MS,
            a,
            ProbeCmd::Send {
                local: sa(1),
                remote: sa(2),
                data,
            },
        );
    }
    sim.replay(SEC, host, obs, 1, 4, 10 * MS);
    sim.run_until(2 * SEC);

    let recs = &sim.observer(obs).records;
    assert_eq!(recs.len(), 5);
    for (i, r) in recs.iter().enumerate() {
        assert_eq!(r.time, i as u64 * 10 * MS);
        assert_eq!(r.size, 40 + i);
        assert_eq!(r.header, vec![0xC0, i as u8, i as u8, i as u8]);
        assert_eq!((r.src, r.dst), (sa(1), sa(2)));
    }
    // Five originals, then three replays of captures 1, 2 and 3 with the original claimed source.
    let got = sim.events(b);
    assert_eq!(got.len(), 8);
    for (k, (t, e)) in got[5..].iter().enumerate() {
        let ProbeEvent::Recv { remote, data, .. } = e else {
            panic!()
        };
        assert_eq!(*remote, sa(1));
        assert_eq!(data, recs[k + 1].payload.as_ref().unwrap());
        assert_eq!(*t, SEC + k as u64 * 10 * MS + 3 * MS);
    }
    assert_eq!(sim.metrics().injected, 3);
}

#[test]
fn an_observer_only_sees_what_the_link_accepted() {
    let mut sim = Sim::with_config(2, cfg(MS));
    let (a, b) = (
        sim.add_node_at(Probe::new(), ip(1)),
        sim.add_node_at(Probe::new(), ip(2)),
    );
    let obs = sim.observe(a, b, 1, false).unwrap();
    sim.link_change(0, a, b, LinkChange::Mtu(10));
    send(&mut sim, MS, a, 1, 2, 1);
    sim.command(
        2 * MS,
        a,
        ProbeCmd::Send {
            local: sa(1),
            remote: sa(2),
            data: vec![0; 50],
        },
    );
    sim.run_until(SEC);
    assert_eq!(sim.observer(obs).records.len(), 1);
    assert!(sim.observer(obs).records[0].payload.is_none());
}

#[test]
fn a_host_receives_datagrams_addressed_to_it() {
    let mut sim = Sim::with_config(2, cfg(MS));
    let a = sim.add_node_at(Probe::new(), ip(1));
    let host = sim.add_host(ip(66));
    send(&mut sim, 0, a, 1, 66, 1);
    sim.run_until(SEC);
    assert_eq!(sim.host_received(host), 1);
}
