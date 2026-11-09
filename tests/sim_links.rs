//! The `vinc-sim` links: FIFO under jitter, explicit reordering, loss models, duplication, bandwidth and queue,
//! MTU, asymmetry and scheduled changes.
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

use vinc_sim::toy::{Probe, ProbeCmd, ProbeEvent};
use vinc_sim::{DropReason, LinkChange, LinkConfig, Loss, MS, NodeId, SEC, Sim, SimConfig, US};

const A: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1)), 1);
const B: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 2)), 1);

/// Two probes with the same link in both directions.
fn pair(seed: u64, link: LinkConfig) -> (Sim<Probe>, NodeId, NodeId) {
    let cfg = SimConfig {
        default_link: Some(link),
        latency_samples: true,
        ..SimConfig::default()
    };
    let mut sim = Sim::with_config(seed, cfg);
    let a = sim.add_node_at(Probe::new(), A.ip());
    let b = sim.add_node_at(Probe::new(), B.ip());
    (sim, a, b)
}

/// Sends `n` datagrams of `len` bytes from A to B, one per `gap`; the first four bytes are the sequence number.
fn blast(sim: &mut Sim<Probe>, a: NodeId, n: u32, len: usize, gap: u64) {
    for i in 0..n {
        let mut data = vec![0; len];
        data[..4].copy_from_slice(&i.to_le_bytes());
        sim.command(
            u64::from(i) * gap,
            a,
            ProbeCmd::Send {
                local: A,
                remote: B,
                data,
            },
        );
    }
}

fn received(sim: &Sim<Probe>, b: NodeId) -> Vec<u32> {
    sim.events(b)
        .iter()
        .filter_map(|(_, e)| {
            if let ProbeEvent::Recv { data, .. } = e {
                Some(u32::from_le_bytes(data[..4].try_into().unwrap()))
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn jitter_never_reorders() {
    let link = LinkConfig {
        delay: 20 * MS,
        jitter: 50 * MS,
        ..LinkConfig::default()
    };
    let (mut sim, a, b) = pair(5, link);
    blast(&mut sim, a, 2000, 50, 100 * US);
    sim.run_until(5 * SEC);
    let got = received(&sim, b);
    assert_eq!(got, (0..2000).collect::<Vec<_>>());
    let lat = &sim.metrics().nodes[b.index()].latency;
    assert!(
        lat.min >= 20 * MS && lat.max <= 70 * MS && lat.max - lat.min > 20 * MS,
        "jitter must be applied: {lat:?}"
    );
}

#[test]
fn reorder_happens_only_when_explicit() {
    let base = LinkConfig {
        delay: 10 * MS,
        jitter: 5 * MS,
        ..LinkConfig::default()
    };
    // Depth and slot without a probability do nothing.
    let (mut sim, a, b) = pair(
        1,
        LinkConfig {
            reorder_depth: 4,
            ..base.clone()
        },
    );
    blast(&mut sim, a, 1000, 40, MS);
    sim.run_until(5 * SEC);
    assert_eq!(received(&sim, b), (0..1000).collect::<Vec<_>>());

    let (mut sim, a, b) = pair(
        1,
        LinkConfig {
            reorder_prob: 0.1,
            reorder_depth: 4,
            ..base
        },
    );
    blast(&mut sim, a, 1000, 40, MS);
    sim.run_until(5 * SEC);
    let got = received(&sim, b);
    assert_eq!(got.len(), 1000);
    let inversions = got.windows(2).filter(|w| w[0] > w[1]).count();
    assert!(
        (50..=200).contains(&inversions),
        "about 10% of datagrams are overtaken, saw {inversions}"
    );
    // A held-back datagram is overtaken by at most depth + the jitter spread of datagrams, never lost.
    let mut sorted = got;
    sorted.sort_unstable();
    assert_eq!(sorted, (0..1000).collect::<Vec<_>>());
}

#[test]
fn bernoulli_loss_rate_is_within_tolerance() {
    for p in [0.01, 0.1, 0.3] {
        let (mut sim, a, b) = pair(
            11,
            LinkConfig {
                loss: Loss::Bernoulli(p),
                ..LinkConfig::default()
            },
        );
        blast(&mut sim, a, 20_000, 20, US);
        sim.run_until(SEC);
        let lost = sim.metrics().dropped(DropReason::Loss);
        assert_eq!(lost + received(&sim, b).len() as u64, 20_000);
        let rate = lost as f64 / 20_000.0;
        let sigma = (p * (1.0 - p) / 20_000.0).sqrt();
        assert!((rate - p).abs() < 5.0 * sigma, "p {p} measured {rate}");
    }
}

/// The longest run of consecutive losses and the loss rate, from the received sequence numbers.
fn loss_shape(got: &[u32], sent: u32) -> (usize, f64) {
    let mut seen = vec![false; sent as usize];
    for g in got {
        seen[*g as usize] = true;
    }
    let (mut run, mut longest) = (0, 0);
    for s in &seen {
        run = if *s { 0 } else { run + 1 };
        longest = longest.max(run);
    }
    (longest, 1.0 - got.len() as f64 / f64::from(sent))
}

#[test]
fn gilbert_elliott_matches_its_stationary_rate_and_bursts() {
    let ge = Loss::GilbertElliott {
        good_to_bad: 0.02,
        bad_to_good: 0.2,
        loss_good: 0.0,
        loss_bad: 0.8,
    };
    // Stationary bad share 0.02 / 0.22, so 0.8 * 0.0909 = 7.27% overall.
    let (mut sim, a, b) = pair(
        3,
        LinkConfig {
            loss: ge,
            ..LinkConfig::default()
        },
    );
    blast(&mut sim, a, 50_000, 20, US);
    sim.run_until(SEC);
    let (longest, rate) = loss_shape(&received(&sim, b), 50_000);
    assert!((rate - 0.0727).abs() < 0.012, "rate {rate}");

    let (mut sim, a, b) = pair(
        3,
        LinkConfig {
            loss: Loss::Bernoulli(rate),
            ..LinkConfig::default()
        },
    );
    blast(&mut sim, a, 50_000, 20, US);
    sim.run_until(SEC);
    let (bern_longest, _) = loss_shape(&received(&sim, b), 50_000);
    assert!(
        longest >= 2 * bern_longest,
        "bursts must be longer than independent loss: {longest} vs {bern_longest}"
    );
}

#[test]
fn duplication_rate_is_within_tolerance() {
    let (mut sim, a, b) = pair(
        9,
        LinkConfig {
            dup_prob: 0.1,
            delay: MS,
            ..LinkConfig::default()
        },
    );
    blast(&mut sim, a, 10_000, 20, 10 * US);
    sim.run_until(SEC);
    let got = received(&sim, b);
    let dups = sim.metrics().duplicated;
    assert_eq!(got.len() as u64, 10_000 + dups);
    assert!((dups as f64 / 10_000.0 - 0.1).abs() < 0.015, "dups {dups}");
    assert!(got.windows(2).all(|w| w[0] <= w[1]), "duplicates stay in order");
}

#[test]
fn bandwidth_spaces_datagrams_and_the_queue_drops_the_tail() {
    // 1 Mbit/s: a 1000-byte datagram takes 8 ms. A datagram is admitted while the backlog ahead of it is at most 10 kB.
    let link = LinkConfig {
        bandwidth_bps: 1_000_000,
        queue_bytes: 10_000,
        delay: 5 * MS,
        ..LinkConfig::default()
    };
    let (mut sim, a, b) = pair(1, link);
    blast(&mut sim, a, 100, 1000, 0);
    sim.run_until(SEC);
    let got = received(&sim, b);
    assert_eq!(
        got,
        (0..11).collect::<Vec<_>>(),
        "the backlog ahead of a datagram may reach the queue size, the rest are tail-dropped"
    );
    assert_eq!(sim.metrics().dropped(DropReason::QueueFull), 89);
    let times: Vec<u64> = sim.events(b).iter().map(|(t, _)| *t).collect();
    assert_eq!(times[0], 13 * MS);
    assert!(times.windows(2).all(|w| w[1] - w[0] == 8 * MS));
}

#[test]
fn a_paced_sender_below_the_rate_loses_nothing() {
    let link = LinkConfig {
        bandwidth_bps: 1_000_000,
        queue_bytes: 4_000,
        ..LinkConfig::default()
    };
    let (mut sim, a, b) = pair(1, link);
    blast(&mut sim, a, 200, 1000, 9 * MS);
    sim.run_until(10 * SEC);
    assert_eq!(received(&sim, b).len(), 200);
    assert_eq!(sim.metrics().total_dropped(), 0);
}

#[test]
fn mtu_drops_large_datagrams_silently() {
    let (mut sim, a, b) = pair(
        1,
        LinkConfig {
            mtu: 1200,
            ..LinkConfig::default()
        },
    );
    for (i, len) in [100, 1200, 1201, 1500, 800].into_iter().enumerate() {
        let mut data = vec![0; len];
        data[..4].copy_from_slice(&(i as u32).to_le_bytes());
        sim.command(
            0,
            a,
            ProbeCmd::Send {
                local: A,
                remote: B,
                data,
            },
        );
    }
    sim.run_until(SEC);
    assert_eq!(received(&sim, b), vec![0, 1, 4]);
    assert_eq!(sim.metrics().dropped(DropReason::Mtu), 2);
}

#[test]
fn directions_are_independent() {
    let (mut sim, a, b) = pair(1, LinkConfig::default());
    let (sa, sb) = (sim.site(a), sim.site(b));
    sim.set_link(
        sa,
        sb,
        LinkConfig {
            delay: 10 * MS,
            ..LinkConfig::default()
        },
    );
    sim.set_link(
        sb,
        sa,
        LinkConfig {
            delay: 50 * MS,
            loss: Loss::Bernoulli(1.0),
            ..LinkConfig::default()
        },
    );
    sim.command(
        0,
        a,
        ProbeCmd::Send {
            local: A,
            remote: B,
            data: vec![0; 8],
        },
    );
    sim.command(
        0,
        b,
        ProbeCmd::Send {
            local: B,
            remote: A,
            data: vec![0; 8],
        },
    );
    sim.run_until(SEC);
    assert_eq!(sim.events(b)[0].0, 10 * MS);
    assert!(sim.events(a).is_empty());
    assert_eq!(sim.metrics().dropped(DropReason::Loss), 1);
}

#[test]
fn outage_windows_mtu_changes_and_bandwidth_steps_apply_on_schedule() {
    let (mut sim, a, b) = pair(
        1,
        LinkConfig {
            delay: MS,
            ..LinkConfig::default()
        },
    );
    let (sa, sb) = (sim.site(a), sim.site(b));
    sim.outage(sa, sb, 100 * MS, 200 * MS);
    sim.link_change(300 * MS, sa, sb, LinkChange::Mtu(500));
    sim.link_change(400 * MS, sa, sb, LinkChange::Mtu(1500));
    sim.link_change(500 * MS, sa, sb, LinkChange::Bandwidth(800_000));
    // One 1000-byte datagram every 50 ms.
    blast(&mut sim, a, 20, 1000, 50 * MS);
    sim.run_until(5 * SEC);
    let got = received(&sim, b);
    // 100 and 150 ms are in the outage; 300 and 350 ms are over the 500-byte MTU.
    assert_eq!(got, (0..20).filter(|g| ![2, 3, 6, 7].contains(g)).collect::<Vec<_>>());
    assert_eq!(sim.metrics().dropped(DropReason::Blocked), 2);
    assert_eq!(sim.metrics().dropped(DropReason::Mtu), 2);
    // After the step each datagram takes 10 ms to serialise.
    let after: Vec<u64> = sim
        .events(b)
        .iter()
        .map(|(t, _)| *t)
        .filter(|t| *t > 500 * MS)
        .collect();
    assert!(!after.is_empty());
    assert_eq!(after[0] % MS, 0);
    assert_eq!(after[0], 500 * MS + 10 * MS + MS);
}

#[test]
fn links_have_independent_random_streams() {
    // Adding traffic on another link does not change the draws of this one.
    let lossy = LinkConfig {
        loss: Loss::Bernoulli(0.2),
        ..LinkConfig::default()
    };
    let run = |extra: bool| {
        let (mut sim, a, b) = pair(77, lossy.clone());
        sim.add_node_at(Probe::new(), IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3)));
        blast(&mut sim, a, 500, 20, 100 * US);
        if extra {
            for i in 0..300 {
                let to = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 3)), 1);
                sim.command(
                    i * 100 * US,
                    b,
                    ProbeCmd::Send {
                        local: B,
                        remote: to,
                        data: vec![0; 20],
                    },
                );
            }
        }
        sim.run_until(SEC);
        received(&sim, b)
    };
    assert_eq!(run(false), run(true));
}
