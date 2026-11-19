//! Time to the first byte of an answer through two endpoints on a slow, lossy path whose datagrams overtake each other
//! (5% loss, an extra delay drawn uniformly from 0 to 0.6 times the one-way delay for every datagram), for a new and
//! a resumed session, over 200 seeds at one-way delays of 0.1, 25 and 100 ms.
//!
//! A new session needs two round trips (Initial and Reply, then the first data with the Finish and its answer), and one
//! more when its handshake round trip is under 20 ms (the dialer waits for the server's READY); a resumed one needs a
//! single round trip (the Hello with its 0-RTT data, then the Reply and the answer). The median must stay within that
//! many round trips at the largest extra delay of every crossing: 6.4 (9.6 under 20 ms) and 3.2 one-way delays.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::print_stderr
)]

use pinc_core::{Command, Event, Role, SessionId, Value};
use pinc_tests::*;

const SEEDS: u64 = 200;

/// Write one byte on a new stream of session `s` of node `a` if the session reports Connected; returns whether it did.
fn write_when_connected(net: &mut CoreNet, a: usize, s: SessionId) -> bool {
    let t = net.now;
    if !net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == s)) {
        return false;
    }
    let Ok(Value::Stream(id)) = net.nodes[a]
        .cmd(t, Command::OpenStream { session: s, bidi: true })
        .map(|r| r.value)
    else {
        return false;
    };
    net.nodes[a]
        .cmd(
            t,
            Command::Write {
                session: s,
                stream: id,
                data: b"H",
            },
        )
        .unwrap();
    true
}

/// Dial from `a` to `b`, write one byte as soon as the session reports Connected (at once, with the first flight,
/// when resuming towards a peer the dialer may reach), answer it with one byte, and return the session and the time
/// from the dial to the answer.
fn first_byte(net: &mut CoreNet, a: usize, b: usize) -> (SessionId, u64) {
    for n in &mut net.nodes {
        n.events.clear();
        n.read.clear();
    }
    let (peer, to, t0) = (net.nodes[b].node, net.nodes[b].addr, net.now);
    let rep = net.nodes[a].connect(t0, peer, ALPN_A, to, Role::Other).unwrap();
    let sa = net.nodes[a].session(&rep);
    let mut written = write_when_connected(net, a, sa);
    let mut answered = false;
    let ok = net.run(t0 + 30 * SEC_NS, |n| {
        let t = n.now;
        if !written && write_when_connected(n, a, sa) {
            // As a host does after every call: send what the write made ready.
            n.pump(a);
            written = true;
        }
        if !answered && let Some((sb, id)) = n.nodes[b].read.iter().find(|(_, v)| !v.is_empty()).map(|(k, _)| *k) {
            n.nodes[b]
                .cmd(
                    t,
                    Command::Write {
                        session: sb,
                        stream: id,
                        data: b"k",
                    },
                )
                .unwrap();
            n.pump(b);
            answered = true;
        }
        n.nodes[a].read.values().any(|v| !v.is_empty())
    });
    assert!(ok, "no answer within 30 s");
    (sa, net.now - t0)
}

/// One seed: a new session, then a resumed one on the same path.
fn seed_times(seed: u64, delay: u64) -> (u64, u64) {
    let mut net = CoreNet::new(delay);
    let (a, b) = (net.add(1), net.add(2));
    net.jitter = delay * 6 / 10;
    net.rng = SplitMix64::new(seed);
    let mut drop = SplitMix64::new(seed ^ 0x5555);
    net.loss = Some(Box::new(move |_, _, _| drop.next_u64() % 100 < 5));
    let (sa, new) = first_byte(&mut net, a, b);
    let deadline = net.now + 20 * SEC_NS;
    assert!(
        net.run(deadline, |n| !n.nodes[a].ep.tickets().is_empty()),
        "seed {seed}: no ticket arrived"
    );
    let t = net.now;
    net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
    net.run_for(SEC_NS);
    let (_, resumed) = first_byte(&mut net, a, b);
    (new, resumed)
}

/// The `p`th percentile of sorted times, in microseconds.
fn pct(v: &[u64], p: usize) -> u64 {
    v[(v.len() * p / 100).min(v.len() - 1)] / 1000
}

#[test]
fn the_median_setup_takes_its_round_trips_on_a_lossy_reordering_path() {
    big_stack(|| {
        let mut failed = Vec::new();
        for delay in [100_000, 25 * MS_NS, 100 * MS_NS] {
            let (mut new, mut resumed): (Vec<u64>, Vec<u64>) = (0..SEEDS).map(|s| seed_times(s, delay)).unzip();
            // The READY hold of a dialer whose handshake round trip is under 20 ms adds one round trip.
            let new_crossings = if 2 * delay < 20 * MS_NS { 6 } else { 4 };
            for (name, v, crossings) in [("new", &mut new, new_crossings), ("resumed", &mut resumed, 2)] {
                v.sort_unstable();
                let bound = crossings * delay * 16 / 10;
                eprintln!(
                    "one-way {} us, {name}: p10 {} p25 {} median {} p75 {} p90 {} max {} us (median bound {} us)",
                    delay / 1000,
                    pct(v, 10),
                    pct(v, 25),
                    pct(v, 50),
                    pct(v, 75),
                    pct(v, 90),
                    pct(v, 100),
                    bound / 1000
                );
                if pct(v, 50) * 1000 > bound {
                    failed.push(format!("one-way {} us {name}", delay / 1000));
                }
            }
        }
        assert!(failed.is_empty(), "the median exceeds its bound: {failed:?}");
    });
}
