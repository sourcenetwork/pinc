//! Trace generation for the resends of the Finish of a dialing connection: real dialers over the harness link
//! (`trace_finish`), recorded as ndjson (`finish_resend.ndjson`) for the TLA+ trace check (`TraceFinishResend.tla`).
//!
//! A run dials over a link with a one-way delay of 1 ms to 2 s, for an ordinary node, a node thin by its flag, a node
//! thin by a slow round trip and an ordinary node with a long round trip on record, after 0, 1 or 3 lost first
//! flights. When the Finish has gone out the run stops using the link: the dialer is driven alone, its timer called
//! at each deadline it names, with nothing delivered, so that every resend of the Finish is the timer's own. An `est`
//! event records the state when the Finish went out and a `fire` event each resend, with the wait to the next.
//!
//! The test asserts, without the model: every run reaches `est` and fires at least once, the first wait is at most
//! 999 ms and at most the probe timeout, waits never shrink, an ordinary node never waits over 2 s, a thin node waits
//! at least the least of 20 s and twice its round trip, and the runs cover a probe timeout above and below 999 ms.
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names
)]

use std::fmt::Write as _;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{FinishView, PathId};

const MAX_CALLS: usize = 100_000;

/// A time in microseconds, for the trace.
fn us(ns: u64) -> u64 {
    assert_eq!(ns % 1000, 0, "a time of {ns} ns is not a whole number of microseconds");
    assert!(ns / 1000 < 1 << 31, "a time of {ns} ns does not fit");
    ns / 1000
}

#[derive(Default)]
struct Seen {
    long_pto: bool,
    short_pto: bool,
}

/// One run; returns its trace lines.
fn run_case(seed: u64, delay_ms: u64, kind: u64, lost: u32, seen: &mut Seen) -> String {
    let mut out = String::new();
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.flight_split = false;
    w.cfg.probe_mtu = false;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut a = w.client(&mut sa, None, pinc_security::ClientTickets::new());
    let b = w.server(&mut sb);
    match kind {
        1 => a.conn.set_node_rtt(0, 0, true),
        2 => a.conn.set_node_rtt(400 * MS, 300 * MS, false),
        3 => a.conn.set_node_rtt(200 * MS, 100 * MS, false),
        _ => {}
    }
    let mut net = Net::new(a, b, Link::new(seed, Params::new(delay_ms * MS)), &mut w.stores);
    net.link.route(PathId(1)).ab.drop_next(lost);
    let out_view = |n: &Net<'_, '_>| n.a.conn.trace_finish();
    let sent = net.run(net.now + 600 * SEC, |n| {
        let v = n.a.conn.trace_finish();
        v.finish && v.retx_at.is_some()
    });
    assert!(sent, "the Finish never went out (seed {seed})");
    let now0 = net.now;
    let v0 = out_view(&net);
    let wait0 = v0.retx_at.unwrap() - now0;
    assert_eq!(
        wait0, v0.first,
        "the first wait is not the first wait of the view (seed {seed})"
    );
    writeln!(
        out,
        r#"{{"t":"est","pto":{},"rtt":{},"thin":{},"sends":{},"wait":{}}}"#,
        us(v0.pto),
        us(v0.rtt),
        u8::from(v0.thin),
        v0.sends,
        us(wait0)
    )
    .unwrap();
    assert!(
        wait0 <= 999 * MS && wait0 <= v0.pto,
        "the first wait {wait0} passes 999 ms or the timeout {}",
        v0.pto
    );
    seen.long_pto |= v0.pto > 999 * MS;
    seen.short_pto |= v0.pto < 999 * MS && wait0 == v0.pto;

    let mut waits = vec![wait0];
    let mut view: FinishView = v0;
    let mut buf = vec![0u8; 65536];
    let mut at = now0;
    for _ in 0..MAX_CALLS {
        let Some(t) = net.a.conn.poll_timeout() else { break };
        if t > now0 + 120 * SEC || !view.finish {
            break;
        }
        at = at.max(t);
        net.a.with_env(at, |c, env| {
            c.handle_timeout(env);
            for _ in 0..64 {
                if c.poll_transmit(env, &mut buf).is_none() {
                    break;
                }
            }
        });
        let after = net.a.conn.trace_finish();
        assert!(
            after.sends <= view.sends + 1,
            "a timer call raised the sends by more than one (seed {seed})"
        );
        if after.sends == view.sends + 1 && after.finish {
            let wait = after.retx_at.unwrap() - at;
            writeln!(
                out,
                r#"{{"t":"fire","sent":{},"first":{},"thin":{},"rtt":{},"wait":{}}}"#,
                view.sends,
                us(after.first),
                u8::from(after.thin),
                us(after.rtt),
                us(wait)
            )
            .unwrap();
            assert!(
                after.thin || wait <= 2 * SEC,
                "an ordinary node waited {wait} ns (seed {seed})"
            );
            assert!(
                !after.thin || wait >= (20 * SEC).min(2 * after.rtt),
                "a thin node waited {wait} ns for a round trip of {} (seed {seed})",
                after.rtt
            );
            waits.push(wait);
        }
        view = after;
    }
    assert!(waits.len() > 1, "no resend of the Finish (seed {seed})");
    assert!(
        waits.windows(2).all(|p| p[0] <= p[1]),
        "the waits shrank: {waits:?} (seed {seed})"
    );
    out
}

#[test]
fn finish_resend_traces() {
    let out = big_stack(|| {
        let mut out = String::new();
        let mut seen = Seen::default();
        let mut seed = 0;
        for d in [1u64, 10, 40, 150, 400, 1500] {
            for kind in 0..4 {
                for lost in [0u32, 1, 3] {
                    out += &run_case(seed, d, kind, lost, &mut seen);
                    seed += 1;
                }
            }
        }
        for s in 0..24u64 {
            let mut rng = SplitMix64::new(s);
            let d = 1 + rng.next_u64() % 2000;
            let kind = rng.next_u64() % 4;
            let lost = (rng.next_u64() % 4) as u32;
            out += &run_case(seed, d, kind, lost, &mut seen);
            seed += 1;
        }
        assert!(seen.long_pto, "no run with a probe timeout over 999 ms");
        assert!(
            seen.short_pto,
            "no run with a probe timeout under 999 ms and a first wait equal to it"
        );
        out
    });
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("finish_resend.ndjson"), out).unwrap();
    }
}
