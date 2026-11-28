//! The punches a peer's `REACH_OUT` starts: a peer that sends `REACH_OUT` after `REACH_OUT` starts one punch round per
//! session per [`UPGRADE_INTERVAL`] (the cadence of the layer's own rounds), so it cannot keep the challenge budget of
//! the end's paths (`Paths::back_left`) full by naming candidates round after round. The pair sits behind symmetric
//! translators, where no punch succeeds and only the budget ends a round.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

mod connect_sim_common;

use std::net::SocketAddr;

use connect_sim_common::*;
use pinc_connect::client::punch::{PROBES, UPGRADE_INTERVAL, encode};
use pinc_connect::record::MAX_ADDRS;
use pinc_sim::{NatKind, NodeId, SEC, Time};
use pinc_tests::Cmd;

/// A and B behind symmetric translators, connected through the relays at 9 s.
fn connected(seed: u64) -> (World, NodeId, NodeId) {
    let mut w = World::new(seed);
    let (_r1, r1) = w.relay(1, relay_ip(10));
    let (_r2, r2) = w.relay(2, relay_ip(20));
    let na = w.nat(NatKind::Symmetric, ext(1), 120 * SEC, 7200 * SEC);
    let nb = w.nat(NatKind::Symmetric, ext(2), 120 * SEC, 7200 * SEC);
    let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[r1, r2]), na);
    let b = w.client_behind(&client_spec(0xb1, priv_addr(2), &[r1, r2]), nb);
    w.run(secs(6));
    w.dial(secs(6), a, b, vec![]);
    w.run(secs(11));
    (w, a, b)
}

/// Eight candidates nobody answers from, the set `k` of them.
fn cands(k: u8) -> Vec<SocketAddr> {
    (0..MAX_ADDRS as u8)
        .map(|i| ([198, 51, 100 + k, 1 + i], 9000).into())
        .collect()
}

fn reach_out(w: &mut World, at: Time, from: NodeId, session: pinc_core::SessionId, to: &[SocketAddr]) {
    let mut body = [0u8; pinc_core::REACH_BODY_MAX];
    let n = encode(to, &mut body).expect("candidates encode");
    w.sim.command(
        at,
        from,
        Cmd::ReachOut {
            session,
            body: body[..n].to_vec(),
        },
    );
}

/// Datagrams node `n` sent to any of `to` in `[from, until)`.
fn sent_to(w: &World, n: NodeId, to: &[SocketAddr], from: Time, until: Time) -> usize {
    w.client(n)
        .tx_log
        .iter()
        .filter(|(t, r, _)| (from..until).contains(t) && to.contains(r))
        .count()
}

/// One `REACH_OUT` per second for 60 s, each naming the same eight candidates: one round starts, nine probes to each,
/// and nothing more for the minute. Without the limit each frame starts a round and the count is a multiple of that.
#[test]
fn a_peer_that_sends_reach_out_after_reach_out_starts_one_round_per_cadence() {
    big(|| {
        let (mut w, a, b) = connected(31);
        let sb = w.incoming(b).expect("b has the session");
        let set = cands(0);
        let t0 = secs(12);
        for k in 0..60 {
            reach_out(&mut w, t0 + k * SEC, b, sb, &set);
        }
        w.run(t0 + 100 * SEC);
        let n = sent_to(&w, a, &set, t0, t0 + 100 * SEC);
        eprintln!("datagrams to the named candidates in 100 s: {n}");
        assert!(n > 0, "the first REACH_OUT started no round");
        assert!(
            n <= MAX_ADDRS * PROBES as usize,
            "more than one round of {PROBES} probes to {MAX_ADDRS} candidates: {n}"
        );
    });
}

/// A second `REACH_OUT` after the cadence starts its round: a peer that moved, or a legitimate next round, is not starved.
#[test]
fn a_reach_out_after_the_cadence_starts_a_round() {
    big(|| {
        let (mut w, a, b) = connected(32);
        let sb = w.incoming(b).expect("b has the session");
        let (first, second) = (cands(0), cands(1));
        let t0 = secs(12);
        let t1 = t0 + UPGRADE_INTERVAL + SEC;
        reach_out(&mut w, t0, b, sb, &first);
        reach_out(&mut w, t0 + SEC, b, sb, &second);
        reach_out(&mut w, t1, b, sb, &second);
        w.run(t1 + 30 * SEC);
        assert_eq!(
            sent_to(&w, a, &second, t0, t1 - SEC),
            0,
            "a REACH_OUT inside the cadence started a round"
        );
        let n = sent_to(&w, a, &second, t1, t1 + 30 * SEC);
        assert!(n > 0, "the REACH_OUT after the cadence started no round");
        assert!(n <= MAX_ADDRS * PROBES as usize, "more than one round: {n}");
    });
}
