//! The handshake-end runs of the timers trace: a dialing side whose Finish never arrived, and a dial nobody answers.

use pinc_crypto::IdentityAlg;
use pinc_security::ClientTickets;
use pinc_tests::*;

use crate::duo::{app, close, init, poll, take_over, timeout};
use crate::rec::Log;

/// A dialing side whose Finish never reached the responder (#390): A holds the session, connected and unconfirmed, B
/// still waits in its handshake, and nothing either writes arrives. B's handshake runs out, and A ends the session as
/// unconfirmed, silently, at the first timer call past the connect limit counted from when it established (30 s, 60 s
/// on a thin node), not a microsecond earlier. With `turn`, A's node becomes thin (or not) that long after A
/// established: the limit is the new one, still counted from the establishment, so one already past ends the session
/// at the next timer call.
pub fn unconfirmed_run(log: &mut Log, seed: u64, thin: bool, turn: Option<(u64, bool)>) {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.thin = thin;
    w.seed = seed as u8;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    net.drop_finish = true;
    assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.is_connected()));
    assert!(!net.b.conn.is_connected(), "the responder took the Finish");
    take_over(net, |d| {
        // A established at its last activity: nothing of B was heard after the reply.
        let est = d.nodes[0].conn.trace_timers().last_activity;
        assert!(!d.nodes[0].conn.trace_timers().confirmed);
        d.init(log);
        let limit = |thin: bool| if thin { 60 * SEC } else { 30 * SEC };
        let (mut kind, mut turn, mut turned) = (thin, turn, None);
        let mut ends: [Option<(u64, &'static str)>; 2] = [None, None];
        for _ in 0..4000 {
            for n in 0..2 {
                d.tx(log, n);
            }
            d.lose_all();
            let Some(next) = d.next_deadline() else { break };
            if let Some((after, to)) = turn
                && next >= est + after
            {
                // A's node changes its kind before A's next timer.
                d.now = d.now.max((est + after).div_ceil(1000) * 1000);
                d.nodes[0].conn.set_node_rtt(0, 0, to);
                (kind, turn, turned) = (to, None, Some(d.now));
                continue;
            }
            // The first whole microsecond at or past the end: the connect limit is exceeded, not reached.
            let at = (est + limit(kind) + 1).div_ceil(1000) * 1000;
            if ends[0].is_none() && next.div_ceil(1000) * 1000 >= at && at >= d.now + 1000 {
                // a microsecond before it, A still holds the session
                d.now = at - 1000;
                d.poll(log, 0);
                let ev = d.timeout(log, 0);
                assert!(
                    ev.is_empty() && !d.nodes[0].conn.is_closed(),
                    "unconfirmed before the limit: {ev:?}"
                );
            }
            d.now = d.now.max(next.div_ceil(1000) * 1000);
            for n in 0..2 {
                if d.poll(log, n).is_some_and(|t| t <= d.now) {
                    let ev = d.timeout(log, n);
                    if let Some(&e) = ev.iter().find(|e| ["unconf", "hs", "idle", "dead"].contains(*e)) {
                        ends[n] = Some((d.now, e));
                    }
                }
            }
        }
        let at = (est + limit(kind) + 1).div_ceil(1000) * 1000;
        assert_eq!(
            ends[0],
            Some((at.max(turned.unwrap_or(0)), "unconf")),
            "the dialing side ends unconfirmed at its limit"
        );
        assert_eq!(ends[1].map(|e| e.1), Some("hs"), "the responder's handshake runs out");
        assert_eq!(log.closes, [0, 0], "an unconfirmed session ended with a CLOSE");
        for n in 0..2 {
            assert!(d.poll(log, n).is_none());
            assert_eq!(d.tx(log, n), 0);
            app(log, n, &mut d.nodes[n], d.now, 10);
        }
    });
}

/// A dial nobody answers: its handshake retransmits, then gives up; or the application closes it first.
pub fn dial_run(log: &mut Log, seed: u64, close_at: Option<u64>) {
    let w = World::new(IdentityAlg::Ed25519);
    let mut sa = Store::new(true);
    let mut node = w.client(&mut sa, None, ClientTickets::new());
    let mut now = T0;
    init(log, 0, &mut node, now);
    let mut buf = vec![0u8; 65_536];
    let mut rng = SplitMix64::new(seed);
    for _ in 0..400 {
        if let Some(c) = close_at
            && now >= T0 + c
            && !node.conn.is_closed()
        {
            close(log, 0, &mut node, now, 9);
        }
        loop {
            let r = node.with_env(now, |c, env| c.poll_transmit(env, &mut buf));
            let len = r.map_or(0, |t| t.len);
            log.line(0, &mut node, now, "tx", &format!(r#","len":{len}"#));
            if r.is_none() {
                break;
            }
        }
        let Some(t) = poll(log, 0, &mut node, now) else { break };
        // sometimes a timer call before the deadline
        if rng.next_u64().is_multiple_of(4) && t.div_ceil(1000) * 1000 > now + 1000 {
            let at = t.div_ceil(1000) * 1000 - 1000;
            let ev = timeout(log, 0, &mut node, at);
            assert_eq!(ev, Vec::<&str>::new(), "a timer call before the deadline did something");
            now = at;
        }
        now = now.max(t.div_ceil(1000) * 1000);
        timeout(log, 0, &mut node, now);
    }
    assert!(node.conn.is_closed());
}
