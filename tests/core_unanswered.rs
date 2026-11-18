//! A dial reported before its handshake (a cached allow) ends once its 4th first flight goes unanswered: a peer that
//! stopped is told within 15 first delays (7.5 s), while a running peer is reached whatever the round trip, a lost
//! flight, a held flight or a rejected ticket does to the schedule, and the node's handshake floor stays where it was. A
//! thin node keeps its 60 s handshake limit for such a dial.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

#[path = "core_timing_common.rs"]
mod common;

use std::cell::Cell;
use std::rc::Rc;

use common::{S, dial, message_type};
use vinc_core::{Command, EndReason, Event, Role, SessionId};
use vinc_tests::*;
use vinc_transport::conn::CloseReason;

fn unanswered(e: &Event) -> bool {
    matches!(
        e,
        Event::Closed {
            reason: EndReason::Transport(CloseReason::Unanswered),
            ..
        }
    )
}
fn handshake_timeout(e: &Event) -> bool {
    matches!(
        e,
        Event::Closed {
            reason: EndReason::Transport(CloseReason::HandshakeTimeout),
            ..
        }
    )
}
fn closed(e: &Event) -> bool {
    matches!(e, Event::Closed { .. })
}
fn incoming(e: &Event) -> bool {
    matches!(e, Event::Incoming { .. })
}

/// Two nodes `delay` apart one way that held a session, closed it and still have a cached allow: the next dial of `a`
/// is reported at once.
fn warm(delay: u64) -> (CoreNet, usize, usize) {
    let mut net = CoreNet::new(delay);
    let (a, b) = (net.add(1), net.add(2));
    let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
    net.run_for(S);
    let t = net.now;
    net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
    net.run_for(2 * S);
    // What follows is about the next dial only.
    net.nodes[a].events.clear();
    net.nodes[b].events.clear();
    (net, a, b)
}

/// Lose the first `n` first flights `a` sends to `b`, and count every one it sends.
fn lose_first_flights(net: &mut CoreNet, a: usize, b: usize, n: u32) -> Rc<Cell<u32>> {
    lose_flights(net, a, b, 1..=n)
}

/// Lose the first flights `a` sends to `b` whose number (from 1) is in `lost`, and count every one it sends.
fn lose_flights(net: &mut CoreNet, a: usize, b: usize, lost: core::ops::RangeInclusive<u32>) -> Rc<Cell<u32>> {
    let (from, to) = (net.nodes[a].addr, net.nodes[b].addr);
    let seen = Rc::new(Cell::new(0));
    let s = Rc::clone(&seen);
    net.loss = Some(Box::new(move |f, t, d| {
        if f != from || t != to || message_type(d).is_none() {
            return false;
        }
        s.set(s.get() + 1);
        lost.contains(&s.get())
    }));
    seen
}

/// Dial and require the early report.
fn early_dial(net: &mut CoreNet, a: usize, b: usize) -> SessionId {
    let before = net.nodes[a].count(|e| matches!(e, Event::Connected { .. }));
    let s = dial(net, a, b, ALPN_A, Role::Other);
    assert_eq!(
        net.nodes[a].count(|e| matches!(e, Event::Connected { .. })),
        before + 1,
        "not reported at dial"
    );
    s
}

#[test]
fn a_stopped_peer_ends_the_early_dial_after_four_unanswered_flights_and_the_floor_stays() {
    big_stack(|| {
        let (mut net, a, b) = warm(15 * MS_NS);
        net.loss = Some(Box::new(|_, _, _| true));
        let floor = net.nodes[a].ep.node_stats().hs_floor;
        // A host that redials a stopped peer as soon as the dial fails, three times.
        for round in 0..3 {
            let t0 = net.now;
            early_dial(&mut net, a, b);
            let seen = net.nodes[a].count(unanswered);
            assert!(
                net.run(t0 + 10 * S, |n| n.nodes[a].count(unanswered) > seen),
                "round {round}: no end by 10 s"
            );
            let at = net.nodes[a].events.iter().rev().find(|(_, e)| unanswered(e)).unwrap().0 - t0;
            // The first dial resumes: flights at 0, 0.5 and 1.5 s (the fallback to a full handshake, which restarts
            // the schedule) and 2 s; the wait after the 4th ends at 3 s. The ticket is spent, so later dials are full
            // handshakes: flights at 0, 0.5, 1.5 and 3.5 s, the end at 7.5 s.
            let bound = if round == 0 { 3_000 * MS_NS } else { 7_500 * MS_NS };
            assert!(
                at.abs_diff(bound) < 100 * MS_NS,
                "round {round}: ended at {at} ns, not {bound}"
            );
            assert_eq!(
                net.nodes[a].ep.node_stats().hs_floor,
                floor,
                "round {round}: the floor moved"
            );
        }
    });
}

#[test]
fn a_running_peer_is_reached_when_lost_flights_push_its_answer_past_the_old_bound() {
    big_stack(|| {
        // 1 s round trip, the first two flights lost (a thin node keeps its 60 s); 200 ms, the first three lost
        // (answered at 3.7 s, past the 2 s the remembered round trips gave).
        for (delay, lost) in [(500 * MS_NS, 2), (100 * MS_NS, 3)] {
            let (mut net, a, b) = warm(delay);
            let incoming_before = net.nodes[b].count(incoming);
            let seen = lose_first_flights(&mut net, a, b, lost);
            let t0 = net.now;
            early_dial(&mut net, a, b);
            assert!(
                net.run(t0 + 30 * S, |n| n.nodes[b].count(incoming) > incoming_before),
                "delay {delay}: never reached"
            );
            net.run_for(2 * S);
            assert!(seen.get() > lost, "delay {delay}: only {} flights", seen.get());
            assert!(!net.nodes[a].saw(closed), "delay {delay}: the dial closed");
        }
    });
}

#[test]
fn a_flight_held_for_ten_seconds_does_not_end_the_dial() {
    big_stack(|| {
        let (mut net, a, b) = warm(15 * MS_NS);
        let incoming_before = net.nodes[b].count(incoming);
        let cut = Rc::new(Cell::new(true));
        let c = Rc::clone(&cut);
        net.loss = Some(Box::new(move |_, _, _| c.get()));
        let s = early_dial(&mut net, a, b);
        let t = net.now;
        net.nodes[a]
            .cmd(t, Command::HoldFlight { session: s, hold: true })
            .unwrap();
        net.run_for(10 * S);
        assert!(!net.nodes[a].saw(closed), "a held dial closed");
        cut.set(false);
        let t = net.now;
        net.nodes[a]
            .cmd(
                t,
                Command::HoldFlight {
                    session: s,
                    hold: false,
                },
            )
            .unwrap();
        assert!(
            net.run(t + 5 * S, |n| n.nodes[b].count(incoming) > incoming_before),
            "never reached"
        );
        assert!(!net.nodes[a].saw(closed));
    });
}

#[test]
fn a_rejected_ticket_starts_the_count_again_and_the_restarted_peer_is_reached() {
    big_stack(|| {
        for delay in [50 * MS_NS, 150 * MS_NS] {
            let (mut net, a, b) = warm(delay);
            assert!(!net.nodes[a].ep.tickets().is_empty(), "no ticket to resume with");
            // The peer restarts on its address with the same identity and none of the tickets it issued.
            let addr = net.nodes[b].addr;
            net.nodes[b] = TNode::new(2, addr, net.now);
            // The resumed Hello reaches it and is rejected; the next three flights (the full handshake and two
            // resends) are lost. Counted from the reject, the fifth flight is the third unheard one and is answered;
            // counted from the dial, the timer would end the dial after the fourth.
            let seen = lose_flights(&mut net, a, b, 2..=4);
            let t0 = net.now;
            early_dial(&mut net, a, b);
            assert!(
                net.run(t0 + 30 * S, |n| n.nodes[b].saw(incoming)),
                "delay {delay}: the restarted peer was never reached"
            );
            net.run_for(2 * S);
            assert!(seen.get() >= 5, "delay {delay}: only {} flights", seen.get());
            assert!(!net.nodes[a].saw(closed), "delay {delay}: the dial closed");
        }
    });
}

#[test]
fn a_resumed_early_dial_tells_that_it_resumed_when_the_peer_answers() {
    big_stack(|| {
        let (mut net, a, b) = warm(50 * MS_NS);
        assert!(!net.nodes[a].ep.tickets().is_empty(), "no ticket to resume with");
        let s = early_dial(&mut net, a, b);
        assert!(
            net.run(net.now + 5 * S, |n| n.nodes[a]
                .saw(|e| matches!(e, Event::Answered { .. }))),
            "never answered"
        );
        assert!(net.nodes[a].saw(|e| matches!(e, Event::Answered { session, resumed: true } if *session == s)));
    });
}

#[test]
fn an_early_dial_whose_ticket_the_peer_refused_tells_that_it_did_not_resume() {
    big_stack(|| {
        let (mut net, a, b) = warm(50 * MS_NS);
        assert!(!net.nodes[a].ep.tickets().is_empty(), "no ticket to resume with");
        let addr = net.nodes[b].addr;
        net.nodes[b] = TNode::new(2, addr, net.now);
        let s = early_dial(&mut net, a, b);
        assert!(
            net.run(net.now + 5 * S, |n| n.nodes[a]
                .saw(|e| matches!(e, Event::Answered { .. }))),
            "never answered"
        );
        assert!(net.nodes[a].saw(|e| matches!(e, Event::Answered { session, resumed: false } if *session == s)));
    });
}

/// One first handshake that took 400 ms (a host that stalled while it ran, on a link of 30 ms) makes the node thin: its
/// next early dial to a peer that stopped is not ended after 4 unanswered flights but at a thin node's 60 s handshake
/// limit, as a handshake timeout, which raises the floor.
#[test]
fn a_node_whose_first_handshake_took_400_ms_keeps_the_thin_limit_for_an_early_dial_to_a_stopped_peer() {
    big_stack(|| {
        let mut net = CoreNet::new(200 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.delay = 15 * MS_NS;
        net.run_for(S);
        let t = net.now;
        net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(2 * S);
        let st = net.nodes[a].ep.node_stats();
        assert!(
            st.thin,
            "the node is not thin after a 400 ms handshake: lrtt {} ns",
            st.lrtt
        );
        net.nodes[a].events.clear();
        net.loss = Some(Box::new(|_, _, _| true));
        let t0 = net.now;
        early_dial(&mut net, a, b);
        assert!(
            net.run(t0 + 61 * S, |n| n.nodes[a].saw(handshake_timeout)
                || n.nodes[a].saw(unanswered)),
            "no end by 61 s"
        );
        let (at, e) = net.nodes[a]
            .events
            .iter()
            .find(|(_, e)| handshake_timeout(e) || unanswered(e))
            .unwrap();
        let at = *at - t0;
        assert!(
            handshake_timeout(e),
            "ended as unanswered at {at} ns, not at the thin node's 60 s limit"
        );
        assert!(
            at.abs_diff(60 * S) < 100 * MS_NS,
            "ended at {at} ns, not at the 60 s limit"
        );
        assert_eq!(
            net.nodes[a].ep.node_stats().hs_floor,
            500 * MS_NS,
            "the floor did not rise"
        );
    });
}
