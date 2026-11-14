//! The access gate after a deny and after a lapse: no application event of a session reaches the host once the
//! peer's answer was a deny, nor while its answer has lapsed and no fresh allow came.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

use vinc_core::{Command, CommandError, Event, Role, SessionId, Value};
use vinc_tests::*;

const SLOW: u64 = 15 * MS_NS;

fn is_data(e: &Event) -> bool {
    matches!(e, Event::StreamOpened { .. } | Event::StreamReadable { .. })
}

/// Opens a unidirectional stream on `n`'s session `s` and writes `data` to it.
fn write_once(net: &mut CoreNet, n: usize, s: SessionId, data: &[u8]) {
    let t = net.now;
    let Value::Stream(id) = net.nodes[n]
        .cmd(
            t,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!()
    };
    net.nodes[n]
        .cmd(
            t,
            Command::Write {
                session: s,
                stream: id,
                data,
            },
        )
        .unwrap();
}

/// Every datagram node `n` has to send at `now`, taken off the endpoint directly.
fn transmits(net: &mut CoreNet, n: usize, now: u64) -> Vec<Vec<u8>> {
    let mut buf = vec![0u8; 65_536];
    let mut out = Vec::new();
    while let Some(tx) = net.nodes[n].ep.poll_transmit(now, &mut buf) {
        for c in buf[..tx.len].chunks(tx.segment_size) {
            out.push(c.to_vec());
        }
    }
    out
}

/// Fill the host's event queue without reading it (as `core_acp.rs` does).
fn stall_events(ep: &mut CoreEp, now: u64) {
    let me = ep.identity().node_id();
    for _ in 0..10_000 {
        match ep.command(
            now,
            Command::Connect {
                node: me,
                alpn: ALPN_A,
                addrs: &[],
                role: Role::Other,
            },
        ) {
            Err(CommandError::Refused) => {}
            Err(CommandError::EventsPending) => return,
            other => panic!("unexpected {other:?}"),
        }
    }
    panic!("the queue never stalled");
}

#[test]
fn a_dial_denied_on_its_recheck_delivers_nothing_after_the_deny() {
    big_stack(|| {
        let mut net = CoreNet::new(SLOW);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.nodes[a].acp = Acp::Manual;
        // 5 s before the cached allow runs out the dialer asks its application again.
        let t0 = net.now;
        assert!(net.run(t0 + 30 * SEC_NS, |n| !n.nodes[a].checks.is_empty()));
        let (check, _) = net.nodes[a].checks[0];
        let t = net.now;
        // The application denies the peer.
        let rep = net.nodes[a]
            .ep
            .command(t, Command::AcpAnswer { check, allow: false })
            .unwrap();
        let mut after: Vec<Event> = rep.events.iter().copied().collect();
        // The peer writes; its datagrams reach the dialer before the dialer's host next calls `poll_transmit`
        // (a host that reads a batch of datagrams from its socket before it sends).
        write_once(&mut net, b, sb, b"after the deny");
        let dgrams = transmits(&mut net, b, t);
        assert_ne!(dgrams.len(), 0, "nothing to send");
        let (to, from) = (net.nodes[a].addr, net.nodes[b].addr);
        for mut d in dgrams {
            net.nodes[a].ep.handle_datagram(t + SLOW, to, from, &mut d);
        }
        while let Some(e) = net.nodes[a].ep.poll_event() {
            after.push(e);
        }
        let leaked: Vec<&Event> = after.iter().filter(|e| e.session() == Some(sa) && is_data(e)).collect();
        assert!(
            leaked.is_empty(),
            "application events after the deny: {leaked:?}\nall events after the deny: {after:?}"
        );
    });
}

#[test]
fn a_parked_session_releases_nothing_held_on_a_lapsed_answer_before_a_fresh_allow() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        net.nodes[b].acp = Acp::Manual;
        // The host did not run the endpoints for a minute: the cached answer of 30 s lapsed.
        net.now += 60 * SEC_NS;
        let t0 = net.now;
        write_once(&mut net, a, sa, b"late");
        net.run_for(SEC_NS);
        assert!(!net.nodes[b].checks.is_empty(), "no new check was raised");
        assert!(
            !net.nodes[b]
                .events
                .iter()
                .any(|(at, e)| *at >= t0 && e.session() == Some(sb) && is_data(e)),
            "data reached the application on a lapsed answer"
        );
        // The host leaves its events unread until the queue is near full; a datagram for the session then arrives
        // (the endpoint parks the session, as it does for any input while the queue is near full).
        let t = net.now;
        stall_events(&mut net.nodes[b].ep, t);
        write_once(&mut net, a, sa, b"more");
        let dgrams = transmits(&mut net, a, t);
        assert_ne!(dgrams.len(), 0, "nothing to send");
        let (to, from) = (net.nodes[b].addr, net.nodes[a].addr);
        for mut d in dgrams {
            net.nodes[b].ep.handle_datagram(t + 5 * MS_NS, to, from, &mut d);
        }
        // The host reads its events; the check is still unanswered.
        let mut got = Vec::new();
        while let Some(e) = net.nodes[b].ep.poll_event() {
            got.push(e);
        }
        let leaked: Vec<&Event> = got.iter().filter(|e| e.session() == Some(sb) && is_data(e)).collect();
        assert!(
            leaked.is_empty(),
            "application events left on a lapsed answer before any fresh allow: {leaked:?}"
        );
    });
}
