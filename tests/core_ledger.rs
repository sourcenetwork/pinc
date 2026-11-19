//! The amplification ledger and an honest peer: a peer that moves pays the wait for the evidence that validates its new
//! address and nothing more. The connection is told which of its paths the ledger holds and offers no size probe on
//! one, so the probe the gate would refuse is never built, and the size probe goes once the address has answered.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::cell::Cell;
use std::net::SocketAddr;
use std::rc::Rc;

use pinc_core::{Answer, Command, LedgerEntry, Query, Role, SessionId};
use pinc_tests::*;

fn ledger_of(net: &mut CoreNet, node: usize, a: SocketAddr) -> Option<LedgerEntry> {
    match net.nodes[node].ep.query(Query::Ledger(a)) {
        Answer::Ledger(e) => Some(e),
        _ => None,
    }
}

/// Open a stream on `session` of `node` and write what it takes of `data`. Returns the stream and the bytes taken.
fn open_and_write(net: &mut CoreNet, node: usize, session: SessionId, data: &[u8]) -> (u64, usize) {
    let now = net.now;
    let Ok(pinc_core::Value::Stream(stream)) = net.nodes[node]
        .cmd(now, Command::OpenStream { session, bidi: true })
        .map(|r| r.value)
    else {
        panic!("no stream")
    };
    (stream, write_more(net, node, session, stream, data))
}

/// Write what the stream takes of `data` and let the node send it. Returns the bytes taken.
fn write_more(net: &mut CoreNet, node: usize, session: SessionId, stream: u64, data: &[u8]) -> usize {
    let now = net.now;
    let taken = match net.nodes[node]
        .cmd(now, Command::Write { session, stream, data })
        .map(|r| r.value)
    {
        Ok(pinc_core::Value::Written(n)) => n,
        other => panic!("write refused: {other:?}"),
    };
    net.pump(node);
    taken
}

/// What a transfer from the server to a client that moves in its middle cost.
struct Moved {
    /// From the server's write to the client holding every byte.
    took: u64,
    /// Datagrams the server's ledger held back during the transfer.
    held: u64,
    /// The server's ledger entry of the client's new address at the end.
    entry: Option<LedgerEntry>,
    /// The datagram size of the server's session two seconds after the transfer (its size probe has had its time).
    mtu: u16,
}

/// The server (node 0) writes `size` bytes to its client (node 1) over 5 ms one way. When `moved`, the client's address
/// changes 30 ms into the transfer (a NAT that rebinds) and the client then writes a few bytes, which the server
/// follows to the new address.
fn transfer(moved: bool, size: usize) -> Moved {
    let mut net = CoreNet::new(5 * MS_NS);
    let (s, c) = (net.add(1), net.add(2));
    let (sa, sb) = net.connect_pair(c, s, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let outside: SocketAddr = "10.7.7.7:5555".parse().unwrap();
    let held0 = net.nodes[s].ep.node_stats().held_by_ledger;
    let t0 = net.now;
    let payload = vec![5u8; size];
    let (stream, mut sent) = open_and_write(&mut net, s, sb, &payload);
    let mut moved_at = None;
    let done = net.run(t0 + 30 * SEC_NS, |n| {
        if sent < size {
            sent += write_more(n, s, sb, stream, &payload[sent..]);
        }
        if moved && moved_at.is_none() && n.now >= t0 + 30 * MS_NS {
            moved_at = Some(n.now);
            n.nat = Some((n.nodes[c].addr, outside));
            open_and_write(n, c, sa, &[1u8; 40]);
        }
        n.nodes[c].read.values().any(|v| v.len() >= size)
    });
    assert!(done, "moved {moved}: the transfer did not end within 30 s");
    let took = net.now - t0;
    let held = net.nodes[s].ep.node_stats().held_by_ledger - held0;
    net.run_for(2 * SEC_NS);
    let Answer::Stats(st) = net.nodes[s].ep.query(Query::Stats(sb)) else {
        panic!("no stats")
    };
    Moved {
        took,
        held,
        entry: ledger_of(&mut net, s, outside),
        mtu: st.transport.mtu,
    }
}

#[test]
fn a_client_that_moves_mid_transfer_costs_its_server_nothing_held_and_only_the_wait_for_its_challenge() {
    big_stack(|| {
        let size = 300_000;
        let home = transfer(false, size);
        let moved = transfer(true, size);
        eprintln!(
            "transfer of {size} bytes: home {} ms held {}; moved {} ms held {} entry {:?}",
            home.took / MS_NS,
            home.held,
            moved.took / MS_NS,
            moved.held,
            moved.entry
        );
        assert_eq!(home.held, 0, "nothing is held for a client at its address");
        assert_eq!(
            moved.held, 0,
            "the ledger held back datagrams the server counted as sent to the client's new address"
        );
        assert!(
            moved.entry.is_some_and(|e| e.validated),
            "the challenge to the new address was never answered: {:?}",
            moved.entry
        );
        // What the move costs is the recovery of what the server had in flight to the old address, which nobody
        // answers: the client's challenge answer takes one round trip (10 ms on this link), then the probe timer
        // fires twice and the loss that follows is found one probe timeout after the second. A probe timeout is the
        // smoothed round trip, 1 ms of variance floor and the 25 ms the receiver may hold an acknowledgement. A size
        // probe sent in that wait would be acknowledged alone, 25 ms late, and stretch every one of those timeouts.
        let rtt = 10 * MS_NS;
        let pto = rtt + MS_NS + 25 * MS_NS;
        assert!(
            moved.took <= home.took + rtt + 3 * pto,
            "the move cost {} ms over the {} ms of the transfer at home; the bound is {} ms",
            (moved.took - home.took) / MS_NS,
            home.took / MS_NS,
            (rtt + 3 * pto) / MS_NS
        );
    });
}

#[test]
fn a_client_that_moves_mid_transfer_gets_its_size_probe_on_the_new_path() {
    big_stack(|| {
        let size = 300_000;
        let home = transfer(false, size);
        let moved = transfer(true, size);
        assert_eq!(home.mtu, 1452, "the session at home settles at the probed size");
        assert_eq!(
            moved.mtu, 1452,
            "the session on the new address stays at the minimum size: its probe was refused or never sent"
        );
    });
}

#[test]
fn the_ledger_refuses_what_a_server_builds_past_three_times_what_a_moved_client_sent_and_counts_it() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (s, c) = (net.add(1), net.add(2));
        let (sa, sb) = net.connect_pair(c, s, ALPN_A, Role::Other);
        net.run_for(SEC_NS);
        let outside: SocketAddr = "10.7.7.7:5555".parse().unwrap();
        let (inside, server) = (net.nodes[c].addr, net.nodes[s].addr);
        // Only the first datagram the client sends after it moved reaches the server, until `open` is set.
        let (sent, open) = (Rc::new(Cell::new(0u32)), Rc::new(Cell::new(false)));
        let (count, opened) = (sent.clone(), open.clone());
        net.loss = Some(Box::new(move |from, _, _| {
            if from != inside || opened.get() {
                return false;
            }
            count.set(count.get() + 1);
            count.get() > 1
        }));
        net.nat = Some((inside, outside));
        let out0 = net.nodes[s].ep.node_stats().datagrams_out;
        let held0 = net.nodes[s].ep.node_stats().held_by_ledger;
        let tapped0 = net.tapped.len();
        open_and_write(&mut net, c, sa, &[1u8; 40]);
        assert!(
            net.run(net.now + SEC_NS, |w| ledger_of(w, s, outside).is_some()),
            "the server never heard the move"
        );
        // The server has a lot to send, and the only evidence of the new address is that one small datagram.
        let size = 300_000;
        let payload = vec![5u8; size];
        let (stream, mut written) = open_and_write(&mut net, s, sb, &payload);
        net.run(net.now + 2 * SEC_NS, |w| {
            written += write_more(w, s, sb, stream, &payload[written..]);
            false
        });
        let Some(e) = ledger_of(&mut net, s, outside) else {
            panic!("no entry")
        };
        assert!(!e.validated, "the address validated without an answer: {e:?}");
        let ns = net.nodes[s].ep.node_stats();
        let left = net.tapped[tapped0..].iter().filter(|t| t.1 == server).count() as u64;
        let to_new: u64 = net.tapped[tapped0..]
            .iter()
            .filter(|t| t.2 == outside)
            .map(|t| t.3 as u64 + 28)
            .sum();
        assert!(ns.held_by_ledger > held0, "the ledger refused nothing: {e:?}");
        assert_eq!(ns.datagrams_out - out0, left, "a refused datagram never counts as out");
        assert_eq!(to_new, e.tx, "every datagram that left was charged");
        assert!(e.tx <= 3 * e.rx, "charged {} for {} received", e.tx, e.rx);
        // The client answers: the address validates and the rest goes.
        open.set(true);
        let done = net.run(net.now + 30 * SEC_NS, |w| {
            if written < size {
                written += write_more(w, s, sb, stream, &payload[written..]);
            }
            w.nodes[c].read.values().any(|v| v.len() >= size)
        });
        assert!(done, "the transfer did not complete once the client answered");
    });
}
