//! The amplification ledger and an honest peer: a peer that moves pays the wait for the evidence that validates its new
//! address and nothing more. The connection is told the room the ledger leaves a held address, so nothing it counts
//! as sent is held back at the gate (it would be declared lost and the window would shrink), and the challenge that
//! brings the evidence leaves at once.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::net::SocketAddr;

use vinc_core::{Answer, Command, LedgerEntry, Query, Role, SessionId};
use vinc_tests::*;

fn ledger_of(net: &mut CoreNet, node: usize, a: SocketAddr) -> Option<LedgerEntry> {
    match net.nodes[node].ep.query(Query::Ledger(a)) {
        Answer::Ledger(e) => Some(e),
        _ => None,
    }
}

/// Open a stream on `session` of `node` and write what it takes of `data`. Returns the stream and the bytes taken.
fn open_and_write(net: &mut CoreNet, node: usize, session: SessionId, data: &[u8]) -> (u64, usize) {
    let now = net.now;
    let Ok(vinc_core::Value::Stream(stream)) = net.nodes[node]
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
        Ok(vinc_core::Value::Written(n)) => n,
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
