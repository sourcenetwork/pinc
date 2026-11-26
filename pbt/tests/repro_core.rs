//! Reproducing tests of bugs the `core_*` properties found in `pinc-core`. Each fails on the unmodified code.

mod core_harness;

use std::net::SocketAddr;

use core_harness::{ALPN_A, HostCfg, MS, Net, SEC, big_stack};
use pinc_core::{Answer, Command, Query, Value};

/// An established pair (host 0 dialed host 1) where host 1 wrote `len` bytes to host 0 on a fresh stream; the net
/// keeps every datagram, and is stopped before the last of them arrived.
fn pair_with_traffic(len: usize) -> (Net, usize, usize, usize) {
    let mut net = Net::new(0);
    let (a, b) = (net.add(1, HostCfg::default()), net.add(2, HostCfg::default()));
    let (_, sb) = net.connect_pair(a, b, ALPN_A).expect("the pair connects");
    net.run_for(300 * MS);
    let now = net.now;
    let Ok(core_harness::Reply2 { value: Value::Stream(st) }) =
        net.hosts[b].cmd(now, Command::OpenStream { session: sb, bidi: true })
    else {
        panic!("no stream")
    };
    let first = net.captured.len();
    net.hosts[b].write(now, sb, st, vec![7; len], true);
    net.pump_all();
    (net, a, b, first)
}

/// What host `h` sent to `x` and received from it on the wire (28 bytes of headers a datagram, as the ledger
/// counts), and the ledger entry of `x`.
fn wire_to(net: &Net, h: usize, x: SocketAddr) -> (u64, u64, Option<pinc_core::LedgerEntry>) {
    let sent = net.sent_to.get(&(h, x)).copied().unwrap_or(0);
    let got = net.got_from.get(&(h, x)).copied().unwrap_or(0);
    let entry = match net.hosts[h].ep.query(Query::Ledger(x)) {
        Answer::Ledger(e) => Some(e),
        _ => None,
    };
    (sent, got, entry)
}

/// The amplification bound is lifted for an address that never answered: the ledger counts any second datagram from
/// an address it sent to as "an answer", so a third party that forwards one datagram of a session from a forged
/// address before the original arrives, and then one more byte from it, makes the endpoint send that address several times what it sent.
///
/// Expected (pinc-core `ledger.rs`): "An address that wrote to us first is held to three times the bytes it sent
/// until it answers something we sent it ... for an address that is not validated the bytes charged never exceed
/// three times the bytes received, so a spoofed source gets at most three times what it sent." The forged address
/// never received anything, so it cannot have answered.
///
/// Actual: the copy makes host 0 probe the new address (small datagrams, within three times), the byte that follows
/// sets the entry to `validated: true`, and host 0 then sends the address a full-size datagram (about 1.45 kB): the
/// property's shrunk case sent 1601 bytes for 105 received (EPHYRA_REPLAY=15910191858001922372:11 of
/// `a_flood_from_a_third_party_bounds_every_table_and_leaves_the_session_intact`).
///
/// Suspected fault: `Ledger::on_receive` (crates/pinc-core/src/ledger.rs:72) sets `validated` on any datagram
/// received after a send (`if e.tx > 0`), before anything says the datagram answers what was sent; the endpoint calls
/// it first thing in `handle_datagram` (rx.rs:131), for every datagram, decryptable or not.
///
/// Who: an unauthenticated remote that sees one datagram of a session on its way (on the path, or a tap beside it)
/// and can send from any address. Once the entry of a victim address is validated this way, nothing bounds what the
/// endpoint sends there: a reflector toward the victim.
#[test]
fn a_replayed_short_packet_from_a_forged_address_is_answered_beyond_three_times() {
    big_stack(|| {
        let x: SocketAddr = "192.0.2.1:7000".parse().unwrap();
        let (mut net, a, b, first) = pair_with_traffic(1419);
        let (to, from_b) = (net.hosts[a].addr, net.hosts[b].addr);
        // The shortest datagram of host 1's session still on its way: a copy of it reaches host 0 first, from `x`.
        let d = net.captured[first..]
            .iter()
            .filter(|(f, t, _)| *f == from_b && *t == to)
            .min_by_key(|c| c.2.len())
            .map(|c| c.2.clone())
            .expect("host 1 sent to host 0");
        net.deliver(x, to, d.clone());
        net.pump_all();
        // One more byte from the same forged address.
        net.deliver(x, to, vec![0]);
        net.pump_all();
        net.run_for(2 * SEC);
        let (sent, got, entry) = wire_to(&net, a, x);
        eprintln!("forwarded {} bytes and one: sent {sent}, got {got}, ledger {entry:?}", d.len());
        assert!(sent <= 3 * got, "host 0 sent {sent} bytes to a forged address that sent {got}");
    });
}
