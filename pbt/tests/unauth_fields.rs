//! `pinc-core` and `pinc-transport`: a field a responder acts on before its handshake message authenticated, changed
//! alone in an otherwise genuine datagram. Read from crates/pinc-transport/src/conn/recv.rs (`on_handshake`): a
//! responder still in its handshake sets the peer's first id from the source id of every handshake packet that names
//! its ids (`cids.set_first_remote(header.scid)`, recv.rs:272), before the message the packet carries a part of opened.
//! The other fields of that list are covered elsewhere: the path (`core_parts`, `repro_core2.rs` A and C), the length
//! and offset of a fragment (`repro_core2.rs` D), the client's believing the source id of the Reply
//! (`repro_transport_link.rs`, known).
//!
//! Expected: recv.rs:9-11, "nothing is acted on before it authenticated", and the property's rule from
//! `core_parts.rs`: the datagram is dropped, and the session goes on as if it never arrived, so the honest handshake
//! completes within the 30 s connect limit (`CONNECT_TIMEOUT`) on a link that is lossy for a while and then clean.

mod core_harness;

use core_harness::{ALPN_A, HostCfg, MS, Net, SEC, big_stack};
use ephyra::{check_generator, gens};
use pinc_core::{Command, Event, Role, Value};
use pinc_transport::packet::{LongHeader, LongType};

/// A copy of the client's handshake datagrams with one byte of the source id changed, from the client's address.
#[derive(Clone, Debug, PartialEq, Eq, ephyra::Arbitrary)]
struct UCase {
    seed: u64,
    split: bool,
    #[ephyra(gen = gens::int(1u64..=40))]
    delay_ms: u64,
    #[ephyra(gen = gens::frequency(vec![(1, gens::constant(0u16).boxed()), (2, gens::int(1u16..=500).boxed())]))]
    loss: u16,
    #[ephyra(gen = gens::int(0u64..=6000))]
    lossy_ms: u64,
    /// Which byte of the source id (modulo its length) and the change.
    byte: u8,
    #[ephyra(gen = gens::int(1u8..=255))]
    xor: u8,
    /// Every handshake datagram of the client gets its copy, else only the first.
    every: bool,
    /// The copy arrives this many ms after the genuine datagram.
    #[ephyra(gen = gens::frequency(vec![(2, gens::int(0u64..=5).boxed()), (1, gens::int(0u64..=600).boxed())]))]
    offset_ms: u64,
}

fn in_support(c: &UCase) -> bool {
    (1..=40).contains(&c.delay_ms) && c.loss <= 500 && c.lossy_ms <= 6000 && c.xor > 0 && c.offset_ms <= 600
}

/// The datagram with byte `byte` of the source id of its first packet changed, when that packet is a long Handshake.
fn with_scid_changed(d: &[u8], byte: u8, xor: u8) -> Option<Vec<u8>> {
    let (h, hlen) = LongHeader::parse(d).ok()?;
    if h.ty != LongType::Handshake {
        return None;
    }
    let scid = h.scid.as_bytes();
    let at = d.get(..hlen)?.windows(scid.len()).rposition(|w| w == scid)? + usize::from(byte) % scid.len();
    let mut x = d.to_vec();
    *x.get_mut(at)? ^= xor;
    Some(x)
}

fn run(c: &UCase) {
    let mut net = Net::new(c.seed);
    net.delay = c.delay_ms * MS;
    let cfg = HostCfg {
        split: c.split,
        ..HostCfg::default()
    };
    let (a, b) = (net.add(1, cfg), net.add(2, cfg));
    let (ca, sa_addr, peer) = (net.hosts[a].addr, net.hosts[b].addr, net.hosts[b].id);
    let t0 = net.now;
    let Ok(core_harness::Reply2 {
        value: Value::Session(sa),
    }) = net.hosts[a].cmd(
        t0,
        Command::Connect {
            node: peer,
            alpn: ALPN_A,
            addrs: &[sa_addr],
            role: Role::Other,
        },
    )
    else {
        panic!("the dial was refused");
    };
    let (mut seen, mut sent) = (0usize, 0usize);
    let incoming = |n: &Net| n.hosts[b].count(|e| matches!(e, Event::Incoming { .. }));
    net.run(t0 + 32 * SEC, |n| {
        n.faults.loss = if n.now < t0 + c.lossy_ms * MS { c.loss } else { 0 };
        while seen < n.captured.len() {
            let (from, to, d) = n.captured[seen].clone();
            seen += 1;
            if from != ca || to != sa_addr || (sent > 0 && !c.every) || sent >= 32 {
                continue;
            }
            if let Some(x) = with_scid_changed(&d, c.byte, c.xor) {
                sent += 1;
                n.inject(ca, sa_addr, x, n.delay + c.offset_ms * MS);
            }
        }
        n.hosts[a].opened.contains(&sa) && incoming(n) > 0
    });
    if let Some(v) = net.first_violation() {
        ephyra::signature(v.sig);
        panic!("{}: {}", v.sig, v.detail);
    }
    let at = net.hosts[a]
        .events
        .iter()
        .find(|(_, e)| matches!(e, Event::Connected { session, .. } if *session == sa))
        .map(|(t, _)| (*t - t0) / MS);
    if !(at.is_some_and(|t| t <= 30_000) && incoming(&net) > 0) {
        ephyra::signature("a changed source id of a first-flight packet blocked the honest handshake");
        panic!(
            "the handshake did not complete within 30 s: client connected at {at:?} ms, server incoming {}; {sent} copies sent; client ended {:?}",
            incoming(&net),
            net.hosts[a].events.iter().filter(|(_, e)| matches!(e, Event::ConnectFailed { .. })).map(|(t, _)| (*t - t0) / MS).collect::<Vec<_>>(),
        );
    }
}

#[test]
fn a_changed_source_id_in_a_first_flight_packet_is_dropped() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(60)
            .name("a_changed_source_id_in_a_first_flight_packet_is_dropped");
        ephyra::check(&config, ephyra::any::<UCase>(), |c: UCase| run(&c)).assert_passed();
    });
}

#[test]
fn the_source_id_case_generator_stays_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    check_generator(&cfg, ephyra::any::<UCase>(), in_support).assert_passed();
}

/// The edit finds the source id: the changed copy differs from the datagram in exactly one byte, inside the header.
#[test]
fn the_source_id_edit_changes_one_header_byte() {
    big_stack(|| {
        let mut net = Net::new(0);
        let (a, b) = (net.add(1, HostCfg::default()), net.add(2, HostCfg::default()));
        let (addr, peer, now) = (net.hosts[b].addr, net.hosts[b].id, net.now);
        let r = net.hosts[a].cmd(now, Command::Connect { node: peer, alpn: ALPN_A, addrs: &[addr], role: Role::Other });
        assert!(r.is_ok());
        net.pump_all();
        let d = net.captured.first().map(|c| c.2.clone()).expect("the client sent its first flight");
        let (_, hlen) = LongHeader::parse(&d).expect("a long header");
        let x = with_scid_changed(&d, 3, 0x40).expect("a handshake packet");
        let diff: Vec<usize> = (0..d.len()).filter(|&i| d[i] != x[i]).collect();
        assert_eq!(diff.len(), 1);
        assert!(diff[0] < hlen);
    });
}
