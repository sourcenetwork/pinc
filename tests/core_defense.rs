//! The defences of an endpoint that answers strangers: the amplification ledger, the half-open cap with its Initial
//! size floors and its 30 s expiry.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation,
    clippy::large_stack_arrays
)]

use std::net::SocketAddr;

use vinc_core::{
    Answer, Command, Endpoint, EndpointConfig, Event, LEDGER_ENTRIES, MAX_HALF_OPEN, Query, Role, Slot, TraceEvent,
};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use vinc_security::{ConnId, KeyHandle, LocalIdentity};
use vinc_tests::*;
use vinc_transport::conn::Resources;
use vinc_transport::packet::{LongHeader, LongType};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, Streams};
use vinc_wire::Writer;

/// An established pair where the server (ML-DSA identity) holds a ticket for the client; the client's second dial is
/// captured on the wire without reaching the server. Returns the net, the server and the captured first flight.
fn spoofable_resume() -> (CoreNet, usize, Vec<u8>) {
    let mut net = CoreNet::new(5 * MS_NS);
    let (s, c) = (net.add_with_alg(1, IdentityAlg::MlDsa65), net.add(2));
    let (sa, _) = net.connect_pair(c, s, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let now = net.now;
    net.nodes[c].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
    net.run_for(SEC_NS);
    net.capture = true;
    let (peer, to, now) = (net.nodes[s].node, net.nodes[s].addr, net.now);
    net.loss = Some(Box::new(|_, _, _| true));
    net.nodes[c].connect(now, peer, ALPN_A, to, Role::Other).unwrap();
    net.run_for(100 * MS_NS);
    net.loss = None;
    let hello = net.captured.first().cloned().unwrap().2;
    (net, s, hello)
}

#[test]
fn the_ledger_holds_a_spoofed_resume_to_three_times_what_it_sent() {
    big_stack(|| {
        let (mut net, s, hello) = spoofable_resume();
        let x: SocketAddr = "10.9.9.9:1000".parse().unwrap();
        let to = net.nodes[s].addr;
        assert_eq!(
            net.nodes[s].ep.node_stats().held_by_ledger,
            0,
            "an honest peer is never held"
        );
        let rx = hello.len() as u64;
        net.inject(x, to, hello, 0);
        net.run_for(5 * SEC_NS);
        let Answer::Ledger(e) = net.nodes[s].ep.query(Query::Ledger(x)) else {
            panic!("no entry")
        };
        assert_eq!(e.rx, rx);
        assert!(!e.validated);
        assert!(e.tx <= 3 * e.rx, "charged {} for {} received", e.tx, e.rx);
        let sent: u64 = net.tapped.iter().filter(|t| t.2 == x).map(|t| t.3 as u64 + 28).sum();
        assert_eq!(sent, e.tx, "every datagram that left was charged");
        assert!(
            net.nodes[s].ep.node_stats().held_by_ledger >= 1,
            "the ledger held nothing back"
        );
    });
}

#[test]
fn a_flood_of_spoofed_sources_keeps_the_ledger_bounded_and_each_source_at_three_times() {
    big_stack(|| {
        let (mut net, s, hello) = spoofable_resume();
        let to = net.nodes[s].addr;
        let rx = hello.len();
        let total = LEDGER_ENTRIES + 500;
        let mut sources = Vec::new();
        for i in 0..total {
            let x: SocketAddr = ([172, 16, (i >> 8) as u8, i as u8], 5000).into();
            sources.push(x);
            net.inject(x, to, hello.clone(), 0);
        }
        net.run_for(10 * SEC_NS);
        let ns = net.nodes[s].ep.node_stats();
        assert!(ns.ledger <= LEDGER_ENTRIES, "ledger holds {}", ns.ledger);
        assert!(ns.ledger >= LEDGER_ENTRIES - 2);
        for x in sources {
            let sent: usize = net.tapped.iter().filter(|t| t.2 == x).map(|t| t.3 + 28).sum();
            assert!(sent <= 3 * rx, "{x} was sent {sent} bytes for {rx}");
        }
    });
}

// ---- the half-open cap ----

const BK: usize = MAX_HALF_OPEN + 44;
type BigEp = Endpoint<'static, 'static, Caps, NoSource, 1, 2, 16, 1, BK, { BK * 10 }, 4, 4, 2>;
type BigSlot = Slot<'static, Caps, NoSource, 1, 2, 16, 1>;

fn small_memory() -> Resources<'static, NoSource, 1, 2> {
    let pool = BufferPool::new_boxed(4);
    let streams: &'static mut Streams<NoSource, 1, 2> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    Resources {
        pool,
        streams,
        loss: Box::leak(Box::new(LossEstimate::new())),
    }
}

fn big_server(now: u64) -> (Box<BigEp>, SocketAddr) {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let v: Vec<BigSlot> = (0..BK).map(|_| Slot::new(small_memory())).collect();
    let slots: Box<[BigSlot; BK]> = v.into_boxed_slice().try_into().ok().unwrap();
    let mut ep = Box::new(Endpoint::new(
        now,
        Caps(Software, true),
        Drbg::new(&[3; 32]),
        id,
        EndpointConfig::new(5),
        Box::leak(slots),
    ));
    assert!(ep.register_alpn(ALPN_A));
    let addr: SocketAddr = "10.0.0.1:4433".parse().unwrap();
    ep.add_iface(addr).unwrap();
    (ep, addr)
}

/// A long handshake datagram of exactly `len` bytes whose message starts with `kind`.
fn craft(odcid: u64, kind: u8, len: usize) -> Vec<u8> {
    let mut d = vec![0u8; len];
    let mut cid = [0u8; 8];
    cid.copy_from_slice(&odcid.to_be_bytes());
    let mut h = LongHeader {
        ty: LongType::Handshake,
        dcid: ConnId::new(&cid).unwrap(),
        scid: ConnId::new(&[1, 2, 3, 4]).unwrap(),
        body_len: 0,
    };
    // The length field is a varint of one or two bytes; settle the body length it describes.
    for _ in 0..3 {
        h.body_len = len - h.header_len();
    }
    let mut w = Writer::new(&mut d);
    h.write(&mut w, 0).unwrap();
    w.put_varint(4095).unwrap(); // the message is 4095 bytes in all
    w.put_varint(0).unwrap(); // this fragment starts at offset 0
    w.put_u8(kind).unwrap();
    d
}

fn feed(ep: &mut BigEp, addr: SocketAddr, now: u64, i: u64, mut d: Vec<u8>) {
    let from: SocketAddr = ([10, 1, (i >> 8) as u8, i as u8], 9).into();
    ep.handle_datagram(now, addr, from, &mut d);
}

fn admissions(ep: &mut BigEp) -> Vec<(bool, bool)> {
    let mut v = Vec::new();
    while let Some(r) = ep.poll_trace() {
        if let TraceEvent::HalfOpen { admitted, resume, .. } = r.event {
            v.push((admitted == 1, resume == 1));
        }
    }
    v
}

#[test]
fn the_half_open_cap_floors_and_expiry() {
    big_stack(|| {
        let now = 100 * SEC_NS;
        let (mut ep, addr) = big_server(now);
        // Size floors: a full Initial needs 1200 bytes, a short one 464.
        feed(&mut ep, addr, now, 1, craft(1, 1, 1199));
        feed(&mut ep, addr, now, 2, craft(2, 2, 463));
        assert_eq!(admissions(&mut ep), [(false, false), (false, false)]);
        assert_eq!(ep.node_stats().half_open, 0);
        feed(&mut ep, addr, now, 3, craft(3, 1, 1200));
        feed(&mut ep, addr, now, 4, craft(4, 2, 464));
        assert_eq!(admissions(&mut ep), [(true, false), (true, false)]);
        assert_eq!(ep.node_stats().half_open, 2);
        // Only a first handshake message starts a session; a reply or a finish does not.
        feed(&mut ep, addr, now, 5, craft(5, 4, 1300));
        feed(&mut ep, addr, now, 6, craft(6, 5, 1300));
        assert_eq!(ep.node_stats().half_open, 2);

        // Fill to the cap with sessions that never finish.
        for i in 10..(10 + (MAX_HALF_OPEN as u64 - 2)) {
            feed(&mut ep, addr, now, i, craft(i, 1, 1200));
        }
        assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN);
        let _ = admissions(&mut ep);
        let dropped = ep.node_stats().dropped_in;
        feed(&mut ep, addr, now, 900, craft(900, 1, 1200));
        feed(&mut ep, addr, now, 901, craft(901, 2, 464));
        assert_eq!(admissions(&mut ep), [(false, false), (false, false)]);
        assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN);
        assert_eq!(ep.node_stats().dropped_in, dropped + 2);

        // A resumption Hello is exempt from the cap: it starts a session and the count does not move.
        feed(&mut ep, addr, now, 902, craft(902, 6, 300));
        assert_eq!(admissions(&mut ep), [(true, true)]);
        assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN);

        // Each unauthenticated session lives 30 s, then the cap opens again.
        let end = now + 31 * SEC_NS;
        let mut t = now;
        let mut expired = 0;
        while let Some(next) = ep.poll_timeout() {
            if next > end {
                break;
            }
            t = next.max(t);
            ep.handle_timeout(t);
        }
        while let Some(r) = ep.poll_trace() {
            if matches!(r.event, TraceEvent::HalfOpenExpired { .. }) {
                expired += 1;
            }
        }
        let ns = ep.node_stats();
        assert_eq!((ns.half_open, ns.sessions), (0, 0), "{ns:?}");
        assert!(expired >= MAX_HALF_OPEN, "only {expired} expired");
        assert!(t >= now + 30 * SEC_NS && t <= end);
        feed(&mut ep, addr, end, 903, craft(903, 1, 1200));
        assert_eq!(admissions(&mut ep), [(true, false)]);
        let _: Option<Event> = None;
        let _ = Answer::None;
    });
}
