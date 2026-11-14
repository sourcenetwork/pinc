//! A first flight for an id a half-open session already holds, and that differs from the flight that session was made
//! from, gets a half-open session of its own under the same id: the first holder is never displaced, an id has at most
//! four holders, a long packet is offered to each in turn, the session whose Finish authenticates stays and the others
//! end at the half-open limit, and the half-open cap counts every holder. A forged flight is one whole message in one
//! datagram, the real one with a bit flipped.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::net::SocketAddr;

use vinc_core::{Endpoint, EndpointConfig, Event, HALF_OPEN_LIFE, MAX_HALF_OPEN, NodeStats, Role, Slot, TraceEvent};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use vinc_security::message::FULL_INITIAL_MIN;
use vinc_security::{ConnId, KeyHandle, LocalIdentity};
use vinc_tests::*;
use vinc_transport::conn::{Resources, Tables};
use vinc_transport::packet::{LongHeader, LongType};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, Streams};
use vinc_wire::Writer;

/// Offsets into the first message where a flipped bit makes a different flight that still parses.
const FLIPS: [usize; 5] = [300, 301, 302, 303, 304];

/// What the dialer's first flight put on the wire.
struct Flight {
    /// The first datagram of the flight.
    first: Vec<u8>,
    /// The datagrams of the flight.
    datagrams: Vec<Vec<u8>>,
    /// The whole first message they carry.
    message: Vec<u8>,
}

impl Flight {
    /// What `net` captured of `from`'s long datagrams.
    fn of(net: &CoreNet, from: SocketAddr) -> Self {
        let datagrams: Vec<Vec<u8>> = net
            .captured
            .iter()
            .filter(|(f, _, d)| *f == from && d[0] & 0x80 != 0)
            .map(|c| c.2.clone())
            .collect();
        let message = first_message(datagrams.iter().map(Vec::as_slice)).unwrap();
        Self {
            first: datagrams[0].clone(),
            datagrams,
            message,
        }
    }

    /// The id the flight is for.
    fn dcid(&self) -> ConnId {
        LongHeader::parse(&self.first).unwrap().0.dcid
    }

    /// Another whole first message under the same ids: the real one with a bit flipped.
    fn other(&self, k: usize) -> Vec<u8> {
        let mut m = self.message.clone();
        m[FLIPS[k]] ^= 1;
        forge_message(self.dcid(), &m)
    }

    /// A datagram for the id that no message type claims: it finds its holders and changes none.
    fn probe(&self) -> Vec<u8> {
        forge_message(self.dcid(), &[0xff; 40])
    }
}

/// How many sessions of the endpoint `$ep` hold the id of `$flight`, as the demultiplexing of a probe finds them.
macro_rules! holders {
    ($ep:expr, $flight:expr, $now:expr, $local:expr, $remote:expr) => {{
        while $ep.poll_trace().is_some() {}
        $ep.handle_datagram($now, $local, $remote, &mut $flight.probe());
        let mut found = None;
        while let Some(r) = $ep.poll_trace() {
            if let TraceEvent::Demux { candidates, .. } = r.event {
                found = Some(candidates);
            }
        }
        found.unwrap()
    }};
}

struct Pair {
    net: CoreNet,
    a: usize,
    b: usize,
    flight: Flight,
}

impl Pair {
    fn new() -> Self {
        Self::with_alg(IdentityAlg::Ed25519)
    }

    /// A pair whose dialer has the identity `alg`: its Finish spans as many datagrams as the identity needs.
    fn with_alg(alg: IdentityAlg) -> Self {
        let mut net = CoreNet::new(5 * MS_NS);
        net.capture = true;
        let (a, b) = (net.add_with_alg(1, alg), net.add(2));
        let (addr_a, addr_b) = (net.nodes[a].addr, net.nodes[b].addr);
        let (peer, now) = (net.nodes[b].node, net.now);
        net.nodes[a].connect(now, peer, ALPN_A, addr_b, Role::Other).unwrap();
        net.pump_all();
        let flight = Flight::of(&net, addr_a);
        Self { net, a, b, flight }
    }

    fn addrs(&self) -> (SocketAddr, SocketAddr) {
        (self.net.nodes[self.a].addr, self.net.nodes[self.b].addr)
    }

    /// Hand the responder a forged flight now.
    fn forge(&mut self, k: usize) {
        let (addr_a, addr_b) = self.addrs();
        let now = self.net.now;
        let mut d = self.flight.other(k);
        self.net.nodes[self.b].ep.handle_datagram(now, addr_b, addr_a, &mut d);
    }

    fn stats(&self) -> NodeStats {
        self.net.nodes[self.b].ep.node_stats()
    }

    fn holders(&mut self) -> u64 {
        let (addr_a, addr_b) = self.addrs();
        let now = self.net.now;
        holders!(self.net.nodes[self.b].ep, self.flight, now, addr_b, addr_a)
    }

    /// Run until both ends report the session open.
    fn open(&mut self) -> bool {
        let (a, b) = (self.a, self.b);
        let end = self.net.now + 10 * SEC_NS;
        self.net.run(end, |n| {
            n.nodes[a].saw(|e| matches!(e, Event::Connected { .. }))
                && n.nodes[b].saw(|e| matches!(e, Event::Incoming { .. }))
        })
    }
}

/// A forged flight that arrives after the real one changes nothing for the real pair: both ends open.
#[test]
fn a_forged_flight_after_the_real_one_leaves_the_real_pair_to_open() {
    big_stack(|| {
        let mut p = Pair::new();
        let (addr_a, addr_b) = p.addrs();
        let forged = p.flight.other(0);
        p.net.inject(addr_a, addr_b, forged, 7 * MS_NS);
        assert!(
            p.open(),
            "{:?} / {:?}",
            p.net.nodes[p.a].events,
            p.net.nodes[p.b].events
        );
        let st = p.stats();
        assert_eq!(
            (st.sessions, st.half_open),
            (2, 1),
            "the forged flight got a session beside the real one"
        );
    });
}

/// A damaged flight that arrives before the correct one does not stop the dial: the repeat is the second holder.
#[test]
fn a_damaged_flight_before_the_correct_one_still_connects() {
    big_stack(|| {
        let mut p = Pair::new();
        let (addr_a, addr_b) = p.addrs();
        let damaged = p.flight.other(0);
        p.net.inject(addr_a, addr_b, damaged, MS_NS);
        assert!(
            p.open(),
            "{:?} / {:?}",
            p.net.nodes[p.a].events,
            p.net.nodes[p.b].events
        );
    });
}

/// A later datagram of the flight damaged on the way, then the correct flight: the repeat still connects.
#[test]
fn a_flight_damaged_in_a_later_datagram_before_the_correct_one_still_connects() {
    big_stack(|| {
        let mut p = Pair::new();
        let (addr_a, addr_b) = p.addrs();
        assert!(p.flight.datagrams.len() > 1, "the first flight is one datagram");
        for (k, d) in p.flight.datagrams.iter().enumerate() {
            let mut d = d.clone();
            if k + 1 == p.flight.datagrams.len() {
                let (_, hlen) = LongHeader::parse(&d).unwrap();
                d[hlen + 12] ^= 1;
            }
            p.net.inject(addr_a, addr_b, d, MS_NS);
        }
        assert!(
            p.open(),
            "{:?} / {:?}",
            p.net.nodes[p.a].events,
            p.net.nodes[p.b].events
        );
    });
}

/// Three forged flights under one id do not hide the real session; a fifth different flight is dropped and counted;
/// the four holders are still reachable, and the real pair opens.
#[test]
fn forged_flights_under_one_id_do_not_hide_the_real_session() {
    big_stack(|| {
        let mut p = Pair::new();
        let (addr_a, addr_b) = p.addrs();
        // The real flight arrives first and makes the first holder.
        let end = p.net.now + 6 * MS_NS;
        p.net.run(end, |_| false);
        assert_eq!(p.stats().half_open, 1);
        for k in 0..3 {
            p.forge(k);
            assert_eq!(p.stats().half_open, 2 + k, "forged flight {k}");
        }
        assert_eq!(p.holders(), 4);
        let before = p.stats();
        assert_eq!(before.holders_refused, 0);
        p.forge(3);
        let after = p.stats();
        assert_eq!((after.holders_refused, after.dropped_in - before.dropped_in), (1, 1));
        assert_eq!((after.half_open, after.sessions), (4, 4));
        assert_eq!(p.holders(), 4, "the four holders are still reachable");
        // The identical repeat of the real flight reaches its holder and makes no session.
        for mut d in p.flight.datagrams.clone() {
            let now = p.net.now;
            p.net.nodes[p.b].ep.handle_datagram(now, addr_b, addr_a, &mut d);
        }
        assert_eq!(p.stats().half_open, 4);
        assert!(
            p.open(),
            "{:?} / {:?}",
            p.net.nodes[p.a].events,
            p.net.nodes[p.b].events
        );
    });
}

/// The holder whose Finish authenticated is the one left under the id: the others are gone after the half-open limit,
/// and the table has no entry left for them.
#[test]
fn the_session_whose_finish_authenticates_stays_under_the_id() {
    big_stack(|| {
        // The forged flight comes after the real one, and before it (a damaged flight and its repeat).
        for forged_first in [false, true] {
            let mut p = Pair::new();
            let (addr_a, addr_b) = p.addrs();
            let forged = p.flight.other(1);
            let delay = if forged_first { MS_NS } else { 7 * MS_NS };
            p.net.inject(addr_a, addr_b, forged, delay);
            assert!(p.open());
            let st = p.stats();
            assert_eq!((st.sessions, st.half_open), (2, 1), "forged_first {forged_first}");
            let held = p.holders();
            let t = p.net.now + HALF_OPEN_LIFE + 2 * SEC_NS;
            p.net.run(t, |_| false);
            let st = p.stats();
            assert_eq!((st.sessions, st.half_open), (1, 0), "forged_first {forged_first}");
            assert_eq!(p.holders(), held - 1, "the table kept an entry of the ended session");
            assert!(!p.net.nodes[p.b].saw(|e| matches!(e, Event::Closed { .. })));
        }
    });
}

/// `d` with its destination id replaced by `dcid` (a long handshake packet is not sealed, so nothing else changes).
fn readdressed(d: &[u8], dcid: ConnId) -> Vec<u8> {
    let (h, hlen) = LongHeader::parse(d).unwrap();
    let body = &d[hlen..hlen + h.body_len];
    let h = LongHeader { dcid, ..h };
    let mut out = vec![0u8; h.header_len() + body.len()];
    let mut w = Writer::new(&mut out);
    h.write(&mut w, 0).unwrap();
    w.put_slice(body).unwrap();
    out
}

/// A Finish that spans several datagrams and reaches the id of the first flight (as when a path hands the dialer's
/// packets to the shared id) reaches every holder of the id, and only the session whose key opens it takes it: the real
/// pair opens whichever flight came first, the other holder is not closed by the parts and ends at its own half-open
/// limit. The dialer addresses its Finish to the id its responder chose, so the test keeps those datagrams back and
/// hands them over readdressed to the id of the first flight (and keeps back what the dialer resends, so only
/// those copies can complete the Finish).
fn finish_of_several_datagrams(forged_delay: u64) {
    use std::cell::RefCell;
    use std::rc::Rc;

    let mut p = Pair::with_alg(IdentityAlg::MlDsa65);
    let (addr_a, addr_b) = p.addrs();
    let odcid = p.flight.dcid();
    let kept: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
    let sink = Rc::clone(&kept);
    p.net.loss = Some(Box::new(move |from, _, d| {
        let to_other_id =
            from == addr_a && d[0] & 0x80 != 0 && LongHeader::parse(d).is_ok_and(|(h, _)| h.dcid != odcid);
        if to_other_id {
            sink.borrow_mut().push(d.to_vec());
        }
        to_other_id
    }));
    let forged = p.flight.other(1);
    p.net.inject(addr_a, addr_b, forged, forged_delay);
    // The dialer's repeat of its flight is what the forged-first case waits for.
    let end = p.net.now + 5 * SEC_NS;
    p.net.run(end, |_| !kept.borrow().is_empty());
    p.net.run_for(50 * MS_NS);
    let finish: Vec<Vec<u8>> = kept.borrow().iter().map(|d| readdressed(d, odcid)).collect();
    assert!(
        finish.len() >= 3,
        "the Finish did not span datagrams ({})",
        finish.len()
    );
    for d in finish {
        p.net.inject(addr_a, addr_b, d, 0);
    }
    assert!(
        p.open(),
        "{:?} / {:?}",
        p.net.nodes[p.a].events,
        p.net.nodes[p.b].events
    );
    let st = p.stats();
    assert_eq!(
        (st.sessions, st.half_open),
        (2, 1),
        "the forged holder is not half-open any more"
    );
    assert!(
        !p.net.nodes[p.b].saw(|e| matches!(e, Event::Closed { .. })),
        "a holder was closed"
    );
    let t = p.net.now + HALF_OPEN_LIFE + 2 * SEC_NS;
    p.net.run(t, |_| false);
    let st = p.stats();
    assert_eq!(
        (st.sessions, st.half_open),
        (1, 0),
        "the forged holder did not end by its own life"
    );
    assert!(!p.net.nodes[p.b].saw(|e| matches!(e, Event::Closed { .. })));
}

/// The real flight, then a forged one, then the real Finish in several datagrams.
#[test]
fn a_finish_of_several_datagrams_is_taken_by_the_real_holder_when_a_forged_flight_came_after() {
    big_stack(|| finish_of_several_datagrams(7 * MS_NS));
}

/// The forged flight, then the real one, then the real Finish in several datagrams.
#[test]
fn a_finish_of_several_datagrams_is_taken_by_the_real_holder_when_a_forged_flight_came_first() {
    big_stack(|| finish_of_several_datagrams(MS_NS));
}

/// The table of the endpoint: room past the cap, so the cap and not the table refuses.
const K: usize = MAX_HALF_OPEN + 44;

type BigEp = Endpoint<'static, 'static, Caps, NoSource, 1, 2, 16, 1, K, { K * 10 }, 4, 4, 2>;
type TSlot = Slot<'static, Caps, NoSource, 1, 2, 16, 1>;

fn server(now: u64) -> (Box<BigEp>, SocketAddr) {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let v: Vec<TSlot> = (0..K).map(|_| Slot::new(small_memory())).collect();
    let slots: Box<[TSlot; K]> = v.into_boxed_slice().try_into().ok().unwrap();
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

fn small_memory() -> Resources<'static, NoSource, 1, 2, 16> {
    let pool = BufferPool::new_boxed(4);
    let streams: &'static mut Streams<NoSource, 1, 2> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    Resources {
        pool,
        streams: streams.into(),
        loss: (&*Box::leak(Box::new(LossEstimate::new()))).into(),
        tables: Tables::new(),
    }
}

/// A first flight of `FULL_INITIAL_MIN` bytes for `odcid` whose message is longer than the datagram.
fn craft(odcid: u64) -> Vec<u8> {
    let mut d = vec![0u8; FULL_INITIAL_MIN];
    let mut h = LongHeader {
        ty: LongType::Handshake,
        dcid: ConnId::new(&odcid.to_be_bytes()).unwrap(),
        scid: ConnId::new(&[1, 2, 3, 4]).unwrap(),
        body_len: 0,
    };
    for _ in 0..3 {
        h.body_len = FULL_INITIAL_MIN - h.header_len();
    }
    let mut w = Writer::new(&mut d);
    h.write(&mut w, 0).unwrap();
    w.put_varint(4095).unwrap();
    w.put_varint(0).unwrap();
    w.put_u8(1).unwrap();
    w.put_u8(odcid as u8).unwrap();
    d
}

fn source(i: u64) -> SocketAddr {
    SocketAddr::from(([10, 1, (i >> 8) as u8, i as u8], 9))
}

/// The half-open cap counts every holder of an id, and a different flight at the cap is refused by the cap.
#[test]
fn the_half_open_cap_counts_every_holder() {
    big_stack(|| {
        let mut net = CoreNet::new(MS_NS);
        net.capture = true;
        let a = net.add(1);
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
        let peer = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap().node_id();
        let (addr_a, now) = (net.nodes[a].addr, net.now);
        let (mut ep, addr) = server(now);
        net.nodes[a].connect(now, peer, ALPN_A, addr, Role::Other).unwrap();
        net.pump_all();
        let flight = Flight::of(&net, addr_a);
        // Strangers fill all but three places.
        for i in 0..(MAX_HALF_OPEN - 3) as u64 {
            ep.handle_datagram(now, addr, source(i), &mut craft(0x1000 + i));
        }
        assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN - 3);
        // The real flight and two other flights under its id take the last three: each holder is counted.
        for mut d in flight.datagrams.clone() {
            ep.handle_datagram(now, addr, addr_a, &mut d);
        }
        assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN - 2, "the real flight");
        for k in 0..2 {
            ep.handle_datagram(now, addr, addr_a, &mut flight.other(k));
            assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN - 1 + k, "forged flight {k}");
        }
        // At the cap, a third different flight under the id makes no session: the cap refuses it, not the holders.
        let before = ep.node_stats();
        ep.handle_datagram(now, addr, addr_a, &mut flight.other(2));
        let after = ep.node_stats();
        assert_eq!(after.half_open, MAX_HALF_OPEN);
        assert_eq!(
            (after.sessions, after.dropped_in - before.dropped_in),
            (before.sessions, 1)
        );
        assert_eq!(after.holders_refused, 0);
        assert_eq!(holders!(ep, flight, now, addr, addr_a), 3);
    });
}

/// `token` in front of `flight`, as a dialer behind a retry sends it: a long retry packet under the flight's ids.
fn behind(token: &[u8], flight: &[u8]) -> Vec<u8> {
    let (h, _) = LongHeader::parse(flight).unwrap();
    let echo = LongHeader {
        ty: LongType::Retry,
        dcid: h.dcid,
        scid: h.scid,
        body_len: token.len(),
    };
    let mut out = vec![0u8; echo.header_len() + token.len()];
    let mut w = Writer::new(&mut out);
    echo.write(&mut w, 0).unwrap();
    w.put_slice(token).unwrap();
    out.extend_from_slice(flight);
    out
}

/// At the cap, a different flight under a held id gets a retry, comes back behind its token as another holder beside
/// the first one (never in its place) while the id has room, and a flight past the holder limit gets no retry.
#[test]
fn a_retry_at_the_cap_keeps_the_holders_of_an_id() {
    big_stack(|| {
        let mut net = CoreNet::new(MS_NS);
        net.capture = true;
        let a = net.add(1);
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
        let peer = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap().node_id();
        let (addr_a, now) = (net.nodes[a].addr, net.now);
        let (mut ep, addr) = server(now);
        net.nodes[a].connect(now, peer, ALPN_A, addr, Role::Other).unwrap();
        net.pump_all();
        let flight = Flight::of(&net, addr_a);
        for i in 0..(MAX_HALF_OPEN - 3) as u64 {
            ep.handle_datagram(now, addr, source(i), &mut craft(0x1000 + i));
        }
        for mut d in flight.datagrams.clone() {
            ep.handle_datagram(now, addr, addr_a, &mut d);
        }
        for k in 0..2 {
            ep.handle_datagram(now, addr, addr_a, &mut flight.other(k));
        }
        assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN);
        let mut buf = vec![0u8; 65_536];
        while ep.poll_transmit(now, &mut buf).is_some() {}
        // A third different flight at the cap: refused by the cap, and answered with a retry.
        ep.handle_datagram(now, addr, addr_a, &mut flight.other(2));
        let t = ep.poll_transmit(now, &mut buf).unwrap();
        let (h, hl) = LongHeader::parse(&buf[..t.len]).unwrap();
        assert_eq!((h.ty, t.remote), (LongType::Retry, addr_a));
        let token = buf[hl..t.len].to_vec();
        // Behind its token it gets a session of its own beside the three holders, uncounted.
        ep.handle_datagram(now, addr, addr_a, &mut behind(&token, &flight.other(2)));
        let ns = ep.node_stats();
        assert_eq!(
            (ns.token_admitted, ns.half_open, ns.holders_refused),
            (1, MAX_HALF_OPEN, 0)
        );
        assert_eq!(
            holders!(ep, flight, now, addr, addr_a),
            4,
            "the holders are kept and the new one joins them"
        );
        // A fifth flight under the full id: the holder limit refuses it, and no retry is offered.
        let sent = ep.node_stats().retries_sent + ep.node_stats().retries_waiting as u64;
        ep.handle_datagram(now, addr, addr_a, &mut behind(&token, &flight.other(3)));
        let ns = ep.node_stats();
        assert_eq!(ns.holders_refused, 1);
        assert_eq!(ns.retries_sent + ns.retries_waiting as u64, sent);
    });
}
