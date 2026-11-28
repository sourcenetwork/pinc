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

use pinc_core::{Endpoint, EndpointConfig, Event, HALF_OPEN_HOLD, MAX_HALF_OPEN, NodeStats, Role, Slot, TraceEvent};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::message::FULL_INITIAL_MIN;
use pinc_security::{ConnId, KeyHandle, LocalIdentity};
use pinc_tests::*;
use pinc_transport::conn::{Resources, Tables};
use pinc_transport::packet::{LongHeader, LongType};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{self, NoSource, Streams};
use pinc_wire::Writer;

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
            let t = p.net.now + HALF_OPEN_HOLD + 2 * SEC_NS;
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
    let t = p.net.now + HALF_OPEN_HOLD + 2 * SEC_NS;
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

/// The length, offset and bytes of the fragment in the long Handshake datagram `d`.
fn parts(d: &[u8]) -> (usize, usize, Vec<u8>) {
    let (h, at) = LongHeader::parse(d).unwrap();
    let mut r = pinc_wire::Reader::new(&d[at..at + h.body_len]);
    let (total, off) = (r.read_varint().unwrap() as usize, r.read_varint().unwrap() as usize);
    (total, off, r.read_bytes(r.remaining()).unwrap().to_vec())
}

/// A datagram for `dcid` that carries `data` at `off` of a message of `total` bytes.
fn piece(dcid: ConnId, total: usize, off: usize, data: &[u8]) -> Vec<u8> {
    let mut body = vec![0u8; data.len() + 16];
    let mut w = Writer::new(&mut body);
    w.put_varint(total as u64).unwrap();
    w.put_varint(off as u64).unwrap();
    w.put_slice(data).unwrap();
    let n = w.written().len();
    forge_packet(dcid, &body[..n])
}

/// The first flight in two datagrams, and the dialer's own copies kept off the wire: the test hands the responder
/// every datagram itself, spaced as it chooses.
struct Held {
    p: Pair,
    /// The datagram with the start of the message and the one with the rest.
    d0: Vec<u8>,
    d1: Vec<u8>,
    /// Where the rest begins.
    cut: usize,
    total: usize,
}

impl Held {
    fn new() -> Self {
        let mut p = Pair::new();
        let (addr_a, _) = p.addrs();
        let odcid = p.flight.dcid();
        p.net.loss = Some(Box::new(move |from, _, d| {
            from == addr_a && d[0] & 0x80 != 0 && LongHeader::parse(d).is_ok_and(|(h, _)| h.dcid == odcid)
        }));
        let both: Vec<Vec<u8>> = p
            .flight
            .datagrams
            .iter()
            .filter(|d| LongHeader::parse(d).is_ok_and(|(h, _)| h.ty == LongType::Handshake))
            .cloned()
            .collect();
        assert_eq!(both.len(), 2, "the first flight is not two datagrams");
        let (total, cut, _) = parts(&both[1]);
        assert_eq!(parts(&both[0]).1, 0);
        Self {
            p,
            d0: both[0].clone(),
            d1: both[1].clone(),
            cut,
            total,
        }
    }

    fn dcid(&self) -> ConnId {
        self.p.flight.dcid()
    }

    /// Hand the responder `d` now.
    fn feed(&mut self, d: &[u8]) {
        let (addr_a, addr_b) = self.p.addrs();
        let now = self.p.net.now;
        self.p.net.nodes[self.p.b]
            .ep
            .handle_datagram(now, addr_b, addr_a, &mut d.to_vec());
    }

    fn feed_all(&mut self, ds: &[&[u8]]) {
        for d in ds {
            self.feed(d);
        }
    }

    /// Let `ms` pass.
    fn wait(&mut self, ms: u64) {
        let end = self.p.net.now + ms * MS_NS;
        self.p.net.run(end, |_| false);
    }

    /// `d0` with one byte of its message flipped.
    fn damaged_start(&self) -> Vec<u8> {
        let mut d = self.d0.clone();
        let (_, at) = LongHeader::parse(&d).unwrap();
        d[at + 320] ^= 1;
        d
    }

    /// The whole message with the byte `at` flipped, in one datagram.
    fn damaged_whole(&self, at: usize) -> Vec<u8> {
        let mut m = self.p.flight.message.clone();
        m[at] ^= 1;
        forge_message(self.dcid(), &m)
    }

    /// One byte at the cut, flipped: a later part that disagrees with the real one.
    fn damaged_part(&self) -> Vec<u8> {
        let mut m = self.p.flight.message.clone();
        m[self.cut] ^= 1;
        piece(self.dcid(), self.total, self.cut, &m[self.cut..=self.cut])
    }

    fn served(&mut self) -> bool {
        self.p.open()
    }
}

/// A repeat that adds nothing to a first message still being assembled is not a take: the flight that follows a forged
/// part is served (the replays 3:3 and 1:86 of the model-based test, witness `FirstFlight_cmp`: `[d0, bad, d1]`, then
/// `[d0, d1]`).
#[test]
fn a_repeat_start_that_adds_nothing_does_not_hide_a_later_part_that_was_refused() {
    big_stack(|| {
        let mut h = Held::new();
        let (d0, d1, bad) = (h.d0.clone(), h.d1.clone(), h.damaged_part());
        h.feed_all(&[&d0, &bad, &d1]);
        h.wait(10);
        h.feed_all(&[&d0, &d1]);
        assert!(h.served(), "the repeated flight was not served");
        assert_eq!(
            h.p.stats().starts_held,
            0,
            "the repeat start made a holder at once, nothing was held"
        );
    });
}

/// A repeat of the start after a part a holder refused makes a holder at once and is not held, so the part before the
/// start of the next flight finds it (witness `FirstFlight_b4`: flight `[d0, bad, d1]`, then `[d1, d0]`).
#[test]
fn a_repeat_start_after_a_held_part_makes_a_holder_at_once() {
    big_stack(|| {
        let mut h = Held::new();
        let (d0, d1, bad) = (h.d0.clone(), h.d1.clone(), h.damaged_part());
        h.feed_all(&[&d0, &bad, &d1]);
        h.wait(10);
        h.feed_all(&[&d1, &d0]);
        assert_eq!(
            h.p.stats().starts_held,
            0,
            "the repeated start was only held, it made no holder at once"
        );
        assert!(h.served(), "the part before the repeated start was not served");
    });
}

/// A damaged start between the genuine parts does not win: the next flight's genuine start and rest are served
/// (witness `FirstFlight_old`: flight `[d0, damaged start, d1]`, then `[d0, d1]`).
#[test]
fn a_damaged_start_between_the_genuine_parts_does_not_win() {
    big_stack(|| {
        let mut h = Held::new();
        let (d0, d1, bad_start) = (h.d0.clone(), h.d1.clone(), h.damaged_start());
        h.feed_all(&[&d0, &bad_start, &d1]);
        // The damaged start is refused as different by the holder of the genuine start and gets a holder of its own:
        // its bytes are not mixed into the genuine message, and it is not held as a repeat.
        let st = h.p.stats();
        assert_eq!(
            (st.half_open, st.starts_held),
            (2, 0),
            "the damaged start did not get its own holder"
        );
        h.wait(10);
        h.feed_all(&[&d0, &d1]);
        assert!(h.served(), "the genuine flight was not served after a damaged start");
    });
}

/// A datagram that coalesces a repeat of the first message's start with a new part is weak (any weak packet makes it
/// so): its start is held, as for any start no holder took as new.
#[test]
fn a_datagram_with_a_repeat_part_and_a_new_part_is_weak() {
    big_stack(|| {
        let mut h = Held::new();
        let (d0, d1) = (h.d0.clone(), h.d1.clone());
        h.feed(&d0);
        h.feed(&[d0.as_slice(), d1.as_slice()].concat());
        assert_eq!(h.p.stats().starts_held, 1, "the coalesced datagram was not weak");
        assert!(
            h.served(),
            "the message the coalesced datagram completed was not served"
        );
    });
}

/// A later part that one holder refused and another took only as a repeat forks a holder from the held start (the
/// replay 5:114).
#[test]
fn a_later_part_that_only_repeats_took_forks_from_the_held_start() {
    big_stack(|| {
        let mut h = Held::new();
        let (d0, d1) = (h.d0.clone(), h.d1.clone());
        let (bad_start, bad_whole) = (h.damaged_start(), h.damaged_whole(h.cut + 5));
        h.feed_all(&[&d0, &bad_start, &bad_whole, &d1]);
        h.wait(10);
        h.feed_all(&[&d0, &d1]);
        assert!(h.served(), "the repeated flight was not served");
    });
}

/// The start a later part forks from is the newest held start that agrees with it, not the newest: the newest is a
/// copy of a forged whole message that the part contradicts.
#[test]
fn a_later_part_forks_from_the_held_start_that_agrees_with_it() {
    big_stack(|| {
        let mut h = Held::new();
        let (d0, d1) = (h.d0.clone(), h.d1.clone());
        let (bad_part, bad_whole) = (h.damaged_part(), h.damaged_whole(h.cut + 5));
        // The first holder takes the forged byte at the cut, so it refuses the real rest; the forged whole message
        // makes a holder of its own.
        h.feed_all(&[&d0, &bad_part, &bad_whole]);
        h.wait(10);
        // Both repeat: the real start and then the forged one are held, and the real rest finds no holder.
        h.feed_all(&[&d0, &bad_whole, &d1]);
        assert!(h.served(), "the second flight was not served");
    });
}

/// A part held for a start that is not its own stays held: a holder that refuses the replay does not take the part
/// from the genuine start that comes after.
#[test]
fn a_held_part_a_holder_refused_in_the_replay_stays_held_for_the_genuine_start() {
    big_stack(|| {
        let mut h = Held::new();
        let (d0, d1, bad_start) = (h.d0.clone(), h.d1.clone(), h.damaged_start());
        h.feed_all(&[&d1, &bad_start, &d0]);
        assert!(h.served(), "the genuine start did not find the held part");
    });
}

/// At the cap a differing later part that would fork a holder from a held start is refused by the same checks as a new
/// flight: the half-open count stays at the cap and the refusal is counted.
#[test]
fn a_fork_at_the_half_open_cap_is_refused_and_counted() {
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
        let both: Vec<Vec<u8>> = flight
            .datagrams
            .iter()
            .filter(|d| LongHeader::parse(d).is_ok_and(|(h, _)| h.ty == LongType::Handshake))
            .cloned()
            .collect();
        assert_eq!(both.len(), 2);
        // Strangers fill all but one place, the real flight takes the last.
        for i in 0..(MAX_HALF_OPEN - 1) as u64 {
            ep.handle_datagram(now, addr, source(i), &mut craft(0x1000 + i));
        }
        for d in &both {
            ep.handle_datagram(now, addr, addr_a, &mut d.clone());
        }
        assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN);
        // A copy of the holder's start is held, then a part that contradicts the genuine message.
        ep.handle_datagram(now, addr, addr_a, &mut both[0].clone());
        let (total, cut, _) = parts(&both[1]);
        let mut m = flight.message.clone();
        m[cut] ^= 1;
        let before = ep.node_stats();
        ep.handle_datagram(now, addr, addr_a, &mut piece(flight.dcid(), total, cut, &m[cut..=cut]));
        let after = ep.node_stats();
        assert_eq!(after.half_open, MAX_HALF_OPEN, "a fork went past the cap");
        assert_eq!(after.sessions, before.sessions);
        assert_eq!(after.dropped_in - before.dropped_in, 1, "the refusal is not counted");
    });
}
