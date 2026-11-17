//! The defences of an endpoint that answers strangers: the amplification ledger, the half-open cap with its Initial
//! size floors and its expiry (30 s, 60 s on a thin node).
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

use std::collections::HashMap;
use std::net::SocketAddr;

use vinc_core::{
    Answer, Command, Endpoint, EndpointConfig, Event, LEDGER_ENTRIES, MAX_HALF_OPEN, Query, Role, Slot, TraceEvent,
};
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_crypto::{Aead, Drbg, IdentityAlg, Keypair, Software};
use vinc_security::message::{FULL_INITIAL_MIN, Initial, MessageType, PrekeyField, ResumeHello, SHORT_INITIAL_MIN};
use vinc_security::{
    AeadSet, ConnId, CreditRecord, Env, KeyHandle, KeyResponse, LocalIdentity, SoftKeys, SoftPrekeys, VERSION,
};
use vinc_tests::*;
use vinc_transport::conn::{Resources, Tables};
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
        // The one datagram the ledger refused here was the server's size probe for the new address; the connection
        // offers none for an address the ledger holds, so nothing is refused and the bound above is met by what left.
        assert_eq!(
            net.nodes[s].ep.node_stats().held_by_ledger,
            0,
            "the server built a size probe for an address the ledger holds"
        );
    });
}

/// The time from a resumption dial with nothing written (a bare Hello) to the client's session being established, from
/// the client's own address or from one the server never saw (`moved`), and the client's handshake resends. The
/// server's identity is ML-DSA and its flights are not split, as in the default configuration. The dial is reported at
/// once (the access check of the peer is cached), so the session's state is read instead of the event.
fn bare_resume(moved: bool) -> (Option<u64>, u64) {
    let mut net = CoreNet::new(5 * MS_NS);
    let (s, c) = (net.add_whole_flights(1, IdentityAlg::MlDsa65), net.add(2));
    let (sa, _) = net.connect_pair(c, s, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let now = net.now;
    net.nodes[c].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
    net.run_for(SEC_NS);
    if moved {
        net.nat = Some((net.nodes[c].addr, "10.7.7.7:5555".parse().unwrap()));
    }
    net.nodes[c].events.clear();
    let (peer, to, t0) = (net.nodes[s].node, net.nodes[s].addr, net.now);
    let rep = net.nodes[c].connect(t0, peer, ALPN_A, to, Role::Other).unwrap();
    let session = net.nodes[c].session(&rep);
    let stats = |n: &CoreNet| match n.nodes[c].ep.query(Query::Stats(session)) {
        Answer::Stats(st) => Some(st),
        _ => None,
    };
    let up = net.run(t0 + 30 * SEC_NS, |n| stats(n).is_some_and(|st| st.established));
    let resends = stats(&net).map_or(0, |st| st.transport.handshake_retransmits);
    (up.then(|| net.now - t0), resends)
}

#[test]
fn a_bare_resumption_hello_from_a_new_address_completes() {
    big_stack(|| {
        let (home, home_resends) = bare_resume(false);
        let (moved, moved_resends) = bare_resume(true);
        eprintln!(
            "bare resumption: home {:?} ms, {home_resends} resends; moved {:?} ms, {moved_resends} resends",
            home.map(|t| t / MS_NS),
            moved.map(|t| t / MS_NS)
        );
        assert!(home.is_some(), "the resumption from the client's own address failed");
        let Some(moved) = moved else {
            panic!("a bare resumption from a new address never got its Reply")
        };
        assert!(moved <= 5 * SEC_NS, "the resumption took {} ms", moved / MS_NS);
    });
}

/// A bare resumption dial, from the client's own address or from a new one (`moved`), then a few seconds on. Returns
/// what the server's side of the session shows: datagrams its ledger held back, packets its session declared lost and
/// probe timeouts it fired. A datagram the ledger refuses is taken for sent by the connection, so it would be one of
/// them.
fn bare_resume_server(moved: bool) -> (u64, u64, u64) {
    let mut net = CoreNet::new(5 * MS_NS);
    let (s, c) = (net.add_whole_flights(1, IdentityAlg::MlDsa65), net.add(2));
    let (sa, _) = net.connect_pair(c, s, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let now = net.now;
    net.nodes[c].cmd(now, Command::Close { session: sa, error: 0 }).unwrap();
    net.run_for(SEC_NS);
    if moved {
        net.nat = Some((net.nodes[c].addr, "10.7.7.7:5555".parse().unwrap()));
    }
    let held0 = net.nodes[s].ep.node_stats().held_by_ledger;
    let (peer, to, t0) = (net.nodes[s].node, net.nodes[s].addr, net.now);
    net.nodes[c].connect(t0, peer, ALPN_A, to, Role::Other).unwrap();
    net.run_for(5 * SEC_NS);
    let session = net.nodes[s]
        .events
        .iter()
        .rev()
        .find_map(|(at, e)| match e {
            Event::Incoming { session, .. } if *at >= t0 => Some(*session),
            _ => None,
        })
        .unwrap();
    let Answer::Stats(st) = net.nodes[s].ep.query(Query::Stats(session)) else {
        panic!("no stats")
    };
    let held = net.nodes[s].ep.node_stats().held_by_ledger - held0;
    (held, st.transport.packets_lost, st.transport.ptos)
}

#[test]
fn a_bare_resumption_from_a_new_address_leaves_nothing_held_and_nothing_lost() {
    big_stack(|| {
        let home = bare_resume_server(false);
        let moved = bare_resume_server(true);
        assert_eq!(
            home,
            (0, 0, 0),
            "held, lost and probe timeouts of the resumption from the client's own address"
        );
        assert_eq!(
            moved,
            (0, 0, 0),
            "held, lost and probe timeouts of the resumption from a new address"
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
        // A short Initial that does not parse is dropped before it takes a slot.
        feed(&mut ep, addr, now, 4, craft(4, 2, 464));
        assert_eq!(admissions(&mut ep), [(true, false), (false, false)]);
        assert_eq!(ep.node_stats().half_open, 1);
        // Only a first handshake message starts a session; a reply or a finish does not.
        feed(&mut ep, addr, now, 5, craft(5, 4, 1300));
        feed(&mut ep, addr, now, 6, craft(6, 5, 1300));
        assert_eq!(ep.node_stats().half_open, 1);

        // Fill to the cap with sessions that never finish.
        for i in 10..(10 + (MAX_HALF_OPEN as u64 - 1)) {
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

        // A resumption Hello whose ticket does not open is counted like an Initial: the full table refuses it.
        let dropped = ep.node_stats().dropped_in;
        feed(&mut ep, addr, now, 902, craft(902, 6, 300));
        assert_eq!(admissions(&mut ep), [(false, false)]);
        assert_eq!(ep.node_stats().half_open, MAX_HALF_OPEN);
        assert_eq!(ep.node_stats().dropped_in, dropped + 1);

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

/// A responder on a slow link keeps a session whose peer is not authenticated yet as long as a handshake may last on
/// such a node, 60 s: a dialer that finished its handshake and whose Finish waits more than 30 s in a queue on its slow
/// uplink is answered when the Finish arrives, not left holding a session the responder dropped. A handshake that is
/// never finished still ends at 60 s.
#[test]
fn a_thin_responder_holds_a_half_open_session_until_a_late_finish_arrives() {
    big_stack(|| {
        // 150 ms each way: the responder measures a 300 ms round trip on its own dial, so it is thin.
        let mut net = CoreNet::new(150 * MS_NS);
        let (s, w, c, d) = (net.add(1), net.add(2), net.add(3), net.add(4));
        net.connect_pair(s, w, ALPN_A, Role::Other);
        assert!(net.nodes[s].ep.node_stats().thin, "the responder is not thin");
        let (peer, to) = (net.nodes[s].node, net.nodes[s].addr);

        // The dialer's first flight arrives; what it sends after it, its Finish first, is held back.
        let (t0, ca) = (net.now, net.nodes[c].addr);
        net.nodes[c].connect(t0, peer, ALPN_A, to, Role::Other).unwrap();
        net.pump_all();
        let mark = net.captured.len();
        net.capture = true;
        net.loss = Some(Box::new(move |from, _, _| from == ca));
        net.run_for(40 * SEC_NS);
        net.loss = None;
        assert_eq!(
            net.nodes[c].count(|e| matches!(e, Event::Connected { .. })),
            1,
            "the dialer did not finish"
        );
        let finish = net.captured[mark..].iter().find(|x| x.0 == ca).unwrap().2.clone();
        assert_eq!(net.nodes[s].count(|e| matches!(e, Event::Incoming { .. })), 0);

        // The Finish arrives 40 s after the first flight.
        net.inject(ca, to, finish, 0);
        let end = net.now + 2 * SEC_NS;
        let late = net.run(end, |n| n.nodes[s].count(|e| matches!(e, Event::Incoming { .. })) == 1);
        assert!(
            late,
            "the responder dropped the session whose Finish came 40 s late: {:?}",
            net.nodes[s].ep.node_stats()
        );

        // A dialer whose Finish never arrives: the session is held for 60 s and then freed.
        let (t1, da) = (net.now, net.nodes[d].addr);
        net.nodes[d].connect(t1, peer, ALPN_A, to, Role::Other).unwrap();
        net.pump_all();
        net.loss = Some(Box::new(move |from, _, _| from == da));
        net.run_for(59 * SEC_NS);
        assert_eq!(
            net.nodes[s].ep.node_stats().half_open,
            1,
            "the unfinished session ended before 60 s"
        );
        net.run_for(2 * SEC_NS);
        assert_eq!(
            net.nodes[s].ep.node_stats().half_open,
            0,
            "the unfinished session outlived 60 s"
        );
    });
}

// ---- resumption Hellos and the cap ----

/// The host side of the big server: answers key requests with its key and allows every peer.
struct Host {
    kp: Keypair,
    prov: Caps,
    drbg: Drbg,
}

impl Host {
    fn new() -> Self {
        Self {
            kp: Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap(),
            prov: Caps(Software, true),
            drbg: Drbg::new(&[9; 32]),
        }
    }

    fn react(&mut self, ep: &mut BigEp, now: u64, ev: Event) {
        let rep = match ev {
            Event::AcpCheck { check, .. } => ep.command(now, Command::AcpAnswer { check, allow: true }),
            Event::KeyRequest { session } => {
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &self.kp)),
                    prekeys: None::<&SoftPrekeys<Caps>>,
                };
                let mut env = Env {
                    provider: &self.prov,
                    now,
                    drbg: &mut self.drbg,
                };
                let mut sig = [0u8; MAX_SIGNATURE_LEN];
                let response = match ep.query(Query::KeyRequest(session)) {
                    Answer::KeyRequest(req) => match soft.answer(&mut env, &req, &mut sig) {
                        KeyResponse::Signature(s) => KeyResponse::Signature(s),
                        KeyResponse::SharedSecret(s) => KeyResponse::SharedSecret(s),
                        KeyResponse::Failed => KeyResponse::Failed,
                    },
                    _ => return,
                };
                ep.command(now, Command::KeyResponse { session, response })
            }
            _ => return,
        };
        for e in rep
            .into_iter()
            .flat_map(|r| r.events.iter().copied().collect::<Vec<_>>())
        {
            self.react(ep, now, e);
        }
    }
}

/// One dialer on a `CoreNet` and the big server beside it, joined by hand: the dialer's datagrams to the server's
/// address go in, the server's go back.
struct Duo {
    net: CoreNet,
    srv: Box<BigEp>,
    addr: SocketAddr,
    host: Host,
    taken: usize,
}

impl Duo {
    fn new() -> Self {
        let mut net = CoreNet::new(MS_NS);
        net.add(2);
        net.capture = true;
        let (srv, addr) = big_server(net.now);
        Self {
            net,
            srv,
            addr,
            host: Host::new(),
            taken: 0,
        }
    }

    fn drive(&mut self, span: u64) {
        for _ in 0..span / MS_NS {
            self.net.run_for(MS_NS);
            let now = self.net.now;
            while let Some((from, to, d)) = self.net.captured.get(self.taken).cloned() {
                self.taken += 1;
                if to == self.addr {
                    self.srv.handle_datagram(now, self.addr, from, &mut d.clone());
                }
            }
            self.srv.handle_timeout(now);
            while let Some(e) = self.srv.poll_event() {
                self.host.react(&mut self.srv, now, e);
            }
            let mut buf = vec![0u8; 65_536];
            while let Some(t) = self.srv.poll_transmit(now, &mut buf) {
                for chunk in buf[..t.len].chunks(t.segment_size) {
                    self.net.inject(t.local, t.remote, chunk.to_vec(), 0);
                }
            }
        }
    }

    /// The dialer dials the server and the call returns the session once connected.
    fn dial(&mut self) -> vinc_core::SessionId {
        let id = LocalIdentity::from_keypair(&self.host.kp, KeyHandle(1)).unwrap();
        let (now, to) = (self.net.now, self.addr);
        let n0 = self.net.nodes[0].count(|e| matches!(e, Event::Connected { .. }));
        let rep = self.net.nodes[0]
            .connect(now, id.node_id(), ALPN_A, to, Role::Other)
            .unwrap();
        self.drive(300 * MS_NS);
        assert_eq!(
            self.net.nodes[0].count(|e| matches!(e, Event::Connected { .. })),
            n0 + 1,
            "no session"
        );
        self.net.nodes[0].session(&rep)
    }

    fn hang_up(&mut self, session: vinc_core::SessionId) {
        let now = self.net.now;
        self.net.nodes[0]
            .cmd(now, Command::Close { session, error: 0 })
            .unwrap();
        self.drive(2 * SEC_NS);
    }

    /// A full handshake that leaves the dialer holding a ticket, then the half-open table filled with forgeries.
    fn with_full_cap() -> Self {
        let mut d = Self::new();
        let first = d.dial();
        d.hang_up(first);
        let now = d.net.now;
        for i in 0..MAX_HALF_OPEN as u64 {
            feed(&mut d.srv, d.addr, now, 1000 + i, craft(1000 + i, 1, FULL_INITIAL_MIN));
        }
        assert_eq!(
            d.srv.node_stats().half_open,
            MAX_HALF_OPEN,
            "a forged full Initial must count"
        );
        d
    }
}

#[test]
fn a_flood_of_forged_initials_is_held_to_the_cap_and_forged_hellos_hold_nothing() {
    big_stack(|| {
        let now = 100 * SEC_NS;
        let (mut ep, addr) = big_server(now);
        for i in 0..(MAX_HALF_OPEN as u64 + 100) {
            feed(&mut ep, addr, now, i, craft(i + 1, 1, FULL_INITIAL_MIN));
        }
        let ns = ep.node_stats();
        assert_eq!((ns.half_open, ns.sessions), (MAX_HALF_OPEN, MAX_HALF_OPEN));
        assert_eq!(ns.dropped_in, 100);
        let (mut ep, addr) = big_server(now);
        for i in 0..(MAX_HALF_OPEN as u64 + 100) {
            feed(&mut ep, addr, now, i, craft(i + 1, 6, 300));
        }
        let ns = ep.node_stats();
        assert_eq!(
            (ns.half_open, ns.sessions, ns.dropped_in),
            (0, 0, MAX_HALF_OPEN as u64 + 100)
        );
    });
}

#[test]
fn a_genuine_resume_connects_while_the_cap_is_full_of_forgeries() {
    big_stack(|| {
        let mut d = Duo::with_full_cap();
        let _ = admissions(&mut d.srv);
        d.dial();
        let adm = admissions(&mut d.srv);
        assert_eq!(
            adm,
            [(true, true)],
            "the genuine Hello is exempt and nothing else starts a session"
        );
        assert_eq!(d.srv.node_stats().half_open, MAX_HALF_OPEN);
    });
}

#[test]
fn replays_of_a_used_ticket_get_a_reject_and_no_session() {
    big_stack(|| {
        let mut d = Duo::with_full_cap();
        let mark = d.net.captured.len();
        let second = d.dial();
        let hello = d.net.captured[mark..].iter().find(|c| c.1 == d.addr).unwrap().2.clone();
        d.hang_up(second);
        assert_eq!(
            d.srv.node_stats().sessions,
            MAX_HALF_OPEN,
            "the resumed session is gone"
        );
        let _ = admissions(&mut d.srv);
        let (now, ns0) = (d.net.now, d.srv.node_stats());
        let mut out = vec![0u8; 65_536];
        for i in 0..50u64 {
            feed(&mut d.srv, d.addr, now, 5000 + i, hello.clone());
            while d.srv.poll_transmit(now, &mut out).is_some() {}
        }
        let adm = admissions(&mut d.srv);
        assert!(adm.iter().all(|a| *a == (false, false)), "a replay was exempt: {adm:?}");
        let ns = d.srv.node_stats();
        assert_eq!(ns.half_open, MAX_HALF_OPEN);
        assert_eq!(ns.dropped_in, ns0.dropped_in);
        assert_eq!(
            (ns.stateless_rejects - ns0.stateless_rejects) + (ns.stateless_refused - ns0.stateless_refused),
            50
        );
    });
}

#[test]
fn a_hello_with_a_forged_binder_is_not_exempt() {
    big_stack(|| {
        let mut d = Duo::with_full_cap();
        let mark = d.net.captured.len();
        let session = d.dial();
        let mut hello = d.net.captured[mark..].iter().find(|c| c.1 == d.addr).unwrap().2.clone();
        // The credit record is the last field of the message and is part of what the binder covers.
        *hello.last_mut().unwrap() ^= 1;
        d.hang_up(session);
        let _ = admissions(&mut d.srv);
        feed(&mut d.srv, d.addr, d.net.now, 7000, hello);
        assert_eq!(admissions(&mut d.srv), [(false, false)]);
    });
}

#[test]
fn a_charge_near_the_top_of_the_range_saturates_instead_of_overflowing() {
    use vinc_core::Ledger;
    let v: SocketAddr = "10.9.9.8:1000".parse().unwrap();
    let mut l = Ledger::new(1);
    l.on_receive(v, u64::MAX);
    assert!(l.allow_send(v, u64::MAX - 28));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| l.allow_send(v, 0)));
    assert_eq!(r.ok(), Some(true), "the second charge must not overflow the total");
    assert_eq!(l.get(&v).unwrap().tx, u64::MAX);
}

#[test]
fn datagrams_out_counts_the_datagrams_that_left_and_no_size_probe_is_built_for_a_held_address() {
    big_stack(|| {
        let (mut net, s, hello) = spoofable_resume();
        let x: SocketAddr = "10.9.9.9:1000".parse().unwrap();
        let to = net.nodes[s].addr;
        let out0 = net.nodes[s].ep.node_stats().datagrams_out;
        let held0 = net.nodes[s].ep.node_stats().held_by_ledger;
        net.inject(x, to, hello, 0);
        net.run_for(5 * SEC_NS);
        let left = net.tapped.iter().filter(|t| t.2 == x).count() as u64;
        let ns = net.nodes[s].ep.node_stats();
        assert!(left >= 1);
        assert_eq!(ns.datagrams_out - out0, left, "a refused datagram never counts as out");
        assert_eq!(
            ns.held_by_ledger, held0,
            "the server built a size probe for an address the ledger holds"
        );
    });
}

// ---- first packets the responder will reject take no half-open slot ----

/// A long handshake datagram of at least `len` bytes (zero padded) that carries the whole `message` as its first
/// fragment, as a dialer's first packet does.
fn first_datagram(odcid: u64, message: &[u8], len: usize) -> Vec<u8> {
    let dcid = ConnId::new(&odcid.to_be_bytes()).unwrap();
    let mut head = [0u8; 16];
    let mut w = Writer::new(&mut head);
    w.put_varint(message.len() as u64).unwrap();
    w.put_varint(0).unwrap();
    let mut body = w.written().to_vec();
    body.extend_from_slice(message);
    let d = forge_packet(dcid, &body);
    if d.len() >= len {
        return d;
    }
    body.resize(body.len() + len - d.len(), 0);
    forge_packet(dcid, &body)
}

/// A well-formed resumption Hello for a ticket nobody issued: random ticket id, key and binder.
fn forged_hello(seed: u64) -> Vec<u8> {
    let mut rng = SplitMix64::new(seed);
    let (mut tid, mut e, mut binder) = ([0u8; 16], [0u8; 32], [0u8; 32]);
    rng.fill(&mut tid);
    rng.fill(&mut e);
    rng.fill(&mut binder);
    let cid = ConnId::new(&[1, 2, 3, 4]).unwrap();
    let hello = ResumeHello {
        version: VERSION,
        dcid: cid,
        scid: cid,
        alpn: ALPN_A,
        aead: Aead::ChaCha20Poly1305,
        tid,
        e,
        binder,
        credit: CreditRecord::NONE,
    };
    let mut buf = [0u8; 256];
    let mut w = Writer::new(&mut buf);
    hello.write(&mut w).unwrap();
    w.written().to_vec()
}

/// A well-formed short Initial that names a prekey nobody sent: a random id.
fn unknown_key_initial(seed: u64) -> Vec<u8> {
    let mut rng = SplitMix64::new(seed);
    let (mut e, mut key_id) = ([0u8; 32], [0u8; 32]);
    rng.fill(&mut e);
    rng.fill(&mut key_id);
    let cid = ConnId::new(&[1, 2, 3, 4]).unwrap();
    let initial = Initial {
        version: VERSION,
        dcid: cid,
        scid: cid,
        alpn: ALPN_A,
        aead_offer: AeadSet::from_bits(1).unwrap(),
        e,
        prekey: PrekeyField::Hash(&key_id),
        credit: CreditRecord::NONE,
    };
    let mut buf = [0u8; 256];
    let mut w = Writer::new(&mut buf);
    initial.write(&mut w).unwrap();
    w.written().to_vec()
}

/// What the endpoint sent and received per address while `flood` fed it: `(bytes received, bytes sent with the 28
/// bytes of headers each datagram carries)`.
type Tally = HashMap<SocketAddr, (u64, u64)>;

/// Feed the endpoint of `d` the datagram `make(i)` from its own address for each `i` of `ids`, taking what it sends
/// after every datagram as a host does.
fn flood(d: &mut Duo, ids: std::ops::Range<u64>, make: &dyn Fn(u64) -> Vec<u8>, tally: &mut Tally) {
    let now = d.net.now;
    let mut out = vec![0u8; 65_536];
    for i in ids {
        let mut dgram = make(i);
        let from: SocketAddr = ([10, 1, (i >> 8) as u8, i as u8], 9).into();
        tally.entry(from).or_default().0 += dgram.len() as u64;
        d.srv.handle_datagram(now, d.addr, from, &mut dgram);
        while let Some(t) = d.srv.poll_transmit(now, &mut out) {
            for seg in out[..t.len].chunks(t.segment_size) {
                tally.entry(t.remote).or_default().1 += seg.len() as u64 + 28;
            }
        }
    }
}

/// Every forged address was sent at most three times what it sent.
fn assert_within_three_times(tally: &Tally) {
    for (addr, (rx, tx)) in tally {
        assert!(*tx <= 3 * rx, "{addr} was sent {tx} bytes for {rx}");
    }
}

#[test]
fn ten_thousand_forged_resumption_hellos_leave_the_half_open_table_empty() {
    big_stack(|| {
        let mut d = Duo::new();
        let mut tally = Tally::new();
        // Half are 20-byte datagrams that start a Hello, half whole Hellos of a ticket nobody issued.
        let hello = |i: u64| {
            if i.is_multiple_of(2) {
                first_datagram(i + 1, &[6], 20)
            } else {
                first_datagram(i + 1, &forged_hello(i), 0)
            }
        };
        flood(&mut d, 0..5_000, &hello, &mut tally);
        assert_eq!(
            d.srv.node_stats().half_open,
            0,
            "forged Hellos hold half-open slots: {:?}",
            d.srv.node_stats()
        );
        // A genuine dial in the middle of the flood completes.
        d.dial();
        flood(&mut d, 5_000..10_000, &hello, &mut tally);
        let ns = d.srv.node_stats();
        assert_eq!((ns.half_open, ns.sessions), (0, 1), "{ns:?}");
        assert_within_three_times(&tally);
        assert_eq!(ns.first_too_short, 5_000, "{ns:?}");
        assert_eq!((ns.stateless_rejects, ns.stateless_refused), (5_000, 0), "{ns:?}");
    });
}

#[test]
fn ten_thousand_short_initials_with_unknown_keys_leave_the_half_open_table_empty() {
    big_stack(|| {
        let mut d = Duo::new();
        let mut tally = Tally::new();
        // Half are as small as a short Initial may be, half larger.
        let short = |i: u64| {
            let len = if i.is_multiple_of(2) { SHORT_INITIAL_MIN } else { 900 };
            first_datagram(i + 1, &unknown_key_initial(i), len)
        };
        flood(&mut d, 0..5_000, &short, &mut tally);
        assert_eq!(
            d.srv.node_stats().half_open,
            0,
            "short Initials of unknown keys hold half-open slots: {:?}",
            d.srv.node_stats()
        );
        d.dial();
        flood(&mut d, 5_000..10_000, &short, &mut tally);
        let ns = d.srv.node_stats();
        assert_eq!((ns.half_open, ns.sessions), (0, 1), "{ns:?}");
        assert_within_three_times(&tally);
    });
}

#[test]
fn a_hello_with_a_wrong_binder_gets_no_answer_and_no_session_and_the_genuine_hello_resumes() {
    big_stack(|| {
        let mut d = Duo::new();
        let first = d.dial();
        d.hang_up(first);
        // The next dial resumes; its flight is kept from the server for now.
        let mark = d.net.captured.len();
        let id = LocalIdentity::from_keypair(&d.host.kp, KeyHandle(1)).unwrap();
        let (now, to) = (d.net.now, d.addr);
        d.net.nodes[0]
            .connect(now, id.node_id(), ALPN_A, to, Role::Other)
            .unwrap();
        d.net.run_for(10 * MS_NS);
        d.taken = d.net.captured.len();
        let flight: Vec<&[u8]> = d.net.captured[mark..]
            .iter()
            .filter(|c| c.1 == d.addr)
            .map(|c| c.2.as_slice())
            .collect();
        let mut message = first_message(flight.iter().copied()).unwrap();
        assert_eq!(MessageType::of(&message).unwrap(), MessageType::ResumeHello);
        let dcid = LongHeader::parse(flight[0]).unwrap().0.dcid;
        // The credit record ends the message and the binder covers it: the ticket opens, the binder does not.
        *message.last_mut().unwrap() ^= 1;
        let (sessions, now) = (d.srv.node_stats().sessions, d.net.now);
        let x: SocketAddr = "10.9.9.9:1000".parse().unwrap();
        d.srv
            .handle_datagram(now, d.addr, x, &mut forge_message(dcid, &message));
        let mut out = vec![0u8; 65_536];
        assert!(
            d.srv.poll_transmit(now, &mut out).is_none(),
            "a wrong binder was answered"
        );
        let ns = d.srv.node_stats();
        assert_eq!(
            (ns.half_open, ns.sessions),
            (0, sessions),
            "a wrong binder left a session: {ns:?}"
        );
        // The ticket is still there: the genuine Hello resumes.
        d.taken = mark;
        d.drive(300 * MS_NS);
        let ns = d.srv.node_stats();
        assert_eq!(
            (ns.sessions, ns.stateless_rejects),
            (1, 0),
            "the genuine resumption did not make a session: {ns:?}"
        );
        assert_eq!(d.srv.node_stats().half_open, 0);
    });
}

/// The half-open session made at `now` by a first flight that never completes is there at `limit` and gone one tick
/// past it.
fn assert_ends_strictly_past(ep: &mut BigEp, addr: SocketAddr, now: u64, limit: u64, what: &str) {
    feed(ep, addr, now, 9_000, craft(9_000, 1, FULL_INITIAL_MIN));
    assert_eq!(ep.node_stats().half_open, 1, "{what}: no half-open session");
    ep.handle_timeout(now + limit - 1);
    assert_eq!(ep.node_stats().half_open, 1, "{what}: gone before the limit");
    ep.handle_timeout(now + limit);
    assert_eq!(ep.node_stats().half_open, 1, "{what}: gone at the limit itself");
    ep.handle_timeout(now + limit + 1);
    assert_eq!(
        ep.node_stats().half_open,
        0,
        "{what}: still there one tick past the limit"
    );
}

#[test]
fn a_half_open_session_ends_strictly_past_30_s() {
    big_stack(|| {
        let now = 100 * SEC_NS;
        let (mut ep, addr) = big_server(now);
        assert_ends_strictly_past(&mut ep, addr, now, 30 * SEC_NS, "30 s");
    });
}

#[test]
fn a_half_open_session_of_a_thin_node_ends_strictly_past_60_s() {
    big_stack(|| {
        // 150 ms each way: the node measures a 300 ms round trip on its own dial, so it is thin.
        let mut net = CoreNet::new(150 * MS_NS);
        let (s, w) = (net.add(1), net.add(2));
        net.connect_pair(s, w, ALPN_A, Role::Other);
        assert!(net.nodes[s].ep.node_stats().thin, "the node is not thin");
        let (addr, now) = (net.nodes[s].addr, net.now);
        // The first flight never completes, so the responder never answers and its life is the node's own limit.
        let ep = &mut net.nodes[s].ep;
        ep.handle_datagram(
            now,
            addr,
            "10.9.9.9:1000".parse().unwrap(),
            &mut craft(9_000, 1, FULL_INITIAL_MIN),
        );
        assert_eq!(ep.node_stats().half_open, 1, "60 s: no half-open session");
        ep.handle_timeout(now + 60 * SEC_NS - 1);
        assert_eq!(ep.node_stats().half_open, 1, "60 s: gone before the limit");
        ep.handle_timeout(now + 60 * SEC_NS);
        assert_eq!(ep.node_stats().half_open, 1, "60 s: gone at the limit itself");
        ep.handle_timeout(now + 60 * SEC_NS + 1);
        assert_eq!(
            ep.node_stats().half_open,
            0,
            "60 s: still there one tick past the limit"
        );
    });
}
