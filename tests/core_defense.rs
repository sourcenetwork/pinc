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

use std::net::SocketAddr;

use vinc_core::{
    Answer, Command, Endpoint, EndpointConfig, Event, LEDGER_ENTRIES, MAX_HALF_OPEN, Query, Role, Slot, TraceEvent,
};
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use vinc_security::{ConnId, Env, KeyHandle, KeyResponse, LocalIdentity, SoftKeys, SoftPrekeys};
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
            feed(&mut d.srv, d.addr, now, 1000 + i, craft(1000 + i, 6, 300));
        }
        assert_eq!(
            d.srv.node_stats().half_open,
            MAX_HALF_OPEN,
            "a forged resumption Hello must count"
        );
        d
    }
}

#[test]
fn a_flood_of_forged_resume_hellos_is_held_to_the_cap() {
    big_stack(|| {
        let now = 100 * SEC_NS;
        let (mut ep, addr) = big_server(now);
        for i in 0..(MAX_HALF_OPEN as u64 + 100) {
            feed(&mut ep, addr, now, i, craft(i + 1, 6, 300));
        }
        let ns = ep.node_stats();
        assert_eq!((ns.half_open, ns.sessions), (MAX_HALF_OPEN, MAX_HALF_OPEN));
        assert_eq!(ns.dropped_in, 100);
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
fn replays_of_a_used_ticket_are_held_to_the_cap() {
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
        let (now, dropped) = (d.net.now, d.srv.node_stats().dropped_in);
        for i in 0..50u64 {
            feed(&mut d.srv, d.addr, now, 5000 + i, hello.clone());
        }
        let adm = admissions(&mut d.srv);
        assert!(adm.iter().all(|a| *a == (false, false)), "a replay was exempt: {adm:?}");
        assert_eq!(d.srv.node_stats().half_open, MAX_HALF_OPEN);
        assert_eq!(d.srv.node_stats().dropped_in, dropped + 50);
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
fn datagrams_out_counts_the_datagrams_that_left_and_held_counts_the_refusals() {
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
        assert!(ns.held_by_ledger > held0, "the refusals are still counted");
    });
}
