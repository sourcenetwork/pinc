//! The scenarios of `trace_handshake.rs`: every world is one run of the real machines, asserted here and recorded by
//! the [`Sim`].
use vinc_security::message::{Initial, ResumeHello};
use vinc_security::responder::{LATE_INITIAL_BUDGET, RESEND_BUDGET};
use vinc_security::{ConnId, Failure};

use crate::sim::{Ids, LH, LR, Sim, ex};
use crate::tamper::{agree, flip_field, kinds, malformed};

/// The trace under construction: the ids, the lines and the world counter.
#[derive(Default)]
pub struct Ctx {
    pub ids: Ids,
    pub trace: String,
    pub wid: u32,
}

impl Ctx {
    /// Run `f` in a new world and keep its lines.
    pub fn world(&mut self, ia: bool, f: impl FnOnce(&mut Sim<'_>)) {
        self.wid += 1;
        let mut sim = Sim::new(&mut self.ids, self.wid, ia);
        f(&mut sim);
        sim.finish(&mut self.trace);
    }
}

/// A world that is run and asserted but not recorded (the model cannot state its input).
fn unrecorded(f: impl FnOnce(&mut Sim<'_>)) {
    let mut ids = Ids::default();
    let mut sim = Sim::new(&mut ids, 0, false);
    f(&mut sim);
}

fn is_dropped(r: &Result<(), Failure>) -> bool {
    matches!(r, Err(f) if !f.is_fatal())
}

pub fn scenarios(c: &mut Ctx) {
    base(c);
    retransmits(c);
    attacker(c);
    expiry(c);
    fallback(c);
    late_reply(c);
    resent(c);
    store(c);
    misc();
}

/// The scenarios of the handshake itself: full, short, resumed, rejected, with key requests that fail.
fn base(c: &mut Ctx) {
    for alpn in [1, 2] {
        // full handshake
        c.world(false, |sim| {
            let (is, first) = sim.start(1, alpn, false, false);
            sim.drive(is, first, None, 1, 1);
            let (ei, er) = (sim.ests[&('I', 1)].clone(), sim.ests[&('R', 1)].clone());
            agree(&ei, &er);
            assert!(!ei.resumed && er.tickets.entries().len() == 1);
            sim.accept(is, 1);
        });
        // resumption with 0-RTT keys, twice
        c.world(false, |sim| {
            sim.setup_full(alpn);
            let (is, first) = sim.start(1, alpn, false, true);
            sim.drive(is, first, None, 1, 1);
            let (ei, er) = (sim.ests[&('I', is)].clone(), sim.ests[&('R', 2)].clone());
            agree(&ei, &er);
            assert!(ei.resumed);
            sim.accept(is, 2);
            let (is2, first2) = sim.start(1, alpn, false, true);
            sim.drive(is2, first2, None, 1, 1);
            assert!(sim.ests[&('I', is2)].resumed);
        });
    }
    // short Initial with a prekey hit: the cache was filled by an earlier handshake
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, true, false);
        assert_eq!(first[0][0], 2);
        let log = sim.drive(is, first, None, 1, 1);
        assert_eq!(kinds(&log), vec![2, 4, 5]);
    });
    // short Initial with a miss: reject, then the full Initial
    c.world(false, |sim| {
        let (is, first) = sim.start(1, 1, true, false);
        let log = sim.drive(is, first, None, 1, 1);
        assert_eq!(kinds(&log), vec![2, 3, 1, 4, 5]);
        agree(&sim.ests[&('I', 1)], &sim.ests[&('R', 1)]);
    });
    // a reject made by another responder (with the right echo) falls the initiator back, a wrong echo is dropped
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, true, false);
        let rs2 = sim.r_new(2);
        let (_, d) = sim.r_recv(rs2, &ex(&first[0]));
        assert_eq!(d.sends[0][0], 3);
        let rej = d.sends[0].clone();
        let (r, _) = sim.i_recv(is, &flip_field(&rej, "echo"));
        assert!(is_dropped(&r));
        let (r, d) = sim.i_recv(is, &ex(&rej));
        assert!(r.is_ok() && d.sends[0][0] == 1);
        // the same reject again: the initiator already moved to the full form
        assert!(is_dropped(&sim.i_recv(is, &ex(&rej)).0));
        sim.drive(is, d.sends.clone(), None, 1, 1);
        agree(&sim.ests[&('I', is)], &sim.ests[&('R', sim.resps.len())]);
    });
    // the same Initial twice, and a deferred key request: nothing changes while the host has not answered
    c.world(false, |sim| {
        let (is, first) = sim.start(1, 1, false, false);
        let rs = sim.r_new(1);
        let (_, d) = sim.r_recv(rs, &ex(&first[0]));
        assert!(d.req.is_some() && d.sends.is_empty());
        let (r, d2) = sim.r_recv(rs, &ex(&first[0]));
        assert!(is_dropped(&r) && d2.req.is_none() && d2.sends.is_empty());
        let (r, d) = sim.r_key(rs, true);
        assert!(r.is_ok());
        let reply = d.sends[0].clone();
        // a retransmitted Initial after the Reply gets the same Reply again
        let (_, d3) = sim.r_recv(rs, &ex(&first[0]));
        assert_eq!(d3.sends, vec![reply.clone()]);
        let (r, d) = sim.i_recv(is, &ex(&reply));
        assert!(r.is_ok() && d.req.is_some_and(|q| q.0 == "decap"));
        assert!(is_dropped(&sim.i_recv(is, &ex(&reply)).0));
        let (r, d) = sim.i_key(is, true);
        assert!(r.is_ok() && d.req.is_some_and(|q| q.0 == "sign"));
        assert!(is_dropped(&sim.i_recv(is, &ex(&reply)).0));
        let (r, d) = sim.i_key(is, true);
        assert!(r.is_ok() && d.est.is_some());
        let fin = d.sends[0].clone();
        let (r, d) = sim.r_recv(rs, &ex(&fin));
        assert!(r.is_ok() && d.est.is_some());
        // a second Finish and a second Initial reach a finished session
        assert!(is_dropped(&sim.r_recv(rs, &ex(&fin)).0));
        assert!(is_dropped(&sim.r_recv(rs, &ex(&first[0])).0));
        agree(&sim.ests[&('I', is)], &sim.ests[&('R', rs)]);
        // messages of the wrong kind for the machine are dropped
        assert!(is_dropped(&sim.i_recv(is, &ex(&first[0])).0));
        assert!(is_dropped(&sim.i_recv(is, &ex(&fin)).0));
        assert!(is_dropped(&sim.r_recv(rs, &ex(&reply)).0));
    });
    // key operations that fail: the responder's signature, the initiator's decapsulation and signature
    for stage in 0..3 {
        c.world(false, |sim| {
            let (is, first) = sim.start(1, 1, false, false);
            let rs = sim.r_new(1);
            let _ = sim.r_recv(rs, &ex(&first[0]));
            if stage == 0 {
                let (r, d) = sim.r_key(rs, false);
                assert!(r.is_err() && d.failed.is_some());
                assert!(is_dropped(&sim.r_recv(rs, &ex(&first[0])).0));
                // a refusal when nothing is outstanding is dropped
                assert!(is_dropped(&sim.r_key(rs, false).0));
            } else {
                let reply = sim.r_key(rs, true).1.sends[0].clone();
                let _ = sim.i_recv(is, &ex(&reply));
                if stage == 1 {
                    let (r, d) = sim.i_key(is, false);
                    assert!(r.is_err() && d.failed.is_some());
                } else {
                    let _ = sim.i_key(is, true);
                    let (r, d) = sim.i_key(is, false);
                    assert!(r.is_err() && d.failed.is_some());
                }
                assert!(is_dropped(&sim.i_recv(is, &ex(&reply)).0));
                assert!(is_dropped(&sim.i_key(is, false).0));
            }
        });
    }
    // a refusal after a completed handshake is dropped on both sides
    c.world(false, |sim| {
        let (is, first) = sim.start(1, 1, false, false);
        sim.drive(is, first, None, 1, 1);
        assert!(is_dropped(&sim.i_key(is, false).0));
        assert!(is_dropped(&sim.r_key(1, false).0));
    });
    // a replayed Hello is rejected by a fresh responder, a Hello with a wrong binder does not burn the ticket
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, false, true);
        let hello = first[0].clone();
        let bad = flip_field(&hello, "binder");
        let rs = sim.r_new(1);
        let (r, d) = sim.r_recv(rs, &bad);
        assert!(r.is_ok() && d.sends[0][0] == 8 && d.early.is_none());
        let rs2 = sim.r_new(1);
        let (r, d) = sim.r_recv(rs2, &ex(&hello));
        assert!(r.is_ok() && d.early.is_some() && d.est.is_some());
        let reply = d.sends[0].clone();
        let rs3 = sim.r_new(1);
        let (r, d) = sim.r_recv(rs3, &ex(&hello));
        assert!(r.is_ok() && d.sends[0][0] == 8 && d.early.is_none());
        let rej = d.sends[0].clone();
        // the reject reaches the initiator before the reply: it falls back, and the late reply is dropped
        let (r, d) = sim.i_recv(is, &ex(&rej));
        assert!(r.is_ok() && d.rejected && d.sends[0][0] == 1);
        assert!(is_dropped(&sim.i_recv(is, &ex(&reply)).0));
        sim.drive(is, d.sends.clone(), None, 1, 1);
    });
    // resumption rejected (the responder has no such ticket): the full handshake follows
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, false, true);
        let log = sim.drive(is, first, None, 1, 2);
        assert_eq!(kinds(&log), vec![6, 8, 1, 4, 5]);
        assert!(!sim.ests[&('I', is)].resumed);
        // the reject from a responder of another session, forged and exact, once the initiator moved on
        assert!(is_dropped(&sim.i_recv(is, &ex(&log[1])).0));
    });
    // garbage reaches every state of both machines and is dropped
    c.world(false, |sim| {
        let junk = [vec![], vec![0xff], vec![1, 1, 2], vec![6; 40], vec![7, 0, 0]];
        let (is, first) = sim.start(1, 1, false, false);
        let rs = sim.r_new(1);
        for j in &junk {
            assert!(is_dropped(&sim.r_recv(rs, &malformed(j)).0));
            assert!(is_dropped(&sim.i_recv(is, &malformed(j)).0));
        }
        let _ = sim.r_recv(rs, &ex(&first[0]));
        let reply = sim.r_key(rs, true).1.sends[0].clone();
        for j in &junk {
            assert!(is_dropped(&sim.r_recv(rs, &malformed(j)).0));
        }
        let _ = sim.i_recv(is, &ex(&reply));
        for j in &junk {
            assert!(is_dropped(&sim.i_recv(is, &malformed(j)).0));
        }
        let _ = sim.i_key(is, true);
        let _ = sim.i_key(is, true);
        for j in &junk {
            assert!(is_dropped(&sim.i_recv(is, &malformed(j)).0));
        }
    });
}

/// Lost flights sent again: the short Initial (the full prekey on the third send), the full Initial, the Reply
/// and the Finish, until the transport sheds them.
fn retransmits(c: &mut Ctx) {
    // the short Initial of a cache hit, sent again; the third send is the full form
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, true, false);
        let rs = sim.r_new(1);
        assert!(sim.r_recv(rs, &ex(&first[0])).1.req.is_some());
        let reply = sim.r_key(rs, true).1.sends[0].clone();
        let sends: Vec<Vec<u8>> = (0..5).map(|_| sim.i_retx(is).sends.remove(0)).collect();
        assert_eq!(kinds(&sends), vec![2, 1, 2, 2, 1], "sends 2 to 6");
        // the full form of the same Initial reaches the responder that has the Reply: the Reply again
        let (r, d) = sim.r_recv(rs, &ex(&sends[1]));
        assert!(r.is_ok() && d.sends == vec![reply.clone()]);
        assert_eq!(sim.r_retx(rs).sends, vec![reply.clone()]);
        // shed does not drop the Reply of a responder that still waits for the Finish
        sim.r_shed(rs);
        assert_eq!(sim.r_retx(rs).sends, vec![reply.clone()]);
        // the loss timers while the machine waits for the host
        assert!(sim.i_recv(is, &ex(&reply)).1.req.is_some());
        assert!(sim.i_retx(is).sends.is_empty());
        assert!(sim.i_key(is, true).1.req.is_some());
        assert!(sim.i_retx(is).sends.is_empty());
        let (_, d) = sim.i_key(is, true);
        let fin = d.sends[0].clone();
        // the Finish is sent again until the transport sheds it
        assert_eq!(sim.i_retx(is).sends, vec![fin.clone()]);
        assert!(sim.r_recv(rs, &ex(&fin)).1.est.is_some());
        assert!(is_dropped(&sim.r_recv(rs, &ex(&fin)).0));
        assert_eq!(sim.i_retx(is).sends, vec![fin]);
        assert!(sim.r_retx(rs).sends.is_empty());
        sim.i_shed(is);
        assert!(sim.i_retx(is).sends.is_empty());
        sim.r_shed(rs);
        sim.accept(is, rs);
    });
    // a short Initial that misses: sent again, then rejected; the full Initial is sent again after the reject
    c.world(false, |sim| {
        let (is, first) = sim.start(1, 1, true, false);
        let rs = sim.r_new(1);
        let (_, d) = sim.r_recv(rs, &ex(&first[0]));
        assert_eq!(d.sends[0][0], 3);
        let rej = d.sends[0].clone();
        assert_eq!(sim.i_retx(is).sends[0][0], 2);
        let third = sim.i_retx(is).sends.remove(0);
        assert_eq!(third[0], 1);
        // the full form of the same Initial reaches the responder that rejected the short one
        let rs2 = sim.r_new(1);
        assert!(sim.r_recv(rs2, &ex(&third)).1.req.is_some());
        let (_, d) = sim.i_recv(is, &ex(&rej));
        let full = d.sends[0].clone();
        assert_eq!(full[0], 1);
        assert_eq!(sim.i_retx(is).sends, vec![full.clone()]);
        sim.drive(is, vec![full], None, 1, 1);
        agree(&sim.ests[&('I', is)], &sim.ests[&('R', sim.resps.len())]);
    });
    // the full Initial sent again to a responder that is signing, and to one that has sent the Reply
    c.world(false, |sim| {
        let (is, first) = sim.start(1, 1, false, false);
        let again = sim.i_retx(is).sends;
        assert_eq!(again, first);
        assert!(sim.i_retx(is).sends == first);
        let rs = sim.r_new(1);
        assert!(sim.r_recv(rs, &ex(&first[0])).1.req.is_some());
        assert!(is_dropped(&sim.r_recv(rs, &ex(&again[0])).0));
        assert!(sim.r_retx(rs).sends.is_empty(), "nothing to send while the host signs");
        let reply = sim.r_key(rs, true).1.sends[0].clone();
        assert_eq!(sim.r_retx(rs).sends, vec![reply.clone()]);
        assert_eq!(sim.r_recv(rs, &ex(&again[0])).1.sends, vec![reply.clone()]);
        let (r, _) = sim.i_recv(is, &ex(&reply));
        assert!(r.is_ok());
        assert!(sim.i_retx(is).sends.is_empty());
        let _ = sim.i_key(is, true);
        let _ = sim.i_key(is, true);
        let fin = sim.i_retx(is).sends.remove(0);
        assert!(sim.r_recv(rs, &ex(&fin)).1.est.is_some());
        assert!(sim.r_retx(rs).sends.is_empty());
    });
}

/// An attacker's identity as the dialed peer and as the dialing node.
fn attacker(c: &mut Ctx) {
    // the attacker's node as the dialed peer: full handshake, then resumption with the ticket it issued
    for alpn in [1, 2] {
        c.world(false, |sim| {
            let (is, first) = sim.start(3, alpn, false, false);
            let log = sim.drive(is, first, None, 3, 3);
            assert_eq!(kinds(&log), vec![1, 4, 5]);
            sim.accept(is, 1);
            let (is2, first2) = sim.start(3, alpn, false, true);
            assert_eq!(first2[0][0], 6);
            let log = sim.drive(is2, first2, None, 3, 3);
            assert_eq!(kinds(&log), vec![6, 7]);
            assert!(sim.ests[&('I', is2)].resumed);
            sim.accept(is2, 2);
            // the short form against the attacker's cache
            let (is3, first3) = sim.start(3, alpn, true, false);
            assert_eq!(first3[0][0], 2);
            sim.drive(is3, first3, None, 3, 3);
        });
    }
    // the initiator refuses a responder that is not the node it dialed
    for (peer, to) in [(1, 3), (3, 1), (1, 2), (2, 1)] {
        c.world(false, |sim| {
            let (is, first) = sim.start(peer, 1, false, false);
            sim.drive(is, first, None, to, to);
            assert!(sim.ests.is_empty(), "neither side is established");
        });
    }
    // the dialing node is the attacker's identity
    c.world(true, |sim| {
        let (is, first) = sim.start(1, 1, false, false);
        sim.drive(is, first, None, 1, 1);
        sim.accept(is, 1);
        let (is2, first2) = sim.start(1, 1, false, true);
        sim.drive(is2, first2, None, 1, 1);
        assert!(sim.ests[&('I', is2)].resumed);
        let (is3, first3) = sim.start(1, 2, true, false);
        sim.drive(is3, first3, None, 1, 1);
        // dialing the other honest node: the full handshake there
        let (is4, first4) = sim.start(2, 1, false, false);
        sim.drive(is4, first4, None, 2, 2);
        assert!(sim.ests.contains_key(&('I', is4)));
    });
}

/// Ticket expiry and the bounded stores.
fn expiry(c: &mut Ctx) {
    // the server store holds two tickets: the third session evicts the oldest, and a Hello on it is rejected
    c.world(false, |sim| {
        sim.life = 1000;
        sim.setup_full(1);
        for _ in 0..2 {
            let (is, first) = sim.start(1, 1, false, false);
            sim.drive(is, first, None, 1, 1);
        }
        let (is, first) = sim.start(1, 1, false, true);
        assert_eq!(first[0][0], 6);
        let log = sim.drive(is, first, None, 1, 1);
        assert_eq!(kinds(&log), vec![6, 8, 1, 4, 5]);
    });
    // a Hello on a ticket the server holds expired is rejected and the expired slot is removed
    c.world(false, |sim| {
        sim.life = 100;
        let (is1, first) = sim.start(1, 1, false, false);
        sim.drive(is1, first, None, 1, 1);
        sim.advance(60);
        sim.life = 10;
        let (is2, first) = sim.start(1, 1, false, false);
        sim.drive(is2, first, None, 1, 1);
        sim.advance(5);
        sim.accept(is2, 2);
        sim.advance(7);
        let (is3, first) = sim.start(1, 1, false, true);
        assert_eq!(first[0][0], 6, "the client still holds the ticket");
        let log = sim.drive(is3, first, None, 1, 1);
        assert_eq!(kinds(&log), vec![6, 8, 1, 4, 5]);
        sim.life = 100;
        let (is4, first) = sim.start(1, 1, false, false);
        sim.drive(is4, first, None, 1, 1);
    });
    // a full store evicts an expired ticket before the oldest one
    c.world(false, |sim| {
        sim.life = 100;
        sim.setup_full(1);
        sim.advance(10);
        sim.life = 10;
        let (is, first) = sim.start(1, 1, false, false);
        sim.drive(is, first, None, 1, 1);
        sim.advance(15);
        sim.life = 100;
        let (is, first) = sim.start(1, 1, false, false);
        sim.drive(is, first, None, 1, 1);
        let (is, first) = sim.start(1, 1, false, true);
        let log = sim.drive(is, first, None, 1, 1);
        assert_eq!(kinds(&log), vec![6, 7], "the oldest ticket survived");
    });
    // the client store: one ticket per peer, the newest replaces the older, a third peer evicts the oldest,
    // an expired ticket and a ticket of another ALPN are not taken
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, false, false);
        sim.drive(is, first, None, 1, 1);
        sim.accept(is, sim.resps.len());
        assert_eq!(sim.client.len(), 1);
        // the ticket taken is the newer one of the peer
        let (is, first) = sim.start(1, 1, false, true);
        assert_eq!(first[0][0], 6);
        let log = sim.drive(is, first, None, 1, 1);
        assert_eq!(kinds(&log), vec![6, 7]);
        sim.accept(is, sim.resps.len());
        let (is, first) = sim.start(2, 1, false, false);
        sim.drive(is, first, None, 2, 2);
        sim.accept(is, sim.resps.len());
        let (is, first) = sim.start(3, 1, false, false);
        sim.drive(is, first, None, 3, 3);
        sim.accept(is, sim.resps.len());
        assert_eq!(sim.client.len(), 2);
        let (is, first) = sim.start(1, 1, false, true);
        assert_eq!(first[0][0], 1, "the first peer's ticket was evicted");
        sim.drive(is, first, None, 1, 1);
        let (is, first) = sim.start(2, 2, false, true);
        assert_eq!(first[0][0], 1, "a ticket of another ALPN is not taken");
        sim.drive(is, first, None, 2, 2);
        let (is, first) = sim.start(2, 1, false, true);
        assert_eq!(first[0][0], 6);
        sim.drive(is, first, None, 2, 2);
        sim.accept(is, sim.resps.len());
        sim.advance(61);
        let (is, first) = sim.start(3, 1, false, true);
        assert_eq!(first[0][0], 1, "an expired ticket is not taken");
        sim.drive(is, first, None, 3, 3);
    });
    // three tickets per session: all three are issued, two fit the store, the last one is the one the client keeps
    c.world(false, |sim| {
        sim.tps = 3;
        let (is, first) = sim.start(1, 1, false, false);
        sim.drive(is, first, None, 1, 1);
        assert_eq!(sim.ests[&('R', 1)].tickets.entries().len(), 3);
        sim.accept(is, 1);
        assert_eq!(sim.client.len(), 1);
        sim.tps = 1;
        let (is2, first2) = sim.start(1, 1, false, true);
        let log = sim.drive(is2, first2, None, 1, 1);
        assert_eq!(kinds(&log), vec![6, 7]);
        sim.accept(is2, 2);
    });
}

fn hello_of(m: &[u8]) -> ResumeHello<'_> {
    ResumeHello::parse(m).unwrap()
}

/// A Hello that stays unanswered, or is rejected, gives way to a full handshake.
fn fallback(c: &mut Ctx) {
    // unanswered: the Hello again, then the third send is a full Initial under the same destination id
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, false, true);
        let hello = first[0].clone();
        assert_eq!(sim.i_retx(is).sends, vec![hello.clone()]);
        let d = sim.i_retx(is);
        assert!(d.rejected && d.sends[0][0] == 1);
        assert_eq!(Initial::parse(&d.sends[0]).unwrap().dcid, hello_of(&hello).dcid);
        assert_eq!(sim.i_retx(is).sends, vec![d.sends[0].clone()]);
        sim.drive(is, d.sends.clone(), None, 1, 1);
        assert!(!sim.ests[&('I', is)].resumed);
    });
    // rejected: the full handshake uses a new destination id
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, false, true);
        let log = sim.drive(is, first, None, 1, 2);
        assert_eq!(kinds(&log), vec![6, 8, 1, 4, 5]);
        assert_ne!(Initial::parse(&log[2]).unwrap().dcid, hello_of(&log[0]).dcid);
    });
}

/// The state in which the machine waits when the original resume Reply arrives after the fallback.
#[derive(Clone, Copy, PartialEq)]
enum Wait {
    Reply,
    Decap,
    Sign,
    Done,
    Shed,
}

/// A20: the original resume Reply arrives after the Hello was given up.
fn late_reply(c: &mut Ctx) {
    for wait in [Wait::Reply, Wait::Decap, Wait::Sign, Wait::Done, Wait::Shed] {
        c.world(false, |sim| {
            sim.setup_full(1);
            let (is, first) = sim.start(1, 1, false, true);
            let rs = sim.r_new(1);
            let (_, d) = sim.r_recv(rs, &ex(&first[0]));
            let p = d.sends[0].clone();
            sim.i_retx(is);
            let initial = sim.i_retx(is).sends.remove(0);
            assert_eq!(initial[0], 1);
            match wait {
                Wait::Reply => {}
                Wait::Decap | Wait::Sign => {
                    let rs2 = sim.r_new(1);
                    assert!(sim.r_recv(rs2, &ex(&initial)).1.req.is_some());
                    let reply = sim.r_key(rs2, true).1.sends[0].clone();
                    assert!(sim.i_recv(is, &ex(&reply)).1.req.is_some());
                    if wait == Wait::Sign {
                        assert!(sim.i_key(is, true).1.req.is_some());
                    }
                }
                Wait::Done => {
                    sim.drive(is, vec![initial.clone()], None, 1, 1);
                    assert!(is_dropped(&sim.i_recv(is, &ex(&p)).0));
                    return;
                }
                Wait::Shed => {
                    sim.i_shed(is);
                    assert!(is_dropped(&sim.i_recv(is, &ex(&p)).0));
                    return;
                }
            }
            // a forgery changes nothing, the original reply completes the resumption and the key request is gone
            for fld in ["conf", "e", "tids", "cr", "sc"] {
                let (r, d) = sim.i_recv(is, &flip_field(&p, fld));
                assert!(is_dropped(&r) && d.est.is_none() && d.req.is_none() && d.sends.is_empty());
            }
            let (r, d) = sim.i_recv(is, &ex(&p));
            assert!(r.is_ok() && d.est.is_some_and(|e| e.resumed) && d.req.is_none());
            if wait != Wait::Reply {
                assert!(is_dropped(&sim.i_key(is, false).0), "the pending key request is gone");
            }
            assert!(is_dropped(&sim.i_recv(is, &ex(&p)).0));
            assert!(sim.i_retx(is).sends.is_empty());
            sim.accept(is, rs);
        });
    }
}

/// A21: a resumed responder answers repeats within its byte budgets.
fn resent(c: &mut Ctx) {
    // repeated Hellos, then a different Hello, then full Initials under the same ids, until the budgets are spent
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, false, true);
        let hello = first[0].clone();
        let rs = sim.r_new(1);
        let (_, d) = sim.r_recv(rs, &ex(&hello));
        let p = d.sends[0].clone();
        assert_eq!(p.len(), LR);
        let mut spent = 0;
        let (r, d) = sim.r_recv(rs, &flip_field(&hello, "tid"));
        spent += LH;
        assert!(
            is_dropped(&r) && d.sends.is_empty(),
            "a different Hello is not answered"
        );
        let mut answered = 0;
        loop {
            spent += LH;
            let (r, d) = sim.r_recv(rs, &ex(&hello));
            assert_eq!(r.is_ok(), spent <= RESEND_BUDGET);
            if r.is_err() {
                assert!(d.sends.is_empty());
                break;
            }
            assert_eq!(d.sends, vec![p.clone()]);
            answered += 1;
        }
        assert_eq!(answered, RESEND_BUDGET / LH - 1);
        sim.i_retx(is);
        let initial = sim.i_retx(is).sends.remove(0);
        let mut more = 0;
        loop {
            let len = initial.len();
            let (r, d) = sim.r_recv(rs, &ex(&initial));
            let ok = spent + len <= LATE_INITIAL_BUDGET;
            spent += len;
            assert_eq!(r.is_ok(), ok);
            if !ok {
                assert!(d.sends.is_empty());
                break;
            }
            assert_eq!(d.sends, vec![p.clone()]);
            more += 1;
        }
        assert!(more > 5);
        // an Initial under other ids is not answered
        let (_, other) = sim.start(1, 1, false, false);
        assert!(is_dropped(&sim.r_recv(rs, &ex(&other[0])).0));
        // the original reply still completes the resumption
        let (r, d) = sim.i_recv(is, &ex(&p));
        assert!(r.is_ok() && d.est.is_some());
        // shed returns the responder to done: the repeats are dropped
        sim.r_shed(rs);
        assert!(is_dropped(&sim.r_recv(rs, &ex(&hello)).0));
        assert!(is_dropped(&sim.r_recv(rs, &ex(&initial)).0));
    });
    // the full Initial first: its budget runs out before the Hello budget matters
    c.world(false, |sim| {
        sim.setup_full(1);
        let (is, first) = sim.start(1, 1, false, true);
        let rs = sim.r_new(1);
        let _ = sim.r_recv(rs, &ex(&first[0]));
        sim.i_retx(is);
        let initial = sim.i_retx(is).sends.remove(0);
        let mut spent = 0;
        for _ in 0..LATE_INITIAL_BUDGET / initial.len() + 2 {
            let (r, d) = sim.r_recv(rs, &ex(&initial));
            let ok = spent + initial.len() <= LATE_INITIAL_BUDGET;
            spent += initial.len();
            assert_eq!(r.is_ok(), ok);
            assert_eq!(!d.sends.is_empty(), ok);
        }
        assert!(is_dropped(&sim.r_recv(rs, &ex(&first[0])).0));
    });
    // an Initial of the short form under the same ids is answered too; the model has no way to say a message whose
    // form the machine never produces under those ids, so it is run and asserted only
    unrecorded(|sim| {
        sim.setup_full(1);
        let scid = ConnId::new(b"I.shared").unwrap();
        let (_, first) = sim.start_with(1, 1, false, true, scid, Some(0x77));
        let rs = sim.r_new(1);
        let (_, d) = sim.r_recv(rs, &ex(&first[0]));
        let p = d.sends[0].clone();
        let (_, short) = sim.start_with(1, 1, true, false, scid, Some(0x77));
        assert_eq!(short[0][0], 2);
        assert_eq!(Initial::parse(&short[0]).unwrap().dcid, hello_of(&first[0]).dcid);
        let (r, d) = sim.r_recv(rs, &ex(&short[0]));
        assert!(r.is_ok() && d.sends == vec![p]);
    });
}

/// Export and restore of the client store.
fn store(c: &mut Ctx) {
    // the newest tickets, below, at and above the count; restored after a restart and used
    c.world(false, |sim| {
        sim.setup_full(1);
        sim.advance(10);
        let (is, first) = sim.start(2, 1, false, false);
        sim.drive(is, first, None, 2, 2);
        sim.accept(is, 2);
        for max in [0, 1, 2, 5] {
            let bytes = sim.export(max);
            assert_eq!(bytes[1] as usize, max.min(2));
        }
        let bytes = sim.export(5);
        sim.restart();
        assert_eq!(sim.restore(&bytes), Ok(2));
        let (is, first) = sim.start(2, 1, false, true);
        assert_eq!(first[0][0], 6);
        sim.drive(is, first, None, 2, 2);
        assert!(sim.ests[&('I', is)].resumed);
        // restoring into a store that holds a ticket of the same peer replaces it
        assert_eq!(sim.restore(&bytes), Ok(2));
    });
    // entries that expired in between are not stored
    c.world(false, |sim| {
        sim.setup_full(1);
        sim.advance(10);
        let (is, first) = sim.start(2, 1, false, false);
        sim.drive(is, first, None, 2, 2);
        sim.accept(is, 2);
        let bytes = sim.export(5);
        sim.advance(55);
        sim.restart();
        assert_eq!(sim.restore(&bytes), Ok(1));
        let (is, first) = sim.start(1, 1, false, true);
        assert_eq!(first[0][0], 1, "the expired ticket was not restored");
        sim.drive(is, first, None, 1, 1);
        let (is, first) = sim.start(2, 1, false, true);
        assert_eq!(first[0][0], 6);
        sim.drive(is, first, None, 2, 2);
        sim.accept(is, sim.resps.len());
        sim.advance(61);
        assert_eq!(sim.export(5)[1], 0, "nothing unexpired is left to export");
    });
    // a damaged state stores nothing
    c.world(false, |sim| {
        sim.setup_full(1);
        let bytes = sim.export(5);
        sim.restart();
        let mut bad = bytes.clone();
        bad.pop();
        assert!(sim.restore(&bad).is_err());
        let mut bad = bytes.clone();
        bad[0] = 2;
        assert!(sim.restore(&bad).is_err());
        let mut bad = bytes.clone();
        bad.push(0);
        assert!(sim.restore(&bad).is_err());
        assert!(sim.restore(&bytes[..1]).is_err());
        assert!(sim.client.is_empty());
        assert_eq!(sim.restore(&bytes), Ok(1));
    });
    // a restored ticket that was already used is rejected by the responder (single use)
    c.world(false, |sim| {
        sim.setup_full(1);
        let bytes = sim.export(5);
        let (is, first) = sim.start(1, 1, false, true);
        sim.drive(is, first, None, 1, 1);
        sim.accept(is, 2);
        sim.restart();
        assert_eq!(sim.restore(&bytes), Ok(1));
        let (is, first) = sim.start(1, 1, false, true);
        assert_eq!(first[0][0], 6);
        let log = sim.drive(is, first, None, 1, 1);
        assert_eq!(kinds(&log), vec![6, 8, 1, 4, 5]);
    });
}

/// Inputs the model cannot state; run and asserted only.
fn misc() {
    // a Hello for another served ALPN than the ticket's, made by restoring a state whose ALPN was edited, is rejected
    unrecorded(|sim| {
        sim.setup_full(1);
        let mut bytes = sim.export(5);
        let at = 2 + 1 + 32 + 1;
        assert_eq!(&bytes[at..at + 6], b"vinc/1");
        bytes[at + 5] = b'2';
        sim.restart();
        assert_eq!(sim.restore(&bytes), Ok(1));
        let (is, first) = sim.start(1, 2, false, true);
        assert_eq!(first[0][0], 6);
        let log = sim.drive(is, first, None, 1, 1);
        assert_eq!(kinds(&log), vec![6, 8, 1, 4, 5]);
    });
}
