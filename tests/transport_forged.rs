//! A dialing side handed forged Replies: each is dropped and the handshake goes on, so the real Reply that follows
//! completes it, and a handshake that hears only forgeries ends at its connect limit like an unanswered one. The forger
//! holds no key of the dialed node but saw the first flight, so its Replies are well formed and their sealed block can
//! even open (see the support crate's `forge` module).
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use pinc_crypto::IdentityAlg;
use pinc_security::ClientTickets;
use pinc_tests::*;
use pinc_transport::conn::{CloseReason, PathId};

/// Which check a forged Reply fails at the dialing side.
#[derive(Debug, Clone, Copy)]
enum Pick {
    /// An all-zero key share.
    ZeroKey,
    /// An AEAD the dialer did not offer.
    UnofferedAead,
    /// A sealed block that opens and holds no identity.
    Garbage,
    /// A sealed block that opens and holds another node's identity.
    OtherNode,
    /// A sealed block that opens and holds the dialed node's identity with a signature that does not verify.
    BadSignature,
}

const PICKS: [Pick; 5] = [
    Pick::ZeroKey,
    Pick::UnofferedAead,
    Pick::Garbage,
    Pick::OtherNode,
    Pick::BadSignature,
];

fn forgery(w: &World, pick: Pick) -> Forgery {
    match pick {
        Pick::ZeroKey => Forgery::ZeroKey,
        Pick::UnofferedAead => Forgery::UnofferedAead,
        Pick::Garbage => Forgery::Garbage,
        Pick::OtherNode => {
            let other = party(IdentityAlg::Ed25519, 0x77);
            Forgery::ZeroSignature {
                alg: other.id.alg(),
                public_key: other.id.public_key().to_vec(),
            }
        }
        Pick::BadSignature => Forgery::ZeroSignature {
            alg: w.rp.id.alg(),
            public_key: w.rp.id.public_key().to_vec(),
        },
    }
}

/// A Reply forged as `pick` reaches the dialing side as soon as its first flight is out, the real one a round trip
/// later: the forgery is dropped, the dial stays open, and the handshake completes.
fn forged_then_real(pick: Pick) {
    big_stack(move || {
        // Without hardware AES the dialer offers ChaCha20-Poly1305 only, so AES-128-GCM is an AEAD it did not offer.
        let mut w = World::with_aead(IdentityAlg::Ed25519, false);
        let how = forgery(&w, pick);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(61, Params::new(10 * MS)));
        let initial = sent_initial(&mut net);
        let now = net.now;
        let reply = forge_reply(&net.a.prov, &initial, &how);
        let mut d = forge_message(net.a.conn.local_cids().next().unwrap(), &reply);
        let r = net.a.with_env(now, |c, env| c.handle_datagram(env, PathId(1), &mut d));
        net.a.service(now);
        assert_eq!(net.a.closed(), None, "{pick:?} ({r:?})");
        assert!(net.connect(now + 5 * SEC), "{pick:?}: {:?}", net.rx_drops);
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
    });
}

#[test]
fn a_forged_reply_with_a_zero_key_share_is_dropped_and_the_real_one_completes_the_handshake() {
    forged_then_real(Pick::ZeroKey);
}

#[test]
fn a_forged_reply_with_an_aead_never_offered_is_dropped_and_the_real_one_completes_the_handshake() {
    forged_then_real(Pick::UnofferedAead);
}

#[test]
fn a_forged_reply_whose_sealed_block_opens_on_garbage_is_dropped_and_the_real_one_completes_the_handshake() {
    forged_then_real(Pick::Garbage);
}

#[test]
fn a_forged_reply_from_another_node_is_dropped_and_the_real_one_completes_the_handshake() {
    forged_then_real(Pick::OtherNode);
}

#[test]
fn a_forged_reply_with_the_dialed_identity_and_a_bad_signature_is_dropped_and_the_real_one_completes_the_handshake() {
    forged_then_real(Pick::BadSignature);
}

#[test]
fn a_forged_resume_reply_with_a_zero_key_share_is_dropped_and_the_real_one_resumes() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let dialer = w.client(&mut sa, Some(ticket), ClientTickets::new());
        let responder = w.server(&mut sb);
        let mut net = Net::new(dialer, responder, Link::new(63, Params::new(10 * MS)), &mut w.stores);
        net.flush();
        let now = net.now;
        let mut d = forge_message(net.a.conn.local_cids().next().unwrap(), &forge_resume_reply());
        let taken = net.a.with_env(now, |c, env| c.handle_datagram(env, PathId(1), &mut d));
        net.a.service(now);
        assert_eq!(net.a.closed(), None, "{taken:?}");
        assert!(net.connect(now + 5 * SEC), "{:?}", net.rx_drops);
        assert!(net.a.saw(|rec| *rec == Rec::Connected(true)), "the session resumed");
    });
}

#[test]
fn a_handshake_that_hears_only_forged_replies_ends_at_its_connect_limit() {
    big_stack(|| {
        let mut w = World::with_aead(IdentityAlg::Ed25519, false);
        let forgeries: Vec<Forgery> = PICKS.iter().map(|p| forgery(&w, *p)).collect();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // The responder is never reached: only the forger answers.
        let mut link = Link::new(64, Params::new(10 * MS));
        link.route(PathId(1)).up = false;
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let t0 = net.now;
        let initial = sent_initial(&mut net);
        let dcid = net.a.conn.local_cids().next().unwrap();
        let replies: Vec<Vec<u8>> = forgeries
            .iter()
            .map(|f| forge_message(dcid, &forge_reply(&net.a.prov, &initial, f)))
            .collect();
        // One forgery after each resend of the first flight, every kind in turn.
        let (mut sent, mut due) = (0, t0);
        net.run(t0 + 29 * SEC, |n| {
            if n.now >= due {
                let now = n.now;
                let mut d = replies[sent % replies.len()].clone();
                let _ = n.a.with_env(now, |c, env| c.handle_datagram(env, PathId(1), &mut d));
                n.a.service(now);
                sent += 1;
                due = now + SEC;
            }
            false
        });
        assert_eq!(net.a.closed(), None, "the dial still waits for the real Reply");
        assert!(sent >= replies.len(), "{sent} forgeries");
        net.run(t0 + 31 * SEC, |_| false);
        assert_eq!(net.a.closed(), Some(CloseReason::HandshakeTimeout));
    });
}
