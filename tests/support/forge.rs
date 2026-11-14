//! A forger of handshake messages: a party that saw a dialing side's first flight and answers in the responder's
//! place, holding no key of the dialed node. Its Replies are well formed, and their sealed block can even open at the
//! dialer, since the prekey's encapsulation key and the dialer's ephemeral key are public in the full Initial: the key
//! schedule is computed here the way a responder computes it, from public values and the forger's own secrets.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]

use std::cell::RefCell;
use std::rc::Rc;

use vinc_crypto::{Aead, IdentityAlg, Provider, Secret, Transcript, expand, extract};
use vinc_security::ids::aead_tag;
use vinc_security::labels;
use vinc_security::message::{IdSig, Initial, MAX_SEALED_LEN, PrekeyField, Reply, ResumeReply};
use vinc_security::{CreditRecord, PacketKey, TicketBatch};
use vinc_transport::packet::{ConnId, LongHeader, LongType};
use vinc_wire::{Reader, Writer};

use crate::Net;

/// The source id a forger puts in its packets and messages.
pub fn forger_cid() -> ConnId {
    ConnId::new(&[0xee; 8]).unwrap()
}

/// A long Handshake packet to `dcid` from the forger's id, carrying `body`.
pub fn forge_packet(dcid: ConnId, body: &[u8]) -> Vec<u8> {
    let h = LongHeader {
        ty: LongType::Handshake,
        dcid,
        scid: forger_cid(),
        body_len: body.len(),
    };
    let mut d = vec![0u8; h.header_len() + body.len()];
    let mut w = Writer::new(&mut d);
    h.write(&mut w, 0).unwrap();
    w.put_slice(body).unwrap();
    d
}

/// A long Handshake packet to `dcid` from the forger's id, carrying the whole message `msg` as one fragment.
pub fn forge_message(dcid: ConnId, msg: &[u8]) -> Vec<u8> {
    let mut body = vec![0u8; msg.len() + 16];
    let mut w = Writer::new(&mut body);
    w.put_varint(msg.len() as u64).unwrap();
    w.put_varint(0).unwrap();
    w.put_slice(msg).unwrap();
    let len = w.written().len();
    forge_packet(dcid, &body[..len])
}

/// The first handshake message the datagrams carry, put together from its fragments; `None` until every byte of it
/// is in. Datagrams that hold no Handshake packet (padding) are skipped.
pub fn first_message<'a>(datagrams: impl IntoIterator<Item = &'a [u8]>) -> Option<Vec<u8>> {
    let (mut msg, mut have) = (Vec::new(), Vec::new());
    for d in datagrams {
        let Ok((h, at)) = LongHeader::parse(d) else { continue };
        if h.ty != LongType::Handshake {
            continue;
        }
        let mut r = Reader::new(&d[at..at + h.body_len]);
        let total = usize::try_from(r.read_varint().ok()?).ok()?;
        let off = usize::try_from(r.read_varint().ok()?).ok()?;
        let part = r.read_bytes(r.remaining()).ok()?;
        if msg.is_empty() {
            msg = vec![0u8; total];
            have = vec![false; total];
        }
        msg.get_mut(off..off + part.len())?.copy_from_slice(part);
        have[off..off + part.len()].fill(true);
        if have.iter().all(|h| *h) {
            return Some(msg);
        }
    }
    None
}

/// Let the dialing side of `net` send its first flight now, and return the first message that flight carried: what a
/// forger who saw it holds.
pub fn sent_initial<const C: usize, const F: usize>(net: &mut Net<'_, '_, C, F>) -> Vec<u8> {
    let sent: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
    let sink = Rc::clone(&sent);
    let before = net.on_tx.replace(Box::new(move |is_a, d, _| {
        if is_a {
            sink.borrow_mut().push(d.to_vec());
        }
    }));
    net.flush();
    net.on_tx = before;
    first_message(sent.borrow().iter().map(Vec::as_slice)).expect("the first flight carries the whole first message")
}

/// How a forged Reply fails at the dialing side.
#[derive(Debug, Clone)]
pub enum Forgery {
    /// An all-zero ephemeral key: no shared secret comes out of it.
    ZeroKey,
    /// AES-128-GCM, which a dialer without hardware AES does not offer.
    UnofferedAead,
    /// A sealed block that does not open.
    Unopened,
    /// A sealed block that opens and holds no identity.
    Garbage,
    /// A sealed block that opens and holds the identity `alg`/`public_key` with an all-zero signature: another node's
    /// identity, or the dialed node's with a signature that does not verify.
    ZeroSignature { alg: IdentityAlg, public_key: Vec<u8> },
}

/// A Reply to the full Initial `initial` (the dialer's first message), made by the forger and failing `how`.
pub fn forge_reply<P: Provider>(p: &P, initial: &[u8], how: &Forgery) -> Vec<u8> {
    let init = Initial::parse(initial).unwrap();
    let PrekeyField::Full(ek) = init.prekey else {
        panic!("the forger needs the full Initial")
    };
    // The transcript a responder holds after the Initial.
    let mut th = Transcript::with_label(labels::HANDSHAKE);
    th.absorb("label", labels::HANDSHAKE.as_bytes());
    th.absorb("version", &[init.version]);
    th.absorb("alpn", init.alpn);
    th.absorb("dcid", init.dcid.as_bytes());
    th.absorb("scid", init.scid.as_bytes());
    th.absorb("credit", &init.credit.encode());
    th.absorb("offer", &[init.aead_offer.bits()]);
    th.absorb("e", &init.e);
    th.absorb("prekey_hash", &init.prekey_hash());
    // The forger's own share of both exchanges.
    let secret = p.x25519_secret(&[0x46; 32]);
    let ss_x = p.x25519_dh(&secret, &init.e).unwrap();
    let e = match how {
        Forgery::ZeroKey => [0; 32],
        _ => p.x25519_public(&secret),
    };
    let (ct, ss_k) = p.kem_encapsulate(&p.kem_encaps_key(ek).unwrap(), &[0x47; 32]).unwrap();
    let ct = p.kem_ciphertext_bytes(&ct);
    let aead = match how {
        Forgery::UnofferedAead => Aead::Aes128Gcm,
        _ => Aead::ChaCha20Poly1305,
    };
    let scid = forger_cid();
    th.absorb("r_scid", scid.as_bytes());
    th.absorb("aead", &[aead_tag(aead)]);
    th.absorb("r_e", &e);
    th.absorb("ct", &ct);
    let th1 = th.snapshot();
    // The responder's handshake secret, as the dialer derives it.
    let mut ikm = [0u8; 64];
    ikm[..32].copy_from_slice(ss_k.expose());
    ikm[32..].copy_from_slice(ss_x.expose());
    let ck1 = extract(&Transcript::with_label(labels::CHAIN).snapshot(), &ikm);
    let mut key = [0u8; 32];
    expand(&ck1, labels::HANDSHAKE_RESPONDER, &th1, &mut key);
    // What the sealed block holds: an identity and a signature, or bytes that parse as none.
    let mut plain = vec![0u8; MAX_SEALED_LEN];
    let n = if let Forgery::ZeroSignature { alg, public_key } = how {
        let mut w = Writer::new(&mut plain);
        IdSig {
            alg: *alg,
            public_key,
            signature: &vec![0; alg.signature_len()],
            credit: Some(CreditRecord::NONE),
        }
        .write(&mut w)
        .unwrap();
        w.written().len()
    } else {
        plain[..40].fill(0xff);
        40
    };
    let body = &mut plain[..n];
    let tag = if matches!(how, Forgery::Unopened) {
        [0x5a; Aead::TAG_LEN]
    } else {
        let mut k = PacketKey::from_secret(p, aead, &Secret::new(key)).unwrap();
        k.seal(p, 0, &th1, body).unwrap()
    };
    let mut sealed = body.to_vec();
    sealed.extend_from_slice(&tag);
    let reply = Reply {
        scid,
        aead,
        e,
        ct: &ct,
        sealed: &sealed,
    };
    let mut msg = vec![0u8; 8192];
    let mut w = Writer::new(&mut msg);
    reply.write(&mut w).unwrap();
    let len = w.written().len();
    msg.truncate(len);
    msg
}

/// A resume Reply from the forger with an all-zero ephemeral key: no shared secret comes out of it.
pub fn forge_resume_reply() -> Vec<u8> {
    let reply = ResumeReply {
        scid: forger_cid(),
        e: [0; 32],
        tickets: TicketBatch::new(),
        credit: CreditRecord::NONE,
        confirm: [0; 32],
    };
    let mut msg = vec![0u8; 512];
    let mut w = Writer::new(&mut msg);
    reply.write(&mut w).unwrap();
    let len = w.written().len();
    msg.truncate(len);
    msg
}
