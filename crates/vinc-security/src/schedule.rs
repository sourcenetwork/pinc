//! The transcripts and the key schedule, written once and called by both roles.
//!
//! Invariants: every transcript starts with its label and absorbs every field the handshake binds (version, ALPN, both
//! connection ids, the credit record of both sides, the AEAD offer and choice, every public value, the hash of the
//! prekey, the identities and the signatures), each as a length-prefixed field, so two different handshakes never share a transcript; the chain
//! starts at `ck0 = hash("chain")`, mixes in the post-quantum and the classical secrets together
//! (`extract(ck0, ss_K || ss_X)`), and the application keys come from a second extraction over the final transcript,
//! so they depend on everything the peers signed. Both roles derive through the same functions, so they cannot drift.

use vinc_crypto::{Aead, IdentityAlg, Provider, Secret, Transcript, expand, extract};
use vinc_wire::Writer;
use zeroize::Zeroize;

use crate::credit::CreditRecord;
use crate::error::Failure;
use crate::ids::{AeadSet, ConnId, aead_tag};
use crate::labels;
use crate::message::{IdSig, MAX_SEALED_LEN};
use crate::record::PacketKey;

/// The length of the message a signature covers: a label and a transcript hash.
pub(crate) const SIGNATURE_MESSAGE_LEN: usize = labels::SIGNATURE_RESPONDER.len() + 32;
const _: () = assert!(labels::SIGNATURE_RESPONDER.len() == labels::SIGNATURE_INITIATOR.len());

pub(crate) fn derive(prk: &Secret<32>, label: &'static str, ctx: &[u8]) -> Secret<32> {
    let mut out = [0u8; 32];
    expand(prk.expose(), label, ctx, &mut out);
    let secret = Secret::new(out);
    out.zeroize();
    secret
}

pub(crate) fn chain(salt: &Secret<32>, ikm: &[u8]) -> Secret<32> {
    let mut out = extract(salt.expose(), ikm);
    let secret = Secret::new(out);
    out.zeroize();
    secret
}

/// `ck0`: the public starting point of every chain.
pub(crate) fn initial_chain() -> Secret<32> {
    Secret::new(Transcript::with_label(labels::CHAIN).snapshot())
}

/// The first 16 bytes of a transcript hash, which a reject echoes.
pub(crate) fn echo(th: &[u8; 32]) -> [u8; 16] {
    let mut out = [0u8; 16];
    out.iter_mut().zip(th).for_each(|(o, t)| *o = *t);
    out
}

/// The message a signature covers: `label || th`.
pub(crate) fn signature_message(label: &'static str, th: &[u8; 32]) -> [u8; SIGNATURE_MESSAGE_LEN] {
    let mut msg = [0u8; SIGNATURE_MESSAGE_LEN];
    let (head, tail) = msg.split_at_mut(label.len());
    head.copy_from_slice(label.as_bytes());
    tail.copy_from_slice(th);
    msg
}

/// The fields of an Initial that the transcript absorbs.
pub(crate) struct InitialFields<'a> {
    pub version: u8,
    pub dcid: &'a ConnId,
    pub scid: &'a ConnId,
    pub alpn: &'a [u8],
    pub offer: AeadSet,
    pub e: &'a [u8; 32],
    pub prekey_hash: &'a [u8; 32],
    pub credit: &'a CreditRecord,
}

/// The transcript after the Initial (the same for the full and the short form).
pub(crate) fn initial_transcript(f: &InitialFields<'_>) -> Transcript {
    let mut th = Transcript::with_label(labels::HANDSHAKE);
    th.absorb("label", labels::HANDSHAKE.as_bytes());
    th.absorb("version", &[f.version]);
    th.absorb("alpn", f.alpn);
    th.absorb("dcid", f.dcid.as_bytes());
    th.absorb("scid", f.scid.as_bytes());
    th.absorb("credit", &f.credit.encode());
    th.absorb("offer", &[f.offer.bits()]);
    th.absorb("e", f.e);
    th.absorb("prekey_hash", f.prekey_hash);
    th
}

/// Absorb the responder's contribution: its connection id, the chosen AEAD and its public values.
pub(crate) fn absorb_reply(th: &mut Transcript, scid: &ConnId, aead: Aead, e: &[u8; 32], ct: &[u8]) {
    th.absorb("r_scid", scid.as_bytes());
    th.absorb("aead", &[aead_tag(aead)]);
    th.absorb("r_e", e);
    th.absorb("ct", ct);
}

/// Absorb a credit record as its own field.
pub(crate) fn absorb_credit(th: &mut Transcript, credit: CreditRecord) {
    th.absorb("r_credit", &credit.encode());
}

/// Absorb an identity: the algorithm tag, then the public key.
pub(crate) fn absorb_identity(th: &mut Transcript, alg: IdentityAlg, public_key: &[u8]) {
    th.absorb("id_alg", &[alg.tag()]);
    th.absorb("id_key", public_key);
}

/// The secrets of the first stage: the chain key and the two handshake secrets.
pub(crate) struct HandshakeKeys {
    pub ck1: Secret<32>,
    pub initiator: Secret<32>,
    pub responder: Secret<32>,
}

/// `ck1 = extract(ck0, ss_K || ss_X)` and the handshake secrets `expand(ck1, label, th1)`.
pub(crate) fn handshake_keys(ss_k: &Secret<32>, ss_x: &Secret<32>, th1: &[u8; 32]) -> HandshakeKeys {
    let mut ikm = [0u8; 64];
    let (k, x) = ikm.split_at_mut(32);
    k.copy_from_slice(ss_k.expose());
    x.copy_from_slice(ss_x.expose());
    let ck1 = chain(&initial_chain(), &ikm);
    ikm.zeroize();
    HandshakeKeys {
        initiator: derive(&ck1, labels::HANDSHAKE_INITIATOR, th1),
        responder: derive(&ck1, labels::HANDSHAKE_RESPONDER, th1),
        ck1,
    }
}

/// The secrets of the second stage.
pub(crate) struct AppSecrets {
    pub initiator: Secret<32>,
    pub responder: Secret<32>,
    pub resume: Secret<32>,
    pub confirm: Secret<32>,
    pub cid: Secret<32>,
}

/// `ck2 = extract(ck1, th)` and the application, resumption and confirmation secrets `expand(ck2, label, th)`.
pub(crate) fn application_secrets(ck1: &Secret<32>, th: &[u8; 32]) -> AppSecrets {
    let ck2 = chain(ck1, th);
    AppSecrets {
        initiator: derive(&ck2, labels::APPLICATION_INITIATOR, th),
        responder: derive(&ck2, labels::APPLICATION_RESPONDER, th),
        resume: derive(&ck2, labels::RESUMPTION, th),
        confirm: derive(&ck2, labels::RESUME_CONFIRM, th),
        cid: derive(&ck2, labels::CID_SECRET, th),
    }
}

/// The pre-shared key of a ticket.
pub(crate) fn ticket_psk(resume: &Secret<32>, tid: &[u8; 16], credit: CreditRecord) -> Secret<32> {
    // The issuer's remembered credit record is part of the key's context: a resumption only works against it.
    let mut ctx = Transcript::with_label(labels::TICKET);
    ctx.absorb("tid", tid);
    ctx.absorb("credit", &credit.encode());
    derive(resume, labels::TICKET, &ctx.snapshot())
}

/// `extract(ck0, psk)`: the chain a resumption starts from.
pub(crate) fn psk_chain(psk: &Secret<32>) -> Secret<32> {
    chain(&initial_chain(), psk.expose())
}

/// The fields of a resume Hello that its transcript absorbs.
pub(crate) struct HelloFields<'a> {
    pub version: u8,
    pub alpn: &'a [u8],
    pub dcid: &'a ConnId,
    pub scid: &'a ConnId,
    pub aead: Aead,
    pub tid: &'a [u8; 16],
    pub e: &'a [u8; 32],
    pub credit: &'a CreditRecord,
}

/// The transcript after the Hello, up to but not including the binder.
pub(crate) fn hello_transcript(f: &HelloFields<'_>) -> Transcript {
    let mut th = Transcript::with_label(labels::RESUME_HANDSHAKE);
    th.absorb("label", labels::RESUME_HANDSHAKE.as_bytes());
    th.absorb("version", &[f.version]);
    th.absorb("alpn", f.alpn);
    th.absorb("dcid", f.dcid.as_bytes());
    th.absorb("scid", f.scid.as_bytes());
    th.absorb("aead", &[aead_tag(f.aead)]);
    th.absorb("tid", f.tid);
    th.absorb("e", f.e);
    th.absorb("credit", &f.credit.encode());
    th
}

/// `keyed_hash(expand(psk, binder label), th_hello)`.
pub(crate) fn binder(psk: &Secret<32>, th_hello: &[u8; 32]) -> [u8; 32] {
    let key = derive(psk, labels::BINDER, &[]);
    extract(key.expose(), th_hello)
}

/// The 0-RTT secret: `expand(extract(ck0, psk), "early data", th_hello)`.
pub(crate) fn early_secret(ck_psk: &Secret<32>, th_hello: &[u8; 32]) -> Secret<32> {
    derive(ck_psk, labels::EARLY_DATA, th_hello)
}

/// Absorb the rest of a resumption: the binder, the responder's connection id and public value.
pub(crate) fn absorb_resume_reply(
    th: &mut Transcript,
    binder: &[u8; 32],
    scid: &ConnId,
    e: &[u8; 32],
    credit: CreditRecord,
) {
    th.absorb("binder", binder);
    th.absorb("r_scid", scid.as_bytes());
    th.absorb("r_e", e);
    th.absorb("r_credit", &credit.encode());
}

/// The confirmation tag: `keyed_hash(confirm key, th_r || tickets)`, with the tickets absorbed into the transcript.
pub(crate) fn confirmation(confirm: &Secret<32>, th: &mut Transcript, tickets: &[u8]) -> [u8; 32] {
    th.absorb("tickets", tickets);
    extract(confirm.expose(), &th.snapshot())
}

/// The secret of a sub-session: `expand(parent, "sub session", H(alpn, cc, cs))`, where the hash absorbs each field
/// length-prefixed, so different field splits never collide.
pub fn sub_session_secret(parent: &Secret<32>, alpn: &[u8], cc: &[u8], cs: &[u8]) -> Secret<32> {
    let mut t = Transcript::with_label(labels::SUB_SESSION_CONTEXT);
    t.absorb("alpn", alpn);
    t.absorb("cc", cc);
    t.absorb("cs", cs);
    derive(parent, labels::SUB_SESSION, &t.snapshot())
}

/// A sealed identity and signature in a fixed buffer.
pub(crate) struct Sealed {
    pub bytes: [u8; MAX_SEALED_LEN],
    pub len: usize,
}

impl Sealed {
    pub(crate) fn as_slice(&self) -> &[u8] {
        self.bytes.get(..self.len).unwrap_or_default()
    }
}

/// Seal `plain` (already written at the start of a fixed buffer) under the handshake secret, with packet number 0
/// and the transcript hash `th` as associated data, and append the tag.
pub(crate) fn seal_handshake<P: Provider>(
    p: &P,
    aead: Aead,
    secret: &Secret<32>,
    th: &[u8; 32],
    mut sealed: Sealed,
    plain_len: usize,
) -> Result<Sealed, Failure> {
    let mut key = PacketKey::from_secret(p, aead, secret)?;
    let body = sealed.bytes.get_mut(..plain_len).ok_or(Failure::InvalidParameter)?;
    let tag = key.seal(p, 0, th, body).map_err(|_| Failure::InvalidParameter)?;
    let end = plain_len + tag.len();
    sealed
        .bytes
        .get_mut(plain_len..end)
        .ok_or(Failure::InvalidParameter)?
        .copy_from_slice(&tag);
    sealed.len = end;
    Ok(sealed)
}

/// Open a sealed identity and signature, returning the plaintext in a fixed buffer and its length.
pub(crate) fn open_handshake<P: Provider>(
    p: &P,
    aead: Aead,
    secret: &Secret<32>,
    th: &[u8; 32],
    sealed: &[u8],
) -> Result<Sealed, Failure> {
    let mut key = PacketKey::from_secret(p, aead, secret)?;
    let plain_len = sealed.len().checked_sub(Aead::TAG_LEN).ok_or(Failure::Authentication)?;
    let (ct, tag) = sealed.split_at_checked(plain_len).ok_or(Failure::Authentication)?;
    let tag: &[u8; Aead::TAG_LEN] = tag.try_into().map_err(|_| Failure::Authentication)?;
    let mut out = Sealed {
        bytes: [0; MAX_SEALED_LEN],
        len: plain_len,
    };
    let body = out.bytes.get_mut(..plain_len).ok_or(Failure::Authentication)?;
    body.copy_from_slice(ct);
    key.open(p, 0, th, body, tag).map_err(|_| Failure::Authentication)?;
    Ok(out)
}

/// Seal the identity `alg`/`public_key` and its `signature` under the handshake secret (see [`seal_handshake`]).
pub(crate) fn seal_id_sig<P: Provider>(
    p: &P,
    aead: Aead,
    secret: &Secret<32>,
    th: &[u8; 32],
    id: (IdentityAlg, &[u8]),
    signature: &[u8],
    credit: Option<CreditRecord>,
) -> Result<Sealed, Failure> {
    let mut sealed = Sealed {
        bytes: [0; MAX_SEALED_LEN],
        len: 0,
    };
    let mut w = Writer::new(&mut sealed.bytes);
    IdSig {
        alg: id.0,
        public_key: id.1,
        signature,
        credit,
    }
    .write(&mut w)
    .map_err(Failure::BadPayload)?;
    let plain_len = w.written().len();
    seal_handshake(p, aead, secret, th, sealed, plain_len)
}

/// The next secret of a traffic direction after a key roll: `expand(extract(secret, dh), "key roll")`. The fresh
/// Diffie-Hellman value `dh` enters the extraction, so a party that holds only the old `secret` cannot compute it.
pub fn roll_secret(secret: &Secret<32>, dh: &Secret<32>) -> Secret<32> {
    derive(&chain(secret, dh.expose()), labels::KEY_ROLL, &[])
}
