//! Origin authentication: the message id, the body hash and the signature that binds them to the topic.
//!
//! The signature covers `topic | mid | H(body)`, so a hub or a peer that swaps the body of a message breaks it. It
//! also covers the timestamp and the body flag (appended after the body hash): the replay floors judge a message by
//! its timestamp, so an unsigned one would let a relay censor or replay by rewriting it. Signing and verifying go
//! through `vinc-crypto` for every identity algorithm.
//!
//! Invariants: [`verify`] is true only when the origin's key signed this topic, this id and this exact body; the key
//! must match the origin's node id (an Ed25519 id is the key itself, every other id is a hash of it).

use vinc_crypto::identity::verify_node;
use vinc_crypto::{IdentityAlg, Keypair, NodeId as CryptoId};

use crate::consts::MAX_TOPIC;
use crate::wire::{Head, MID_LEN, TS_LEN, put_ts};
use vinc_wire::hlc::Hlc;

const LABEL_MID: &str = "VINC 2026 v1 broadcast message id";
const LABEL_BODY: &str = "VINC 2026 v1 broadcast body hash";

/// The most bytes of a signed statement: the longest topic, the id and the body hash.
const SIGNED_MAX: usize = MAX_TOPIC + MID_LEN + 32 + TS_LEN + 1;

fn first8(d: &blake3::Hash) -> [u8; MID_LEN] {
    d.as_bytes().first_chunk::<MID_LEN>().copied().unwrap_or([0; MID_LEN])
}

/// `H(origin | inc | seq | topic)` cut to 8 bytes: the id of the `seq`-th message of an incarnation.
pub fn message_id(origin: &[u8; 32], inc: u64, seq: u64, topic: &[u8]) -> [u8; MID_LEN] {
    let mut h = blake3::Hasher::new_derive_key(LABEL_MID);
    h.update(origin);
    h.update(&inc.to_be_bytes());
    h.update(&seq.to_be_bytes());
    h.update(topic);
    first8(&h.finalize())
}

/// The hash of a message body, the third part of what the signature covers.
pub fn body_hash(body: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(LABEL_BODY);
    h.update(body);
    *h.finalize().as_bytes()
}

/// A fixed buffer that `put_ts` can extend without allocating.
struct Fixed<'a> {
    buf: &'a mut [u8; SIGNED_MAX],
    at: usize,
}

impl Fixed<'_> {
    fn put(&mut self, src: &[u8]) {
        if let Some(d) = self.buf.get_mut(self.at..self.at + src.len()) {
            d.copy_from_slice(src);
            self.at += src.len();
        }
    }
}

impl Extend<u8> for Fixed<'_> {
    fn extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) {
        for b in iter {
            self.put(&[b]);
        }
    }
}

fn statement(topic: &[u8], mid: [u8; MID_LEN], body: &[u8], ts: Hlc, isb: bool, buf: &mut [u8; SIGNED_MAX]) -> usize {
    let n = topic.len().min(MAX_TOPIC);
    let mut w = Fixed { buf, at: 0 };
    w.put(topic.get(..n).unwrap_or_default());
    w.put(&mid);
    w.put(&body_hash(body));
    put_ts(&mut w, ts);
    w.put(&[u8::from(isb)]);
    w.at
}

/// Sign `topic | mid | H(body) | ts | isb` with `key`, writing the signature to `out`; returns its length, or `None`
/// if `out` is too short.
pub fn sign(
    key: &Keypair,
    topic: &[u8],
    mid: &[u8; MID_LEN],
    body: &[u8],
    ts: Hlc,
    isb: bool,
    out: &mut [u8],
) -> Option<usize> {
    let mut buf = [0u8; SIGNED_MAX];
    let n = statement(topic, *mid, body, ts, isb, &mut buf);
    key.sign(buf.get(..n)?, out).ok()
}

/// Whether `head` is a valid signature of `topic`, its id, `body`, its timestamp and its body flag by its origin.
pub fn verify(head: &Head<'_>, topic: &[u8], body: &[u8]) -> bool {
    if topic.len() > MAX_TOPIC {
        return false;
    }
    let mut buf = [0u8; SIGNED_MAX];
    let n = statement(topic, head.mid, body, head.ts, head.isb, &mut buf);
    let Some(msg) = buf.get(..n) else { return false };
    origin_signed(head.alg, head.origin, head.pk, msg, head.sig)
}

/// Whether `sig` is a signature of `msg` by the key `pk` (the origin itself for Ed25519) that `origin` names under
/// `alg`: the key must match the node id.
pub(crate) fn origin_signed(alg: IdentityAlg, origin: &[u8; 32], pk: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    let id = CryptoId { alg, bytes: *origin };
    let pk: &[u8] = if alg == IdentityAlg::Ed25519 { origin } else { pk };
    verify_node(&id, pk, msg, sig).is_ok()
}
