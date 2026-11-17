//! The signed envelope of a topic message: the topic, the exact wire head and the body, as one value an application
//! can store, hand to anyone and verify later with no endpoint, no session and no network.
//!
//! The canonical bytes are `version1 | kind1 | topic_len2 | topic | head | body`, with the lengths big endian and `head`
//! exactly as it travels ([`Head`]; it names the body's length in `blen`). Version 1 is the only version and kind 1
//! ([`KIND_TOPIC_V1`], a topic message) the only kind defined; any other kind is refused.
//!
//! What a verified envelope proves: the key behind `origin` signed this topic, this message id, this exact payload and
//! this timestamp. What it does not prove: that the key was unrevoked at that time, the message's position among
//! others (the id is a position hash, not a content hash), or that anyone received it. A kind 1 statement carries no
//! label of its own (it begins with the topic's bytes), so a kind 1 proof also holds for a raw signature by the same key
//! over bytes of that shape: an application that signs bytes a peer chose with `Endpoint::sign` can be made to produce
//! one (its guard refuses the reserved label prefixes, which an unlabelled topic statement does not carry).
//!
//! Invariants: [`Envelope::decode`] validates the whole structure at this boundary (version, kind, the topic bound,
//! the head, the body length, no trailing byte) and never panics or reads outside its input; [`Envelope::verify`]
//! re-checks the parts it is given, so an envelope built by hand cannot verify unless it is well formed; neither
//! allocates.

use vinc_crypto::{IdentityAlg, NodeId as AuthorId};
use vinc_membership::NodeId;
use vinc_wire::Reader;

use crate::auth;
use crate::consts::MAX_TOPIC;
use crate::wire::{Head, Malformed};

/// The version of the canonical encoding.
pub const VERSION: u8 = 1;
/// The kind of a topic message, first version.
pub const KIND_TOPIC_V1: u8 = 1;
/// The bytes before the topic: version, kind and the topic length.
const PREFIX: usize = 4;

/// Why an envelope was not accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum EnvelopeError {
    /// The version is not one this library knows.
    BadVersion,
    /// The kind is not one this library knows.
    BadKind,
    /// The bytes are not a well-formed envelope, named by the reason: one plain clause.
    Malformed(&'static str),
    /// The origin's key did not sign this topic, id, payload and timestamp.
    BadSignature,
}

impl core::fmt::Display for EnvelopeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::BadVersion => f.write_str("the envelope has a version this library does not know"),
            Self::BadKind => f.write_str("the envelope has a kind this library does not know"),
            Self::Malformed(why) => write!(f, "the envelope is malformed: {why}"),
            Self::BadSignature => f.write_str("the origin's signature does not match the envelope's contents"),
        }
    }
}

impl core::error::Error for EnvelopeError {}

impl From<Malformed> for EnvelopeError {
    /// The head's own reasons, as one plain clause each.
    fn from(m: Malformed) -> Self {
        Self::Malformed(match m.0 {
            "algorithm" => "the origin's algorithm is unknown",
            "body flag" => "the body flag is neither 0 nor 1",
            "body length" => "the body length does not match the head",
            _ => "the head is cut short",
        })
    }
}

/// What a verified envelope proves, borrowed from its bytes. See the module docs for what it does not prove.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct Verified<'a> {
    /// The origin's node id: the identity whose key signed.
    pub origin: &'a NodeId,
    /// The origin's signature algorithm.
    pub alg: IdentityAlg,
    /// The topic.
    pub topic: &'a [u8],
    /// The payload.
    pub payload: &'a [u8],
    /// The message id: 8 bytes the origin chose. It is not unique across origins and not a content id, so a store must
    /// not use it alone as a key.
    pub mid: [u8; 8],
    /// The signed timestamp's physical part, in milliseconds: the author's own claim, not a time anyone else vouches for.
    pub wall_ms: u64,
    /// The signed timestamp's logical part, which orders messages inside one millisecond.
    pub counter: u32,
    /// The signed body flag: whether the body is bytes rather than a stream slice.
    pub isb: bool,
}

impl Verified<'_> {
    /// The origin as a typed node id, comparable with the origin an event names.
    pub const fn author(&self) -> AuthorId {
        AuthorId {
            alg: self.alg,
            bytes: *self.origin,
        }
    }
}

/// The parts of a signed message, borrowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Envelope<'a> {
    /// The kind of statement: [`KIND_TOPIC_V1`] is the only one.
    pub kind: u8,
    /// The topic.
    pub topic: &'a [u8],
    /// The message head exactly as the wire carries it.
    pub head: &'a [u8],
    /// The body.
    pub body: &'a [u8],
}

impl<'a> Envelope<'a> {
    /// The parts of a topic message.
    pub const fn topic(topic: &'a [u8], head: &'a [u8], body: &'a [u8]) -> Self {
        Self {
            kind: KIND_TOPIC_V1,
            topic,
            head,
            body,
        }
    }

    /// The length of the canonical encoding.
    pub const fn encoded_len(&self) -> usize {
        PREFIX + self.topic.len() + self.head.len() + self.body.len()
    }

    /// Append the canonical encoding to `out`. A topic over 65535 bytes has a length that does not fit its field, and
    /// the encoding is then refused by [`Envelope::decode`] like any topic over the layer's bound.
    pub fn encode_into(&self, out: &mut impl Extend<u8>) {
        out.extend([VERSION, self.kind]);
        out.extend(u16::try_from(self.topic.len()).unwrap_or(u16::MAX).to_be_bytes());
        out.extend(self.topic.iter().copied());
        out.extend(self.head.iter().copied());
        out.extend(self.body.iter().copied());
    }

    /// Split canonical bytes into their parts, checking the structure but not the signature.
    ///
    /// # Errors
    /// [`EnvelopeError::BadVersion`] or [`EnvelopeError::BadKind`] for a version or kind not defined;
    /// [`EnvelopeError::Malformed`] for a topic over the layer's bound, a head that does not parse, a body whose
    /// length differs from the one the head names, or bytes cut short or left over.
    pub fn decode(bytes: &'a [u8]) -> Result<Self, EnvelopeError> {
        const CUT: EnvelopeError = EnvelopeError::Malformed("it is cut short");
        let mut r = Reader::new(bytes);
        if r.read_u8().map_err(|_| CUT)? != VERSION {
            return Err(EnvelopeError::BadVersion);
        }
        let kind = r.read_u8().map_err(|_| CUT)?;
        if kind != KIND_TOPIC_V1 {
            return Err(EnvelopeError::BadKind);
        }
        let tl = usize::from(r.read_u16().map_err(|_| CUT)?);
        if tl > MAX_TOPIC {
            return Err(EnvelopeError::Malformed("the topic is too long"));
        }
        let topic = r.read_bytes(tl).map_err(|_| CUT)?;
        let n = r.remaining();
        let rest = r.read_bytes(n).map_err(|_| CUT)?;
        let (head, blen, tail) = Head::parse_prefix(rest)?;
        if tail.len() < blen {
            return Err(CUT);
        }
        if tail.len() > blen {
            return Err(EnvelopeError::Malformed("bytes follow the body"));
        }
        Ok(Self {
            kind,
            topic,
            head: rest.get(..head.len()).ok_or(CUT)?,
            body: tail,
        })
    }

    /// Check the origin's signature over the topic, the message id, the body and the timestamp, and that its key is
    /// the origin's. The parts are validated again, so an envelope built by hand verifies only if it is well formed.
    ///
    /// # Errors
    /// [`EnvelopeError::BadKind`] for a kind not defined; [`EnvelopeError::Malformed`] if a part does not fit the
    /// format; [`EnvelopeError::BadSignature`] if the signature does not match.
    pub fn verify(&self) -> Result<Verified<'a>, EnvelopeError> {
        if self.kind != KIND_TOPIC_V1 {
            return Err(EnvelopeError::BadKind);
        }
        if self.topic.len() > MAX_TOPIC {
            return Err(EnvelopeError::Malformed("the topic is too long"));
        }
        let (head, blen, tail) = Head::parse_prefix(self.head)?;
        if !tail.is_empty() || blen != self.body.len() {
            return Err(EnvelopeError::Malformed("the body length does not match the head"));
        }
        if !auth::verify(&head, self.topic, self.body) {
            return Err(EnvelopeError::BadSignature);
        }
        Ok(Verified {
            origin: head.origin,
            alg: head.alg,
            topic: self.topic,
            payload: self.body,
            mid: head.mid,
            wall_ms: head.ts.wall,
            counter: head.ts.counter,
            isb: head.isb,
        })
    }
}

/// Decode canonical bytes and verify them: the offline check of a stored envelope.
///
/// # Errors
/// Any [`EnvelopeError`] of [`Envelope::decode`] and [`Envelope::verify`].
pub fn verify_bytes(bytes: &[u8]) -> Result<Verified<'_>, EnvelopeError> {
    Envelope::decode(bytes)?.verify()
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    extern crate std;
    use std::vec;
    use std::vec::Vec;

    use vinc_crypto::Keypair;
    use vinc_crypto::identity::MAX_SIGNATURE_LEN;
    use vinc_wire::hlc::Hlc;

    use super::*;
    use crate::wire::MID_LEN;

    const ALGS: [IdentityAlg; 4] = [
        IdentityAlg::Ed25519,
        IdentityAlg::EcdsaP256,
        IdentityAlg::MlDsa65,
        IdentityAlg::Hybrid,
    ];

    fn key(alg: IdentityAlg, seed: u8) -> Keypair {
        Keypair::from_seed(alg, &vec![seed; alg.seed_len()]).unwrap()
    }

    /// The public key of `key` as a head carries it: empty for Ed25519.
    fn pk_of(alg: IdentityAlg, key: &Keypair) -> Vec<u8> {
        let mut pk = vec![0u8; alg.public_key_len()];
        key.public_key(&mut pk).unwrap();
        if alg == IdentityAlg::Ed25519 { Vec::new() } else { pk }
    }

    /// A head of `origin` and `pk` over `body`, signed by `signer`, as the wire carries it.
    fn head_of(alg: IdentityAlg, origin: &[u8; 32], pk: &[u8], signer: &Keypair, topic: &[u8], body: &[u8]) -> Vec<u8> {
        let mid = auth::message_id(origin, 1, 1, topic);
        let ts = Hlc::new(1_700_000_000_123, 7);
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let n = auth::sign(signer, topic, &mid, body, ts, true, &mut sig).unwrap();
        let head = Head {
            mid,
            origin,
            alg,
            pk,
            sig: &sig[..n],
            isb: true,
            ts,
        };
        let mut bytes = Vec::new();
        head.write(u32::try_from(body.len()).unwrap(), &mut bytes);
        assert_eq!(bytes.len(), head.len());
        bytes
    }

    /// A message of `alg` signed by its own key `seed`: the head bytes.
    fn signed(alg: IdentityAlg, seed: u8, topic: &[u8], body: &[u8]) -> Vec<u8> {
        let k = key(alg, seed);
        head_of(alg, &k.node_id().bytes, &pk_of(alg, &k), &k, topic, body)
    }

    fn encoded(topic: &[u8], head: &[u8], body: &[u8]) -> Vec<u8> {
        let e = Envelope::topic(topic, head, body);
        let mut out = Vec::new();
        e.encode_into(&mut out);
        assert_eq!(out.len(), e.encoded_len());
        out
    }

    #[test]
    fn encode_then_decode_gives_the_same_parts() {
        let longest = vec![b't'; MAX_TOPIC];
        for alg in ALGS {
            for (topic, blen) in [(&b""[..], 0), (b"a", 1), (b"news", 5), (b"news", 70_000), (&longest, 3)] {
                let body = vec![0xAB; blen];
                let head = signed(alg, 9, topic, &body);
                let bytes = encoded(topic, &head, &body);
                let e = Envelope::decode(&bytes).unwrap();
                assert_eq!(
                    (e.kind, e.topic, e.head, e.body),
                    (KIND_TOPIC_V1, topic, &head[..], &body[..]),
                    "{alg:?} {blen}"
                );
                let v = verify_bytes(&bytes).unwrap();
                assert_eq!((v.topic, v.payload, v.alg), (topic, &body[..], alg));
            }
        }
    }

    #[test]
    fn a_verified_envelope_names_origin_id_time_and_flag() {
        let k = key(IdentityAlg::Ed25519, 9);
        let head = signed(IdentityAlg::Ed25519, 9, b"news", b"hello");
        let bytes = encoded(b"news", &head, b"hello");
        let v = verify_bytes(&bytes).unwrap();
        assert_eq!(*v.origin, k.node_id().bytes);
        assert_eq!(v.author(), k.node_id());
        assert_eq!(v.mid, auth::message_id(&k.node_id().bytes, 1, 1, b"news"));
        assert_eq!((v.wall_ms, v.counter, v.isb), (1_700_000_000_123, 7, true));
    }

    #[test]
    fn every_single_bit_flip_is_an_error_for_every_algorithm() {
        for alg in ALGS {
            let head = signed(alg, 9, b"news", b"hello");
            let bytes = encoded(b"news", &head, b"hello");
            assert!(verify_bytes(&bytes).is_ok());
            for at in 0..bytes.len() {
                let mut b = bytes.clone();
                b[at] ^= 1 << (at % 8);
                assert!(verify_bytes(&b).is_err(), "{alg:?} byte {at}");
            }
        }
    }

    #[test]
    fn a_truncated_envelope_and_one_with_a_trailing_byte_are_malformed_for_every_algorithm() {
        for alg in ALGS {
            let head = signed(alg, 9, b"news", b"hello");
            let bytes = encoded(b"news", &head, b"hello");
            for cut in 0..bytes.len() {
                let got = verify_bytes(&bytes[..cut]);
                assert!(
                    matches!(got, Err(EnvelopeError::Malformed(_))),
                    "{alg:?} cut {cut}: {got:?}"
                );
            }
            let mut longer = bytes.clone();
            longer.push(0);
            assert!(
                matches!(verify_bytes(&longer), Err(EnvelopeError::Malformed(_))),
                "{alg:?}"
            );
        }
    }

    #[test]
    fn every_version_and_kind_but_one_is_refused_for_every_algorithm() {
        for alg in ALGS {
            let head = signed(alg, 9, b"news", b"hello");
            let bytes = encoded(b"news", &head, b"hello");
            for v in 0..=255u8 {
                let mut b = bytes.clone();
                b[0] = v;
                let want = if v == VERSION {
                    Ok(())
                } else {
                    Err(EnvelopeError::BadVersion)
                };
                assert_eq!(verify_bytes(&b).map(drop), want, "{alg:?} version {v}");
            }
            for k in 0..=255u8 {
                let mut b = bytes.clone();
                b[1] = k;
                let want = if k == KIND_TOPIC_V1 {
                    Ok(())
                } else {
                    Err(EnvelopeError::BadKind)
                };
                assert_eq!(verify_bytes(&b).map(drop), want, "{alg:?} kind {k}");
            }
            let e = Envelope {
                kind: 2,
                ..Envelope::topic(b"news", &head, b"hello")
            };
            assert_eq!(e.verify(), Err(EnvelopeError::BadKind));
        }
    }

    #[test]
    fn a_topic_over_the_bound_is_malformed() {
        let topic = vec![b't'; MAX_TOPIC + 1];
        let head = signed(IdentityAlg::Ed25519, 9, b"news", b"x");
        let bytes = encoded(&topic, &head, b"x");
        assert!(matches!(verify_bytes(&bytes), Err(EnvelopeError::Malformed(_))));
        assert!(matches!(
            Envelope::topic(&topic, &head, b"x").verify(),
            Err(EnvelopeError::Malformed(_))
        ));
    }

    #[test]
    fn parts_that_do_not_match_do_not_verify() {
        let head = signed(IdentityAlg::Ed25519, 9, b"news", b"hello");
        let ok = |topic: &'static [u8], body: &'static [u8]| Envelope::topic(topic, &head, body).verify();
        assert!(ok(b"news", b"hello").is_ok());
        assert!(matches!(ok(b"news", b"hell"), Err(EnvelopeError::Malformed(_))));
        assert_eq!(ok(b"news", b"jello"), Err(EnvelopeError::BadSignature));
        assert_eq!(ok(b"other", b"hello"), Err(EnvelopeError::BadSignature));
        assert!(matches!(
            Envelope::topic(b"news", &head[..MID_LEN], b"hello").verify(),
            Err(EnvelopeError::Malformed(_))
        ));
    }

    /// An origin that names B but carries A's signature, and (for every algorithm with a key in the head) B's id with
    /// A's public key, never verify.
    #[test]
    fn a_signature_by_another_key_does_not_verify() {
        for alg in ALGS {
            let (a, b) = (key(alg, 1), key(alg, 2));
            let (ida, idb) = (a.node_id().bytes, b.node_id().bytes);
            // B's id and B's key, A's signature.
            let head = head_of(alg, &idb, &pk_of(alg, &b), &a, b"news", b"hello");
            assert_eq!(
                Envelope::topic(b"news", &head, b"hello").verify(),
                Err(EnvelopeError::BadSignature),
                "{alg:?} origin B, signature A"
            );
            // B's id with A's key, A's signature: the key does not belong to the id.
            let head = head_of(alg, &idb, &pk_of(alg, &a), &a, b"news", b"hello");
            assert_eq!(
                Envelope::topic(b"news", &head, b"hello").verify(),
                Err(EnvelopeError::BadSignature),
                "{alg:?} origin B, key A"
            );
            // The control: A's id, A's key, A's signature.
            let head = head_of(alg, &ida, &pk_of(alg, &a), &a, b"news", b"hello");
            assert!(Envelope::topic(b"news", &head, b"hello").verify().is_ok(), "{alg:?}");
        }
    }
}
