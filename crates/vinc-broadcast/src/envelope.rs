//! The signed envelope of a topic message: the topic, the exact wire head and the body, as one value an application
//! can store, hand to anyone and verify later with no endpoint, no session and no network.
//!
//! The canonical bytes are `version1 | kind1 | topic_len2 | topic | head | body`, with the lengths big endian and `head`
//! exactly as it travels ([`Head`]; it names the body's length in `blen`). Version 1 and kind 1 (a topic message) are
//! the only ones defined.
//!
//! What a verified envelope proves: the key behind `origin` signed this topic, this message id, this exact payload and
//! this timestamp. What it does not prove: that the key was unrevoked at that time, the message's position among
//! others (the id is a position hash, not a content hash), or that anyone received it.
//!
//! Invariants: [`Envelope::decode`] validates the whole structure at this boundary (version, kind, the topic bound,
//! the head, the body length, no trailing byte) and never panics or reads outside its input; [`Envelope::verify`]
//! re-checks the parts it is given, so an envelope built by hand cannot verify unless it is well formed; neither
//! allocates.

use vinc_membership::NodeId;
use vinc_wire::Reader;

use crate::auth;
use crate::consts::MAX_TOPIC;
use crate::wire::{Head, Malformed};
use vinc_crypto::IdentityAlg;

/// The version of the canonical encoding.
pub const VERSION: u8 = 1;
/// The kind of a topic message.
pub const KIND_TOPIC: u8 = 1;
/// The bytes before the topic: version, kind and the topic length.
const PREFIX: usize = 4;

/// Why an envelope was not accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnvelopeError {
    /// The version is not one this library knows.
    BadVersion,
    /// The kind is not one this library knows.
    BadKind,
    /// The bytes are not a well-formed envelope, named by the reason.
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
    fn from(m: Malformed) -> Self {
        Self::Malformed(m.0)
    }
}

/// What a verified envelope proves, borrowed from its bytes. See the module docs for what it does not prove.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Verified<'a> {
    /// The origin's node id: the identity whose key signed.
    pub origin: &'a NodeId,
    /// The origin's signature algorithm.
    pub alg: IdentityAlg,
    /// The topic.
    pub topic: &'a [u8],
    /// The payload.
    pub payload: &'a [u8],
    /// The message id.
    pub mid: [u8; 8],
    /// The signed timestamp's physical part, in milliseconds.
    pub wall_ms: u64,
    /// The signed timestamp's logical part, which orders messages inside one millisecond.
    pub counter: u32,
}

/// The parts of a signed topic message, borrowed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Envelope<'a> {
    /// The topic.
    pub topic: &'a [u8],
    /// The message head exactly as the wire carries it.
    pub head: &'a [u8],
    /// The body.
    pub body: &'a [u8],
}

impl<'a> Envelope<'a> {
    /// The length of the canonical encoding.
    pub const fn encoded_len(&self) -> usize {
        PREFIX + self.topic.len() + self.head.len() + self.body.len()
    }

    /// Append the canonical encoding to `out`. A topic over 65535 bytes has a length that does not fit its field, and
    /// the encoding is then refused by [`Envelope::decode`] like any topic over the layer's bound.
    pub fn encode_into(&self, out: &mut impl Extend<u8>) {
        out.extend([VERSION, KIND_TOPIC]);
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
        const CUT: EnvelopeError = EnvelopeError::Malformed("the envelope is cut short");
        let mut r = Reader::new(bytes);
        if r.read_u8().map_err(|_| CUT)? != VERSION {
            return Err(EnvelopeError::BadVersion);
        }
        if r.read_u8().map_err(|_| CUT)? != KIND_TOPIC {
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
            topic,
            head: rest.get(..head.len()).ok_or(CUT)?,
            body: tail,
        })
    }

    /// Check the origin's signature over the topic, the message id, the body and the timestamp, and that its key is
    /// the origin's. The parts are validated again, so an envelope built by hand verifies only if it is well formed.
    ///
    /// # Errors
    /// [`EnvelopeError::Malformed`] if a part does not fit the format; [`EnvelopeError::BadSignature`] if the
    /// signature does not match.
    pub fn verify(&self) -> Result<Verified<'a>, EnvelopeError> {
        if self.topic.len() > MAX_TOPIC {
            return Err(EnvelopeError::Malformed("the topic is too long"));
        }
        let (head, blen, tail) = Head::parse_prefix(self.head)?;
        if !tail.is_empty() || blen != self.body.len() {
            return Err(EnvelopeError::Malformed("the body length differs from the head"));
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

    /// A signed message of `alg`: the topic, the head bytes and the body, as the wire carries them.
    fn signed(alg: IdentityAlg, topic: &[u8], body: &[u8]) -> (Keypair, Vec<u8>) {
        let key = Keypair::from_seed(alg, &vec![9; alg.seed_len()]).unwrap();
        let id = key.node_id();
        let mid = auth::message_id(&id.bytes, 1, 1, topic);
        let ts = Hlc::new(1_700_000_000_123, 7);
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let n = auth::sign(&key, topic, &mid, body, ts, true, &mut sig).unwrap();
        let mut pk = vec![0u8; alg.public_key_len()];
        key.public_key(&mut pk).unwrap();
        let head = Head {
            mid,
            origin: &id.bytes,
            alg,
            pk: if alg == IdentityAlg::Ed25519 { &[] } else { &pk },
            sig: &sig[..n],
            isb: true,
            ts,
        };
        let mut bytes = Vec::new();
        head.write(u32::try_from(body.len()).unwrap(), &mut bytes);
        assert_eq!(bytes.len(), head.len());
        (key, bytes)
    }

    fn encoded(topic: &[u8], head: &[u8], body: &[u8]) -> Vec<u8> {
        let e = Envelope { topic, head, body };
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
                let (_, head) = signed(alg, topic, &body);
                let bytes = encoded(topic, &head, &body);
                let e = Envelope::decode(&bytes).unwrap();
                assert_eq!(
                    (e.topic, e.head, e.body),
                    (topic, &head[..], &body[..]),
                    "{alg:?} {blen}"
                );
                let v = verify_bytes(&bytes).unwrap();
                assert_eq!((v.topic, v.payload, v.alg), (topic, &body[..], alg));
            }
        }
    }

    #[test]
    fn a_verified_envelope_names_origin_id_and_time() {
        let (key, head) = signed(IdentityAlg::Ed25519, b"news", b"hello");
        let bytes = encoded(b"news", &head, b"hello");
        let v = verify_bytes(&bytes).unwrap();
        assert_eq!(*v.origin, key.node_id().bytes);
        assert_eq!(v.mid, auth::message_id(&key.node_id().bytes, 1, 1, b"news"));
        assert_eq!((v.wall_ms, v.counter), (1_700_000_000_123, 7));
    }

    #[test]
    fn every_single_byte_flip_fails_or_changes_the_result() {
        for alg in [IdentityAlg::Ed25519, IdentityAlg::EcdsaP256] {
            let (_, head) = signed(alg, b"news", b"hello");
            let bytes = encoded(b"news", &head, b"hello");
            let original = verify_bytes(&bytes).unwrap();
            for at in 0..bytes.len() {
                for bit in [0x01, 0x80] {
                    let mut b = bytes.clone();
                    b[at] ^= bit;
                    if let Ok(v) = verify_bytes(&b) {
                        assert_ne!(v, original, "{alg:?} byte {at} bit {bit}");
                    }
                }
            }
        }
    }

    #[test]
    fn a_truncated_envelope_and_one_with_a_trailing_byte_are_malformed() {
        let (_, head) = signed(IdentityAlg::Ed25519, b"news", b"hello");
        let bytes = encoded(b"news", &head, b"hello");
        for cut in 0..bytes.len() {
            let got = verify_bytes(&bytes[..cut]);
            assert!(matches!(got, Err(EnvelopeError::Malformed(_))), "cut {cut}: {got:?}");
        }
        let mut longer = bytes.clone();
        longer.push(0);
        assert!(matches!(verify_bytes(&longer), Err(EnvelopeError::Malformed(_))));
    }

    #[test]
    fn an_unknown_version_or_kind_is_named() {
        let (_, head) = signed(IdentityAlg::Ed25519, b"news", b"hello");
        let mut bytes = encoded(b"news", &head, b"hello");
        bytes[0] = 2;
        assert_eq!(verify_bytes(&bytes), Err(EnvelopeError::BadVersion));
        bytes[0] = VERSION;
        bytes[1] = 2;
        assert_eq!(verify_bytes(&bytes), Err(EnvelopeError::BadKind));
    }

    #[test]
    fn a_topic_over_the_bound_is_malformed() {
        let topic = vec![b't'; MAX_TOPIC + 1];
        let (_, head) = signed(IdentityAlg::Ed25519, b"news", b"x");
        let bytes = encoded(&topic, &head, b"x");
        assert!(matches!(verify_bytes(&bytes), Err(EnvelopeError::Malformed(_))));
        let e = Envelope {
            topic: &topic,
            head: &head,
            body: b"x",
        };
        assert!(matches!(e.verify(), Err(EnvelopeError::Malformed(_))));
    }

    #[test]
    fn parts_that_do_not_match_do_not_verify() {
        let (_, head) = signed(IdentityAlg::Ed25519, b"news", b"hello");
        let ok = |topic: &'static [u8], body: &'static [u8]| {
            Envelope {
                topic,
                head: &head,
                body,
            }
            .verify()
        };
        assert!(ok(b"news", b"hello").is_ok());
        assert!(matches!(ok(b"news", b"hell"), Err(EnvelopeError::Malformed(_))));
        assert_eq!(ok(b"news", b"jello"), Err(EnvelopeError::BadSignature));
        assert_eq!(ok(b"other", b"hello"), Err(EnvelopeError::BadSignature));
        assert!(matches!(
            Envelope {
                topic: b"news",
                head: &head[..MID_LEN],
                body: b"hello"
            }
            .verify(),
            Err(EnvelopeError::Malformed(_))
        ));
    }
}
