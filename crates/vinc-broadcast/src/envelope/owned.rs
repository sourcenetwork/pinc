//! The owned envelope: the canonical bytes of one topic message in a single allocation, with the offsets that cut the
//! topic, the head and the payload out of them. Invariant: it is built only by [`EnvelopeRef::into_owned`], so its
//! offsets always lie inside its bytes and in order.

use alloc::boxed::Box;
use alloc::vec::Vec;

use super::{EnvelopeError, EnvelopeRef, PREFIX, Verified, verify_bytes};

/// A signed topic message as one owned value: the topic, the origin's signed head and the payload, in the canonical
/// bytes of [`EnvelopeRef::encode_into`]. Store [`Envelope::as_bytes`] or [`Envelope::into_bytes`] and verify them
/// later with [`verify_bytes`]. Invariants: `PREFIX <= head_at <= body_at <= bytes.len()`, set only by
/// [`EnvelopeRef::into_owned`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Envelope {
    bytes: Box<[u8]>,
    head_at: usize,
    body_at: usize,
}

impl EnvelopeRef<'_> {
    /// The owned envelope of these parts: one allocation, each byte copied once.
    pub fn into_owned(self) -> Envelope {
        let mut bytes = Vec::with_capacity(self.encoded_len());
        self.encode_into(&mut bytes);
        let head_at = PREFIX + self.topic.len();
        Envelope {
            bytes: bytes.into_boxed_slice(),
            head_at,
            body_at: head_at + self.head.len(),
        }
    }
}

impl Envelope {
    /// The topic.
    pub fn topic(&self) -> &[u8] {
        self.bytes.get(PREFIX..self.head_at).unwrap_or_default()
    }

    /// The payload.
    pub fn payload(&self) -> &[u8] {
        self.bytes.get(self.body_at..).unwrap_or_default()
    }

    /// The canonical bytes: what to store and hand to anyone.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// The canonical bytes, moved out without a copy.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes.into_vec()
    }

    /// Check the origin's signature, as [`verify_bytes`] does on the stored bytes.
    ///
    /// # Errors
    /// Any [`EnvelopeError`] of [`verify_bytes`].
    pub fn verify(&self) -> Result<Verified<'_>, EnvelopeError> {
        verify_bytes(&self.bytes)
    }
}
