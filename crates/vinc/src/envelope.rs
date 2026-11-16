//! The signed envelope of a topic message, to store and to verify offline.
//!
//! An endpoint built with [`Builder::envelopes`](crate::Builder::envelopes) hears every topic message with its
//! [`Envelope`]: the canonical bytes of the topic, the origin's signed head and the payload. Keep
//! [`as_bytes`](Envelope::as_bytes), hand it to anyone, and [`verify`] it later with no endpoint, no session and no
//! network.
//!
//! A verified envelope proves that the key behind the origin's id signed this topic, this message id, this exact
//! payload and this timestamp. It does not prove the key was unrevoked at that time, the message's position among
//! others (the id is not a content hash), or that anyone received it.
//!
//! Invariants: an envelope is one buffer, built once per delivered message; [`Envelope::from_bytes`] checks nothing, and
//! every check is in [`verify`].

pub use vinc_broadcast::envelope::{EnvelopeError, Verified, verify_bytes as verify};

/// The canonical bytes of a signed topic message: the topic, the origin's signed head and the payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Envelope(Vec<u8>);

impl Envelope {
    /// The envelope of a message from its parts; one allocation.
    pub(crate) fn new(topic: &[u8], head: &[u8], body: &[u8]) -> Self {
        let parts = vinc_broadcast::envelope::Envelope { topic, head, body };
        let mut bytes = Vec::with_capacity(parts.encoded_len());
        parts.encode_into(&mut bytes);
        Self(bytes)
    }

    /// An envelope read back from stored bytes. Nothing is checked here: [`verify`](Self::verify) does it.
    pub const fn from_bytes(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }

    /// The canonical bytes, to store or to hand to anyone.
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Check the origin's signature offline and say who signed what.
    ///
    /// # Errors
    /// [`EnvelopeError`] for bytes that are not an envelope or a signature that does not match.
    pub fn verify(&self) -> Result<Verified<'_>, EnvelopeError> {
        verify(&self.0)
    }
}
