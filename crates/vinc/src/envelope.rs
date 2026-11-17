//! The signed envelope of a topic message, to store and to verify offline.
//!
//! An endpoint built with [`Builder::envelopes`](crate::Builder::envelopes) hears every topic message as an
//! [`Event::Envelope`](crate::Event::Envelope): the canonical bytes of the topic, the origin's signed head and the
//! payload. Keep [`as_bytes`](Envelope::as_bytes) or [`into_bytes`](Envelope::into_bytes), hand it to anyone, and
//! [`verify`] it later with no endpoint, no session and no network.
//!
//! A verified envelope proves that the key behind the origin's id signed this topic, this message id, this exact
//! payload and this timestamp. It does not prove the key was unrevoked at that time, the message's position among
//! others (the id is not a content hash), or that anyone received it. A kind 1 statement carries no label of its own
//! (it begins with the topic's bytes), so a kind 1 proof also holds for a raw signature by the same key over bytes of
//! that shape: an application that signs bytes a peer chose with [`Endpoint::sign`](crate::Endpoint::sign) can be made
//! to produce one (vinc#572; the guard of `sign` refuses the reserved label prefixes, which an unlabelled topic statement does not
//! carry).
//!
//! Invariants: an envelope is one buffer, built once per delivered message by the node; every check is in [`verify`].

pub use vinc_broadcast::envelope::{Envelope, EnvelopeError, Verified, verify_bytes as verify};
