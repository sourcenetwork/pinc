//! Signing and verification of a version 2 message: the signature covers the statement's content id.
//!
//! The signature is made over [`signed_message`] of the content id of the statement the head's fields build, so
//! a hub or a peer that alters the topic, the author, the position, the time, the flags, the parents or the body
//! breaks it. Signing and verifying go through `vinc-crypto` for every identity algorithm.
//!
//! Invariants: [`verify2`] returns an id only when the origin's key signed the statement of exactly this head, topic
//! and body; the key must match the origin's node id (an Ed25519 id is the key itself, every other id is a hash of
//! it).

use vinc_crypto::identity::verify_node;
use vinc_crypto::{IdentityAlg, Keypair, NodeId as CryptoId};

use crate::statement::{ContentId, Fields, STATEMENT_MAX, content_id, encode, signed_message};
use crate::wire2::Head2;

/// The content id of the statement of `fields`, or `None` if the fields do not make a statement.
fn id_of(fields: &Fields<'_>) -> Option<ContentId> {
    let mut buf = [0u8; STATEMENT_MAX];
    let n = encode(fields, &mut buf).ok()?;
    Some(content_id(buf.get(..n)?))
}

/// Sign the statement of `fields` with `key`, writing the signature to `out`; returns its length, or `None` if the
/// fields do not make a statement or `out` is too short.
pub fn sign2(key: &Keypair, fields: &Fields<'_>, out: &mut [u8]) -> Option<usize> {
    key.sign(&signed_message(&id_of(fields)?), out).ok()
}

/// The content id of the message `head` with `topic` and `body` if its origin signed it, otherwise `None`.
pub fn verify2(head: &Head2<'_>, topic: &[u8], body: &[u8]) -> Option<ContentId> {
    let hash = *blake3::hash(body).as_bytes();
    let id = id_of(&head.statement_fields(topic, &hash))?;
    let node = CryptoId {
        alg: head.alg,
        bytes: *head.origin,
    };
    let pk: &[u8] = if head.alg == IdentityAlg::Ed25519 {
        head.origin
    } else {
        head.pk
    };
    verify_node(&node, pk, &signed_message(&id), head.sig).ok()?;
    Some(id)
}

#[cfg(test)]
mod tests;
