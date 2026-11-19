//! Signing and verification of a version 2 message: the signature covers the statement's content id.
//!
//! The signature is made over [`signed_message`] of the content id of the statement the head's fields build, so
//! a hub or a peer that alters the topic, the author, the position, the time, the flags, the parents or the body
//! breaks it. Signing and verifying go through `pinc-crypto` for every identity algorithm.
//!
//! Invariants: [`verify2`] returns an id only when the origin's key signed the statement of exactly this head, topic
//! and body; the key must match the origin's node id (an Ed25519 id is the key itself, every other id is a hash of
//! it). [`sign2`] writes nothing unless it signs.

use pinc_crypto::Keypair;

use crate::auth::origin_signed;
use crate::statement::{ContentId, Fields, STATEMENT_MAX, content_id, encode, signed_message};
use crate::wire2::Head2;

/// The content id of the statement of `fields`, or `None` if the fields do not make a statement.
fn id_of(fields: &Fields<'_>) -> Option<ContentId> {
    let mut buf = [0u8; STATEMENT_MAX];
    let n = encode(fields, &mut buf).ok()?;
    Some(content_id(buf.get(..n)?))
}

/// Sign the statement of `fields` with `key`, writing the signature to `out`; returns its length and the content id,
/// or `None` (and writes nothing) if the fields do not make a statement, the key's algorithm is not the fields'
/// `origin_alg`, or `out` is too short.
pub fn sign2(key: &Keypair, fields: &Fields<'_>, out: &mut [u8]) -> Option<(usize, ContentId)> {
    if key.alg() != fields.origin_alg {
        return None;
    }
    let id = id_of(fields)?;
    let n = key.sign(&signed_message(&id), out).ok()?;
    Some((n, id))
}

/// The content id of the message `head` with `topic` and `body` if its origin signed it, otherwise `None`.
pub fn verify2(head: &Head2<'_>, topic: &[u8], body: &[u8]) -> Option<ContentId> {
    let hash = *blake3::hash(body).as_bytes();
    let id = id_of(&head.statement_fields(topic, &hash))?;
    origin_signed(head.alg, head.origin, head.pk, &signed_message(&id), head.sig).then_some(id)
}

#[cfg(test)]
mod tests;
