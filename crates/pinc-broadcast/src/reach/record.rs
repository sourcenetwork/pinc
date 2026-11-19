//! The adjacency record on the wire: `origin32 alg1 [public_key] inc8 seq8 count2 peers32*count signature`.

use pinc_crypto::identity::verify_node;
use pinc_crypto::{IdentityAlg, NodeId as CryptoId};
use pinc_membership::NodeId;
use pinc_wire::Reader;

use crate::consts::ADJ_MAX;

pub(super) const LABEL: &str = "PINC 2026 v1 broadcast adjacency";

/// A record as it arrived.
pub(crate) struct View<'a> {
    pub(super) origin: &'a NodeId,
    alg: IdentityAlg,
    pk: &'a [u8],
    pub(super) inc: u64,
    pub(super) seq: u64,
    pub(super) peers: &'a [NodeId],
    signed: &'a [u8],
    pub(super) sig: &'a [u8],
}

/// The record in `rest`, if it is well formed: its peers sorted, without repeats and without its origin.
pub(crate) fn parse(rest: &[u8]) -> Option<View<'_>> {
    let mut r = Reader::new(rest);
    let origin = <&NodeId>::try_from(r.read_bytes(32).ok()?).ok()?;
    let alg = IdentityAlg::from_tag(r.read_u8().ok()?)?;
    let pk = if alg == IdentityAlg::Ed25519 {
        &[][..]
    } else {
        r.read_bytes(alg.public_key_len()).ok()?
    };
    let inc = r.read_u64().ok()?;
    let seq = r.read_u64().ok()?;
    let n = usize::from(r.read_u16().ok()?);
    if n > ADJ_MAX {
        return None;
    }
    let peers = r.read_bytes(n.checked_mul(32)?).ok()?.as_chunks::<32>().0;
    let signed = rest.get(..rest.len().checked_sub(r.remaining())?)?;
    let sig = r.read_bytes(alg.signature_len()).ok()?;
    // Sorted and without repeats, so a hub tests an edge by a binary search.
    if r.remaining() != 0 || !peers.is_sorted_by(|a, b| a < b) || peers.contains(origin) {
        return None;
    }
    Some(View {
        origin,
        alg,
        pk,
        inc,
        seq,
        peers,
        signed,
        sig,
    })
}

/// What the member signs: the record up to its signature, under [`LABEL`].
pub(super) fn digest(signed: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(LABEL)
        .update(signed)
        .finalize()
        .as_bytes()
}

/// Whether the record is signed by the key its origin id names.
pub(super) fn verify(v: &View<'_>) -> bool {
    let id = CryptoId {
        alg: v.alg,
        bytes: *v.origin,
    };
    let pk: &[u8] = if v.alg == IdentityAlg::Ed25519 { v.origin } else { v.pk };
    verify_node(&id, pk, &digest(v.signed), v.sig).is_ok()
}

/// What `parse` and `verify` make of a record's bytes, for the trace test.
#[cfg(feature = "trace")]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdjProbe {
    /// The origin's node id.
    pub origin: NodeId,
    /// The algorithm's tag.
    pub alg: u8,
    /// The public key carried (empty for Ed25519).
    pub pk: alloc::vec::Vec<u8>,
    /// The incarnation.
    pub inc: u64,
    /// The sequence number.
    pub seq: u64,
    /// The peers named.
    pub peers: alloc::vec::Vec<NodeId>,
    /// How many bytes the signature is over.
    pub signed_len: usize,
    /// The signature.
    pub sig: alloc::vec::Vec<u8>,
    /// Whether `verify` accepts it.
    pub verified: bool,
}

/// [`parse`] and [`verify`] of `rest`, for the trace test.
#[cfg(feature = "trace")]
pub(crate) fn probe(rest: &[u8]) -> Option<AdjProbe> {
    let v = parse(rest)?;
    Some(AdjProbe {
        origin: *v.origin,
        alg: v.alg.tag(),
        pk: v.pk.to_vec(),
        inc: v.inc,
        seq: v.seq,
        peers: v.peers.to_vec(),
        signed_len: v.signed.len(),
        sig: v.sig.to_vec(),
        verified: verify(&v),
    })
}
