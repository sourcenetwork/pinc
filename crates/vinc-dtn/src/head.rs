//! The bundle head: what a bundle is, who sent it, who it is for, and the root of its sealed slices.
//!
//! The head carries the bundle id, the source and destination node ids, the creation time (a hybrid logical clock),
//! the lifetime, the copy budget, the erasure parameters, the payload length, the tree root, and the encryption
//! envelope (key epoch, ephemeral X25519 key and ML-KEM ciphertext). The sender signs the head with its identity key
//! ([`SignedHead`]); the signature covers every field, so the root, and through it every slice, is authentic.
//!
//! Invariants: the encoding is fixed-width and canonical (one byte string per head); decoding validates every field
//! at the trust boundary (known identity tags, a valid [`SliceLayout`]) and rejects trailing bytes; the copy budget
//! in the head is the initial one, each holder tracks its own share separately; the signature works with every
//! identity algorithm, since the signer's public key travels with it and is checked against the source node id.

use vinc_crypto::provider::KEM_CIPHERTEXT_LEN;
use vinc_crypto::{IdentityAlg, Keypair, NodeId, Transcript};
use vinc_wire::{Reader, Writer};

use crate::endorse::Endorsement;
use crate::error::DtnError;
use crate::hlc::Hlc;
use crate::labels;
use crate::layout::SliceLayout;
use crate::store::{Key, Space};

/// A bundle identifier: 32 bytes bound to the source, the creation time and the fresh ephemeral key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BundleId(pub [u8; 32]);

impl BundleId {
    /// The id for a bundle from `source` created at `created` with the ephemeral X25519 public key `eph`.
    pub fn derive(source: &NodeId, created: Hlc, eph: &[u8; 32]) -> Self {
        let mut t = Transcript::with_label(labels::BUNDLE_ID);
        absorb_node(&mut t, source);
        t.absorb(&created.wall.to_be_bytes());
        t.absorb(&created.counter.to_be_bytes());
        t.absorb(eph);
        Self(t.snapshot())
    }
}

impl BundleId {
    /// The store key under which the bundle is charged: the same key everywhere that kept bundles are looked up.
    pub const fn store_key(&self) -> Key {
        Key {
            space: Space::DTN,
            id: self.0,
        }
    }
}

/// Absorb a node id into a transcript as its algorithm tag and its 32 bytes.
pub(crate) fn absorb_node(t: &mut Transcript, node: &NodeId) {
    t.absorb(&[node.alg.tag()]);
    t.absorb(&node.bytes);
}

/// The one-shot encryption envelope of a bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Envelope {
    /// The recipient's static-key epoch the sender used.
    pub epoch: u32,
    /// The sender's fresh ephemeral X25519 public key.
    pub eph_x25519: [u8; 32],
    /// The ML-KEM-768 ciphertext for the recipient's static encapsulation key.
    pub kem_ct: [u8; KEM_CIPHERTEXT_LEN],
}

/// The erasure parameters: `k` data and `m` parity symbols per block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Erasure {
    /// Data symbols per block (at least 1).
    pub k: u8,
    /// Parity symbols per block.
    pub m: u8,
}

/// The signed fields of a bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Head {
    /// The bundle id.
    pub id: BundleId,
    /// The sender.
    pub source: NodeId,
    /// The recipient.
    pub destination: NodeId,
    /// The creation time.
    pub created: Hlc,
    /// How long the bundle lives after `created.wall`, in milliseconds.
    pub lifetime_ms: u64,
    /// The initial copy budget for spray-and-wait forwarding.
    pub copies: u16,
    /// The erasure parameters.
    pub erasure: Erasure,
    /// The slice size log (slices of `1024 << slice_log` bytes).
    pub slice_log: u8,
    /// The payload length in bytes.
    pub payload_len: u64,
    /// The BLAKE3 root of the sealed symbols.
    pub root: [u8; 32],
    /// The encryption envelope.
    pub envelope: Envelope,
}

/// The encoded size of a [`Head`].
pub const HEAD_LEN: usize = 32 + 2 * 33 + 12 + 8 + 2 + 2 + 1 + 8 + 32 + 4 + 32 + KEM_CIPHERTEXT_LEN;

fn put_node(w: &mut Writer<'_>, n: &NodeId) -> Result<(), DtnError> {
    w.put_u8(n.alg.tag())?;
    w.put_slice(&n.bytes)?;
    Ok(())
}

fn get_node(r: &mut Reader<'_>) -> Result<NodeId, DtnError> {
    let alg = IdentityAlg::from_tag(r.read_u8()?).ok_or(DtnError::Params)?;
    Ok(NodeId {
        alg,
        bytes: r.read_array()?,
    })
}

impl Head {
    /// The geometry of this bundle.
    ///
    /// # Errors
    /// [`DtnError::Params`] if the erasure parameters, slice size or payload length are invalid.
    pub fn layout(&self) -> Result<SliceLayout, DtnError> {
        SliceLayout::new(self.erasure.k, self.erasure.m, self.slice_log, self.payload_len)
    }

    /// The physical time (milliseconds) at which the bundle expires.
    pub const fn expires_at(&self) -> u64 {
        self.created.expires_at(self.lifetime_ms)
    }

    /// Whether the bundle is expired at physical time `now`.
    pub const fn is_expired(&self, now: u64) -> bool {
        self.expires_at() <= now
    }

    /// Encode into the start of `out`, returning [`HEAD_LEN`].
    ///
    /// # Errors
    /// [`DtnError::Wire`] if `out` is shorter than [`HEAD_LEN`].
    pub fn encode(&self, out: &mut [u8]) -> Result<usize, DtnError> {
        let mut w = Writer::new(out);
        self.write(&mut w)?;
        Ok(w.written().len())
    }

    fn write(&self, w: &mut Writer<'_>) -> Result<(), DtnError> {
        w.put_slice(&self.id.0)?;
        put_node(w, &self.source)?;
        put_node(w, &self.destination)?;
        w.put_u64(self.created.wall)?;
        w.put_u32(self.created.counter)?;
        w.put_u64(self.lifetime_ms)?;
        w.put_u16(self.copies)?;
        w.put_u8(self.erasure.k)?;
        w.put_u8(self.erasure.m)?;
        w.put_u8(self.slice_log)?;
        w.put_u64(self.payload_len)?;
        w.put_slice(&self.root)?;
        w.put_u32(self.envelope.epoch)?;
        w.put_slice(&self.envelope.eph_x25519)?;
        w.put_slice(&self.envelope.kem_ct)?;
        Ok(())
    }

    fn read(r: &mut Reader<'_>) -> Result<Self, DtnError> {
        let head = Self {
            id: BundleId(r.read_array()?),
            source: get_node(r)?,
            destination: get_node(r)?,
            created: Hlc::new(r.read_u64()?, r.read_u32()?),
            lifetime_ms: r.read_u64()?,
            copies: r.read_u16()?,
            erasure: Erasure {
                k: r.read_u8()?,
                m: r.read_u8()?,
            },
            slice_log: r.read_u8()?,
            payload_len: r.read_u64()?,
            root: r.read_array()?,
            envelope: Envelope {
                epoch: r.read_u32()?,
                eph_x25519: r.read_array()?,
                kem_ct: r.read_array()?,
            },
        };
        head.layout()?;
        Ok(head)
    }
}

/// A [`Head`] with the sender's signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedHead {
    head: Head,
    endorsement: Endorsement,
}

/// The longest encoded [`SignedHead`], for sizing a buffer that fits every identity algorithm.
pub const MAX_SIGNED_HEAD_LEN: usize =
    HEAD_LEN + 4 + vinc_crypto::identity::MAX_PUBLIC_KEY_LEN + vinc_crypto::identity::MAX_SIGNATURE_LEN;

impl SignedHead {
    /// Sign `head` with `signer`, which must be the head's source.
    ///
    /// # Errors
    /// [`DtnError::Params`] if the head is not valid or `signer` is not `head.source`; [`DtnError::Crypto`] if
    /// signing fails.
    pub fn sign(head: Head, signer: &Keypair) -> Result<Self, DtnError> {
        head.layout()?;
        if signer.node_id() != head.source {
            return Err(DtnError::Params);
        }
        let mut body = [0u8; HEAD_LEN];
        head.encode(&mut body)?;
        Ok(Self {
            head,
            endorsement: Endorsement::sign(signer, labels::HEAD, &body)?,
        })
    }

    /// The head. It is authentic only after [`SignedHead::verify`] succeeded.
    pub const fn head(&self) -> &Head {
        &self.head
    }

    /// Check that the source node signed this head.
    ///
    /// # Errors
    /// [`DtnError::Crypto`] if the key does not belong to the source or the signature does not verify.
    pub fn verify(&self) -> Result<(), DtnError> {
        let mut body = [0u8; HEAD_LEN];
        self.head.encode(&mut body)?;
        self.endorsement.verify(&self.head.source, labels::HEAD, &body)
    }

    /// The encoded length for the source's identity algorithm.
    pub const fn encoded_len(&self) -> usize {
        HEAD_LEN + Endorsement::encoded_len(self.head.source.alg)
    }

    /// Encode into the start of `out`, returning the length.
    ///
    /// # Errors
    /// [`DtnError::Wire`] if `out` is too short.
    pub fn encode(&self, out: &mut [u8]) -> Result<usize, DtnError> {
        let mut w = Writer::new(out);
        self.head.write(&mut w)?;
        self.endorsement.encode(&mut w)?;
        Ok(w.written().len())
    }

    /// Decode and validate the structure. The signature is not checked: call [`SignedHead::verify`].
    ///
    /// # Errors
    /// [`DtnError::Wire`] or [`DtnError::Params`] for malformed input or trailing bytes.
    pub fn decode(bytes: &[u8]) -> Result<Self, DtnError> {
        let mut r = Reader::new(bytes);
        let head = Head::read(&mut r)?;
        let endorsement = Endorsement::decode(head.source.alg, &mut r)?;
        if !r.is_empty() {
            return Err(DtnError::Params);
        }
        Ok(Self { head, endorsement })
    }
}
