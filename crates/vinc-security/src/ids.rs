//! Small identifiers and parameters shared by the handshake messages and the state machines.
//!
//! Invariants: a [`ConnId`] is at most [`MAX_CID_LEN`] bytes and an [`Alpn`] is 1 to [`MAX_ALPN_LEN`] bytes; both keep
//! their unused tail zero, so equality is equality of the visible bytes; an [`AeadSet`] is never empty and holds no
//! unknown bit. A [`LocalIdentity`] holds only public data and a [`KeyHandle`]: the signing key itself never enters
//! this crate.

use vinc_crypto::identity::MAX_PUBLIC_KEY_LEN;
use vinc_crypto::{Aead, Capabilities, CryptoError, IdentityAlg, Keypair, NodeId};

/// The protocol version: one byte in the Initial, the resume Hello and the transcript. The transport's packet header
/// carries the same byte.
pub const VERSION: u8 = 1;
/// The longest connection id.
pub const MAX_CID_LEN: usize = 20;
/// The longest ALPN.
pub const MAX_ALPN_LEN: usize = 32;
/// The most ALPNs a responder serves: the hub protocol of the node and the application's protocols.
pub const MAX_ALPNS: usize = 8;

/// A connection id of 0 to [`MAX_CID_LEN`] bytes, stored inline.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct ConnId {
    len: u8,
    bytes: [u8; MAX_CID_LEN],
}

impl ConnId {
    /// A connection id of `bytes`, or `None` if it is longer than [`MAX_CID_LEN`].
    pub fn new(bytes: &[u8]) -> Option<Self> {
        let mut id = Self {
            len: u8::try_from(bytes.len())
                .ok()
                .filter(|l| usize::from(*l) <= MAX_CID_LEN)?,
            bytes: [0; MAX_CID_LEN],
        };
        id.bytes.get_mut(..bytes.len())?.copy_from_slice(bytes);
        Some(id)
    }

    /// The id's bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.bytes.get(..usize::from(self.len)).unwrap_or_default()
    }
}

/// An application protocol name of 1 to [`MAX_ALPN_LEN`] bytes, stored inline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Alpn {
    len: u8,
    bytes: [u8; MAX_ALPN_LEN],
}

impl Alpn {
    /// An ALPN of `bytes`, or `None` if it is empty or longer than [`MAX_ALPN_LEN`].
    pub fn new(bytes: &[u8]) -> Option<Self> {
        let mut alpn = Self {
            len: u8::try_from(bytes.len())
                .ok()
                .filter(|l| (1..=MAX_ALPN_LEN).contains(&usize::from(*l)))?,
            bytes: [0; MAX_ALPN_LEN],
        };
        alpn.bytes.get_mut(..bytes.len())?.copy_from_slice(bytes);
        Some(alpn)
    }

    /// The ALPN's bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.bytes.get(..usize::from(self.len)).unwrap_or_default()
    }
}

/// The ALPNs a responder serves: up to [`MAX_ALPNS`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AlpnList {
    len: u8,
    items: [Option<Alpn>; MAX_ALPNS],
}

impl AlpnList {
    /// A list of `alpns`, or `None` if there are none, more than [`MAX_ALPNS`], or one is invalid.
    pub fn new(alpns: &[&[u8]]) -> Option<Self> {
        if alpns.is_empty() || alpns.len() > MAX_ALPNS {
            return None;
        }
        let mut list = Self {
            len: 0,
            items: [None; MAX_ALPNS],
        };
        for (slot, a) in list.items.iter_mut().zip(alpns) {
            *slot = Some(Alpn::new(a)?);
            list.len += 1;
        }
        Some(list)
    }

    /// The served ALPN equal to `wanted`, if any.
    pub fn find(&self, wanted: &[u8]) -> Option<Alpn> {
        self.items.iter().flatten().find(|a| a.as_bytes() == wanted).copied()
    }
}

/// The wire tag of an AEAD: 1 for ChaCha20-Poly1305, 2 for AES-128-GCM.
pub const fn aead_tag(aead: Aead) -> u8 {
    match aead {
        Aead::ChaCha20Poly1305 => 1,
        Aead::Aes128Gcm => 2,
    }
}

/// The AEAD of a wire tag, or `None` for an unknown tag.
pub const fn aead_from_tag(tag: u8) -> Option<Aead> {
    match tag {
        1 => Some(Aead::ChaCha20Poly1305),
        2 => Some(Aead::Aes128Gcm),
        _ => None,
    }
}

/// A non-empty set of AEADs on the wire: bit 0 is ChaCha20-Poly1305, bit 1 is AES-128-GCM.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AeadSet(u8);

impl AeadSet {
    /// The set of one AEAD.
    pub const CHACHA: Self = Self(1);

    /// What a node with `caps` offers: ChaCha20-Poly1305 always, AES-128-GCM only on hardware AES and carry-less
    /// multiplication.
    pub const fn offer(caps: Capabilities) -> Self {
        Self(if caps.aes_gcm_hw { 3 } else { 1 })
    }

    /// The set of wire bits `bits`, or `None` if it is empty or has an unknown bit.
    pub const fn from_bits(bits: u8) -> Option<Self> {
        if bits == 0 || bits > 3 { None } else { Some(Self(bits)) }
    }

    /// The wire bits.
    pub const fn bits(self) -> u8 {
        self.0
    }

    /// Whether `aead` is in the set.
    pub const fn contains(self, aead: Aead) -> bool {
        self.0 & aead_tag(aead) != 0
    }

    /// The AEAD both sets allow, preferring AES-128-GCM, or `None` if they share none.
    pub const fn choose(self, other: Self) -> Option<Aead> {
        let common = self.0 & other.0;
        if common & 2 != 0 {
            Some(Aead::Aes128Gcm)
        } else if common & 1 != 0 {
            Some(Aead::ChaCha20Poly1305)
        } else {
            None
        }
    }
}

/// An opaque name for a key held by the host: a signing key or a prekey decapsulation key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct KeyHandle(pub u64);

/// The identity this node authenticates with: its node id, its public key and the handle of its signing key.
#[derive(Debug, Clone, Copy)]
pub struct LocalIdentity {
    node: NodeId,
    public_key: [u8; MAX_PUBLIC_KEY_LEN],
    key: KeyHandle,
}

impl LocalIdentity {
    /// An identity from a public key and the handle under which the host signs for it.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if `public_key` has the wrong length for `alg`.
    pub fn new(alg: IdentityAlg, public_key: &[u8], key: KeyHandle) -> Result<Self, CryptoError> {
        let node = NodeId::from_public(alg, public_key)?;
        let mut stored = [0; MAX_PUBLIC_KEY_LEN];
        stored
            .get_mut(..public_key.len())
            .ok_or(CryptoError::InvalidLength)?
            .copy_from_slice(public_key);
        Ok(Self {
            node,
            public_key: stored,
            key,
        })
    }

    /// The identity of a software key pair.
    ///
    /// # Errors
    /// Never fails for a well-formed key pair; the error type matches [`LocalIdentity::new`].
    pub fn from_keypair(keypair: &Keypair, key: KeyHandle) -> Result<Self, CryptoError> {
        let mut pk = [0; MAX_PUBLIC_KEY_LEN];
        let n = keypair.public_key(&mut pk)?;
        Self::new(keypair.alg(), pk.get(..n).ok_or(CryptoError::InvalidLength)?, key)
    }

    /// The node id.
    pub const fn node_id(&self) -> NodeId {
        self.node
    }

    /// The signature algorithm.
    pub const fn alg(&self) -> IdentityAlg {
        self.node.alg
    }

    /// The public key.
    pub fn public_key(&self) -> &[u8] {
        self.public_key
            .get(..self.node.alg.public_key_len())
            .unwrap_or_default()
    }

    /// The handle the host signs with.
    pub const fn key(&self) -> KeyHandle {
        self.key
    }
}
