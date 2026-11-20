//! The owned CID on an inline buffer.

use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};

use pinc_wire::Writer;

use super::{CidError, CidRef, MAX_DIGEST_LEN, MAX_LEN, hash, text};

/// An owned `CIDv1` held on a fixed buffer: no heap, `Copy`.
///
/// Equality, order and hashing are over the binary form; use [`Cid::cmp_text`] for `DefraDB`'s text order.
#[derive(Clone, Copy)]
pub struct Cid {
    buf: [u8; MAX_LEN],
    len: u8,
    codec: u64,
    hash: u64,
    digest_len: u8,
}

impl Cid {
    /// Build a CID from its parts.
    ///
    /// # Errors
    /// [`CidError::DigestTooLong`] past 64 bytes, [`CidError::DigestLenMismatch`] for a known hash code with a digest
    /// that is not 32 bytes, [`CidError::Wire`] for a codec or hash code of 2^63 or more.
    pub fn new(codec: u64, hash: u64, digest: &[u8]) -> Result<Self, CidError> {
        let too_long = CidError::DigestTooLong(digest.len() as u64);
        let digest_len = u8::try_from(digest.len())
            .ok()
            .filter(|&l| usize::from(l) <= MAX_DIGEST_LEN);
        let digest_len = digest_len.ok_or(too_long)?;
        let mut buf = [0u8; MAX_LEN];
        let mut w = Writer::new(&mut buf);
        w.put_varint(1)?;
        w.put_varint(codec)?;
        w.put_varint(hash)?;
        w.put_varint(u64::from(digest_len))?;
        w.put_slice(digest)?;
        let len = u8::try_from(w.written().len()).map_err(|_| too_long)?;
        // Re-parse so the invariants live in one place.
        CidRef::parse(buf.get(..usize::from(len)).unwrap_or_default()).map(CidRef::into_owned)
    }

    /// Parse exactly one CID from all of `bytes`.
    ///
    /// # Errors
    /// Any [`CidRef::parse`] error.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CidError> {
        CidRef::parse(bytes).map(CidRef::into_owned)
    }

    pub(super) fn from_ref(r: CidRef<'_>) -> Self {
        let mut buf = [0u8; MAX_LEN];
        let raw = r.as_bytes();
        if let Some(dst) = buf.get_mut(..raw.len()) {
            dst.copy_from_slice(raw);
        }
        Self {
            buf,
            len: u8::try_from(raw.len()).unwrap_or(u8::MAX),
            codec: r.codec(),
            hash: r.hash_code(),
            digest_len: u8::try_from(r.digest().len()).unwrap_or(u8::MAX),
        }
    }

    /// Hash `block` with the multihash `hash` and build the CID of it under `codec`.
    ///
    /// # Errors
    /// [`CidError::UnsupportedHash`] unless `hash` is [`super::SHA2_256`] or [`super::BLAKE3`]; [`CidError::Wire`] for a codec of
    /// 2^63 or more.
    pub fn for_block(codec: u64, hash: u64, block: &[u8]) -> Result<Self, CidError> {
        Self::new(codec, hash, &hash::digest(hash, block)?)
    }

    /// Parse the multibase base32 lower text form.
    ///
    /// # Errors
    /// [`CidError::BadText`] for a missing prefix, a character outside the alphabet, non-zero padding bits, a text
    /// whose length no CID has or a text longer than any CID, plus any [`CidRef::parse`] error on the decoded bytes.
    pub fn parse_text(s: &str) -> Result<Self, CidError> {
        let mut buf = [0u8; MAX_LEN];
        let n = text::decode(s, &mut buf)?;
        Self::from_bytes(buf.get(..n).unwrap_or_default())
    }

    /// The binary CID.
    pub fn as_bytes(&self) -> &[u8] {
        self.buf.get(..usize::from(self.len)).unwrap_or_default()
    }

    /// Borrow as a [`CidRef`].
    #[allow(clippy::should_implement_trait, reason = "it returns a value, not a reference")]
    pub fn as_ref(&self) -> CidRef<'_> {
        CidRef {
            raw: self.as_bytes(),
            codec: self.codec,
            hash: self.hash,
            digest_len: self.digest_len,
        }
    }

    /// The multicodec of the content.
    pub const fn codec(&self) -> u64 {
        self.codec
    }

    /// The multihash code.
    pub const fn hash_code(&self) -> u64 {
        self.hash
    }

    /// The digest bytes.
    pub fn digest(&self) -> &[u8] {
        self.as_ref().digest()
    }

    /// Check that `block` hashes to this CID's digest.
    ///
    /// # Errors
    /// See [`CidRef::verify`].
    pub fn verify(&self, block: &[u8]) -> Result<(), CidError> {
        self.as_ref().verify(block)
    }

    /// Write the multibase base32 text into `out` and return it.
    ///
    /// # Errors
    /// See [`CidRef::encode_text`].
    pub fn encode_text<'o>(&self, out: &'o mut [u8]) -> Result<&'o str, CidError> {
        self.as_ref().encode_text(out)
    }

    /// Order by text form; see [`super::cmp_text`].
    pub fn cmp_text(&self, other: &Self) -> Ordering {
        super::cmp_text(self.as_ref(), other.as_ref())
    }
}

impl PartialEq for Cid {
    fn eq(&self, other: &Self) -> bool {
        self.as_bytes() == other.as_bytes()
    }
}

impl Eq for Cid {}

impl PartialOrd for Cid {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Cid {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_bytes().cmp(other.as_bytes())
    }
}

impl Hash for Cid {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state);
    }
}

impl fmt::Display for Cid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.as_ref(), f)
    }
}

impl fmt::Debug for Cid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Cid({self})")
    }
}
