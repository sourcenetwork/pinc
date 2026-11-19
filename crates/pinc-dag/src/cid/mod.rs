//! Content identifiers: strictly parsed `CIDv1`, an owned heap-free form, hashing and multibase base32 text.
//!
//! A CID (version 1) is `varint(1) varint(codec) varint(hash) varint(len) digest`. Invariants: the version is 1, every varint is
//! minimal (so the byte form of a CID is unique), the digest is at most 64 bytes, and the digest of a known hash
//! code ([`SHA2_256`], [`BLAKE3`]) is exactly 32 bytes. [`CidRef`] borrows its bytes and [`Cid`] owns them inline;
//! neither allocates. The text form is multibase base32 lower (`b` prefix, RFC 4648 lowercase alphabet, no
//! padding), and [`cmp_text`] orders CIDs by that text without building it.

mod error;
mod hash;
mod owned;
mod text;

use core::cmp::Ordering;
use core::fmt;

use pinc_wire::Reader;
use pinc_wire::cbor::{Decoder, Item};

pub use error::CidError;
pub use owned::Cid;
pub use text::MAX_TEXT_LEN;

/// The multicodec of DAG-CBOR.
pub const DAG_CBOR: u64 = 0x71;
/// The multicodec of raw bytes.
pub const RAW: u64 = 0x55;
/// The multihash code of SHA2-256.
pub const SHA2_256: u64 = 0x12;
/// The multihash code of BLAKE3 with a 32-byte digest.
pub const BLAKE3: u64 = 0x1e;

/// The digest length of [`SHA2_256`] and [`BLAKE3`].
pub const DIGEST_LEN: usize = 32;
/// The longest digest a CID may carry.
pub const MAX_DIGEST_LEN: usize = 64;
/// The longest CID: version, codec and hash varints (1, 9, 9 bytes), the length byte and a 64-byte digest.
pub const MAX_LEN: usize = 1 + 9 + 9 + 1 + MAX_DIGEST_LEN;

/// A borrowed `CIDv1`, parsed and validated in place.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CidRef<'a> {
    raw: &'a [u8],
    codec: u64,
    hash: u64,
    digest_len: u8,
}

impl<'a> CidRef<'a> {
    /// Parse exactly one CID from all of `input`.
    ///
    /// # Errors
    /// Any [`CidRef::parse_prefix`] error, and [`CidError::TrailingBytes`] if bytes follow the CID.
    pub fn parse(input: &'a [u8]) -> Result<Self, CidError> {
        match Self::parse_prefix(input)? {
            (cid, []) => Ok(cid),
            _ => Err(CidError::TrailingBytes),
        }
    }

    /// Parse one CID from the start of `input` and return it with the bytes that follow it.
    ///
    /// # Errors
    /// [`CidError::CidV0`] for a bare SHA2-256 multihash, [`CidError::UnsupportedVersion`] for a version other than 1,
    /// [`CidError::DigestTooLong`] past 64 bytes, [`CidError::DigestLenMismatch`] for a known hash code with a digest
    /// that is not 32 bytes, and [`CidError::Wire`] for a truncated or non-minimal varint or a short digest.
    pub fn parse_prefix(input: &'a [u8]) -> Result<(Self, &'a [u8]), CidError> {
        if let [0x12, 0x20, ..] = input {
            return Err(CidError::CidV0);
        }
        let mut r = Reader::new(input);
        let version = r.read_varint()?;
        if version != 1 {
            return Err(CidError::UnsupportedVersion(version));
        }
        let codec = r.read_varint()?;
        let hash = r.read_varint()?;
        let len = r.read_varint()?;
        let digest_len = u8::try_from(len)
            .ok()
            .filter(|&l| usize::from(l) <= MAX_DIGEST_LEN)
            .ok_or(CidError::DigestTooLong(len))?;
        if matches!(hash, SHA2_256 | BLAKE3) && usize::from(digest_len) != DIGEST_LEN {
            return Err(CidError::DigestLenMismatch { hash, len });
        }
        r.read_bytes(usize::from(digest_len))?;
        let (raw, rest) = input.split_at_checked(r.position()).ok_or(CidError::TrailingBytes)?;
        Ok((
            Self {
                raw,
                codec,
                hash,
                digest_len,
            },
            rest,
        ))
    }

    /// Read a CID written as tag 42 over a byte string of `0x00` and the CID, as DAG-CBOR links are.
    ///
    /// # Errors
    /// [`CidError::Wire`] if the next item is not a CID link, plus any [`CidRef::parse`] error.
    pub fn read_cbor(dec: &mut Decoder<'a>) -> Result<Self, CidError> {
        if !matches!(dec.next_item()?, Item::Tag(_)) {
            return Err(pinc_wire::WireError::Unexpected("expected a CID link").into());
        }
        match dec.next_item()? {
            Item::Bytes([0, cid @ ..]) => Self::parse(cid),
            _ => Err(pinc_wire::WireError::Unexpected("expected a CID link").into()),
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
    pub fn digest(&self) -> &'a [u8] {
        let start = self.raw.len().saturating_sub(usize::from(self.digest_len));
        self.raw.get(start..).unwrap_or_default()
    }

    /// The whole binary CID.
    pub const fn as_bytes(&self) -> &'a [u8] {
        self.raw
    }

    /// Copy into an owned [`Cid`].
    pub fn into_owned(self) -> Cid {
        Cid::from_ref(self)
    }

    /// Check that `block` hashes to this CID's digest.
    ///
    /// # Errors
    /// [`CidError::UnsupportedHash`] if the hash code is not [`SHA2_256`] or [`BLAKE3`],
    /// [`CidError::DigestMismatch`] if the digest differs.
    pub fn verify(&self, block: &[u8]) -> Result<(), CidError> {
        if hash::digest(self.hash, block)?.as_slice() == self.digest() {
            Ok(())
        } else {
            Err(CidError::DigestMismatch)
        }
    }

    /// Write the multibase base32 text into `out` and return it.
    ///
    /// # Errors
    /// [`CidError::BufferTooSmall`] if `out` is shorter than the text; [`MAX_TEXT_LEN`] always suffices.
    pub fn encode_text<'o>(&self, out: &'o mut [u8]) -> Result<&'o str, CidError> {
        text::encode(self.raw, out)
    }
}

impl fmt::Display for CidRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = [0u8; MAX_TEXT_LEN];
        f.write_str(self.encode_text(&mut buf).map_err(|_| fmt::Error)?)
    }
}

impl fmt::Debug for CidRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CidRef({self})")
    }
}

/// Order two CIDs by their multibase base32 text, without building the text.
///
/// This is the order `DefraDB` sorts heads and links in. It differs from byte order: base32 digits `2` to `7` stand
/// for values 26 to 31 but sort before every letter in ASCII.
pub fn cmp_text(a: CidRef<'_>, b: CidRef<'_>) -> Ordering {
    text::chars(a.raw).cmp(text::chars(b.raw))
}

/// A validated array of CID links inside DAG-CBOR, iterated in place.
#[derive(Debug, Clone)]
pub struct CidList<'a> {
    dec: Decoder<'a>,
    left: u64,
}

impl<'a> CidList<'a> {
    /// A list of no CIDs.
    pub const fn empty() -> Self {
        Self {
            dec: Decoder::new(&[]),
            left: 0,
        }
    }

    /// Read an array of CID links from `dec`, validating every CID; `whole` must be the buffer `dec` reads.
    ///
    /// # Errors
    /// [`CidError::Wire`] if the next item is not an array or the input is malformed, plus any CID error.
    pub fn read(dec: &mut Decoder<'a>, whole: &'a [u8]) -> Result<Self, CidError> {
        let Item::Array(count) = dec.next_item()? else {
            return Err(pinc_wire::WireError::Unexpected("expected an array of CIDs").into());
        };
        let start = dec.position();
        for _ in 0..count {
            CidRef::read_cbor(dec)?;
        }
        let items = whole
            .get(start..dec.position())
            .ok_or(pinc_wire::WireError::Truncated { needed: 1 })?;
        Ok(Self {
            dec: Decoder::new(items),
            left: count,
        })
    }

    /// How many CIDs remain.
    pub const fn len(&self) -> u64 {
        self.left
    }

    /// Whether no CIDs remain.
    pub const fn is_empty(&self) -> bool {
        self.left == 0
    }
}

impl<'a> Iterator for CidList<'a> {
    type Item = CidRef<'a>;

    fn next(&mut self) -> Option<CidRef<'a>> {
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        // The items were validated by `read`, so a failure cannot happen; it ends the iteration if it ever did.
        let cid = CidRef::read_cbor(&mut self.dec).ok();
        if cid.is_none() {
            self.left = 0;
        }
        cid
    }
}
