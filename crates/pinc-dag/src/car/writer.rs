//! Writing a CAR into a caller buffer.

use pinc_wire::cbor::Encoder;
use pinc_wire::{WireError, varint};

use super::CarError;
use crate::cbor_len::{cid_len, head_len, text_len};
use crate::cid::{Cid, CidRef};

/// Writes a CAR v1 into a caller buffer: the header at construction, then sections.
///
/// A write that does not fit fails with [`WireError::BufferTooSmall`] and leaves the written bytes unchanged.
#[derive(Debug)]
pub struct CarWriter<'a> {
    buf: &'a mut [u8],
    pos: usize,
}

impl<'a> CarWriter<'a> {
    /// The size of the header (length prefix included) for these roots.
    pub fn header_len(roots: &[Cid]) -> usize {
        let body = Self::header_body_len(roots);
        varint::encoded_len(body as u64) + body
    }

    /// The size of a section (length prefix included) for this CID and block.
    pub fn section_len(cid: CidRef<'_>, block: &[u8]) -> usize {
        let body = cid.as_bytes().len() + block.len();
        varint::encoded_len(body as u64) + body
    }

    fn header_body_len(roots: &[Cid]) -> usize {
        let roots_len: usize = roots.iter().map(|r| cid_len(r.as_bytes().len())).sum();
        // The map header, `roots` and its array, `version` and the value 1.
        1 + text_len("roots".len()) + head_len(roots.len() as u64) + roots_len + text_len("version".len()) + 1
    }

    /// Start a CAR in `buf` by writing the header for `roots`.
    ///
    /// # Errors
    /// [`CarError::Wire`] with [`WireError::BufferTooSmall`] if the header does not fit.
    pub fn new(buf: &'a mut [u8], roots: &[Cid]) -> Result<Self, CarError> {
        let body = Self::header_body_len(roots);
        let total = varint::encoded_len(body as u64) + body;
        if total > buf.len() {
            return Err(WireError::BufferTooSmall {
                needed: total - buf.len(),
            }
            .into());
        }
        let prefix = varint::encode(body as u64, buf)?;
        let mut enc = Encoder::new(buf.get_mut(prefix..).unwrap_or_default());
        let mut keys = enc.ordered_map(2)?;
        keys.key(&mut enc, "roots")?;
        enc.array(roots.len() as u64)?;
        for r in roots {
            enc.tag_cid(r.as_bytes())?;
        }
        keys.key(&mut enc, "version")?;
        enc.unsigned(1)?;
        if enc.written().len() != body {
            return Err(CarError::BadHeader("header length disagrees with its encoding"));
        }
        Ok(Self { buf, pos: total })
    }

    /// Append a section. The block is not checked against the CID; use [`CidRef::verify`] for that.
    ///
    /// # Errors
    /// [`CarError::Wire`] with [`WireError::BufferTooSmall`] if the section does not fit.
    pub fn section(&mut self, cid: CidRef<'_>, block: &[u8]) -> Result<(), CarError> {
        let total = Self::section_len(cid, block);
        let rest = self.buf.get_mut(self.pos..).unwrap_or_default();
        if total > rest.len() {
            return Err(WireError::BufferTooSmall {
                needed: total - rest.len(),
            }
            .into());
        }
        let prefix = varint::encode((cid.as_bytes().len() + block.len()) as u64, rest)?;
        let (_, body) = rest
            .split_at_mut_checked(prefix)
            .ok_or(WireError::Truncated { needed: prefix })?;
        let (cid_dst, block_dst) = body
            .split_at_mut_checked(cid.as_bytes().len())
            .ok_or(WireError::Truncated { needed: 1 })?;
        cid_dst.copy_from_slice(cid.as_bytes());
        block_dst
            .get_mut(..block.len())
            .ok_or(WireError::Truncated { needed: block.len() })?
            .copy_from_slice(block);
        self.pos += total;
        Ok(())
    }

    /// The CAR written so far.
    pub fn written(&self) -> &[u8] {
        self.buf.get(..self.pos).unwrap_or_default()
    }
}
