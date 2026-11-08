//! Canonical encoding of a block into a caller buffer.

use vinc_wire::WireError;
use vinc_wire::cbor::{Decoder, Encoder};

use super::BlockError;
use crate::cbor_len::{cid_len, head_len, text_len};
use crate::cid::Cid;

/// A named link to encode.
#[derive(Debug, Clone, Copy)]
pub struct Link<'n> {
    /// The link name, usually a field name.
    pub name: &'n str,
    /// The linked block.
    pub cid: Cid,
}

/// Everything a block holds, ready to encode.
///
/// [`encode_block`] sorts `heads` and `links` in place into `DefraDB`'s order, so the caller need not.
#[derive(Debug)]
pub struct BlockParts<'a, 'n> {
    /// One complete, canonical DAG-CBOR item: the CRDT delta, already encoded.
    pub delta: &'a [u8],
    /// The previous blocks; empty means the key is omitted.
    pub heads: &'a mut [Cid],
    /// The named links; empty means the key is omitted.
    pub links: &'a mut [Link<'n>],
    /// The encryption block, if any.
    pub encryption: Option<Cid>,
    /// The signature block, if any.
    pub signature: Option<Cid>,
}

impl BlockParts<'_, '_> {
    /// The exact encoded size, independent of the order of heads and links; the delta is not validated here.
    pub fn encoded_len(&self) -> usize {
        let cid = |c: &Cid| cid_len(c.as_bytes().len());
        let entries = entry_count(self);
        let mut n = head_len(entries) + text_len("delta".len()) + self.delta.len();
        if !self.heads.is_empty() {
            let items: usize = self.heads.iter().map(cid).sum();
            n += text_len("heads".len()) + head_len(self.heads.len() as u64) + items;
        }
        if !self.links.is_empty() {
            // A link is a two-entry map: `link` then `name`.
            let items: usize = self
                .links
                .iter()
                .map(|l| 1 + text_len("link".len()) + cid(&l.cid) + text_len("name".len()) + text_len(l.name.len()))
                .sum();
            n += text_len("links".len()) + head_len(self.links.len() as u64) + items;
        }
        n += self
            .signature
            .iter()
            .map(|c| text_len("signature".len()) + cid(c))
            .sum::<usize>();
        n += self
            .encryption
            .iter()
            .map(|c| text_len("encryption".len()) + cid(c))
            .sum::<usize>();
        n
    }
}

/// Encode a block into `out` and return the number of bytes written.
///
/// Sorts `parts.heads` by CID text and `parts.links` by CID text then name, as `DefraDB` does. The result parses with
/// [`super::BlockRef::parse`] and re-encodes identically.
///
/// # Errors
/// [`BlockError::Wire`] if the delta is not exactly one canonical item or `out` is too small (nothing is written
/// then); [`BlockError::Unordered`] if two heads, or two links, are identical.
pub fn encode_block(out: &mut [u8], parts: &mut BlockParts<'_, '_>) -> Result<usize, BlockError> {
    let mut dec = Decoder::new(parts.delta);
    dec.skip_value()?;
    if !dec.is_empty() {
        return Err(WireError::Unexpected("delta is more than one item").into());
    }
    parts.heads.sort_unstable_by(Cid::cmp_text);
    parts
        .links
        .sort_unstable_by(|a, b| a.cid.cmp_text(&b.cid).then_with(|| a.name.cmp(b.name)));
    if parts.heads.windows(2).any(|w| matches!(w, [a, b] if a == b)) {
        return Err(BlockError::Unordered("heads"));
    }
    if parts
        .links
        .windows(2)
        .any(|w| matches!(w, [a, b] if a.cid == b.cid && a.name == b.name))
    {
        return Err(BlockError::Unordered("links"));
    }
    let len = parts.encoded_len();
    if len > out.len() {
        return Err(WireError::BufferTooSmall {
            needed: len - out.len(),
        }
        .into());
    }
    // The delta is spliced in as raw bytes, so the encoder is split around it; the key tracker carries over.
    let (prefix, mut keys) = {
        let mut enc = Encoder::new(out);
        let mut keys = enc.ordered_map(entry_count(parts))?;
        keys.key(&mut enc, "delta")?;
        (enc.written().len(), keys)
    };
    let short = WireError::BufferTooSmall { needed: len };
    let (dst, tail) = out
        .get_mut(prefix..)
        .and_then(|t| t.split_at_mut_checked(parts.delta.len()))
        .ok_or(short)?;
    dst.copy_from_slice(parts.delta);
    let mut enc = Encoder::new(tail);
    if !parts.heads.is_empty() {
        keys.key(&mut enc, "heads")?;
        enc.array(parts.heads.len() as u64)?;
        for h in parts.heads.iter() {
            enc.tag_cid(h.as_bytes())?;
        }
    }
    if !parts.links.is_empty() {
        keys.key(&mut enc, "links")?;
        enc.array(parts.links.len() as u64)?;
        for l in parts.links.iter() {
            let mut link = enc.ordered_map(2)?;
            link.key(&mut enc, "link")?;
            enc.tag_cid(l.cid.as_bytes())?;
            link.key(&mut enc, "name")?;
            enc.text(l.name)?;
        }
    }
    if let Some(sig) = &parts.signature {
        keys.key(&mut enc, "signature")?;
        enc.tag_cid(sig.as_bytes())?;
    }
    if let Some(e) = &parts.encryption {
        keys.key(&mut enc, "encryption")?;
        enc.tag_cid(e.as_bytes())?;
    }
    Ok(prefix + parts.delta.len() + enc.written().len())
}

fn entry_count(parts: &BlockParts<'_, '_>) -> u64 {
    1 + u64::from(!parts.heads.is_empty())
        + u64::from(!parts.links.is_empty())
        + u64::from(parts.signature.is_some())
        + u64::from(parts.encryption.is_some())
}
