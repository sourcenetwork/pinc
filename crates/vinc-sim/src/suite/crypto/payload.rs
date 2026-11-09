//! Self-identifying payload bytes.
//!
//! A message or value body is a sequence of 64-byte blocks generated from `(registry seed, message id)`. Every block
//! starts with an 8-byte magic, the message id (u64) and the block index (u32), all little-endian; the remaining
//! 44 bytes are a cheap pseudo-random function of the same inputs. A block can therefore be recognised at any offset
//! of any byte string, and a candidate is accepted only if the whole visible part matches what the generator would
//! write (its first 32 bytes, so a block cut short and followed by other data still counts), so a ciphertext collides with a block with probability about 2^-64 per position (the magic alone).
//!
//! Limits, stated where the verdicts read them: a block is found only when at least its 20-byte header is visible, so
//! a range edge can hide up to 63 bytes of payload at each end; a message shorter than 20 bytes holds no
//! recognisable block.

use super::registry::Registry;

/// The length of a block.
pub const BLOCK_LEN: usize = 64;
/// The length of the block header: magic, message id, block index.
pub const HEADER_LEN: usize = 20;
/// How many bytes of a candidate block are compared with the generator (the header and 12 pseudo-random bytes).
const CHECKED: usize = 32;
/// The first eight bytes of every block.
pub const MAGIC: [u8; 8] = [0xB5, b'V', b'N', b'C', b'b', b'l', b'k', 0x01];
const GOLDEN: u64 = 0x9E37_79B9_7F4A_7C15;

/// The identity of a generated message or value; ids start at 1.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MsgId(pub u64);

/// What a body stands for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PayloadKind {
    /// A stored value (fetched by root).
    Value,
    /// An application message; a datagram that carries another node's message is third-party bytes.
    Msg,
}

/// Why payload bytes could not be produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PayloadError {
    /// The id was never issued by this registry.
    UnknownMsg,
    /// The range reaches past the end of the message.
    OutOfRange,
}

impl core::fmt::Display for PayloadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::UnknownMsg => "no such message",
            Self::OutOfRange => "range is past the end of the message",
        })
    }
}

impl core::error::Error for PayloadError {}

/// What the registry knows of one message.
#[derive(Debug, Clone, Copy)]
pub(super) struct MsgMeta {
    pub(super) creator: usize,
    pub(super) kind: PayloadKind,
    pub(super) len: u64,
}

pub(super) fn mix(mut z: u64) -> u64 {
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// The block `idx` of message `msg` under `seed`.
pub(super) fn block(seed: u64, msg: u64, idx: u32) -> [u8; BLOCK_LEN] {
    let mut out = [0u8; BLOCK_LEN];
    out[..8].copy_from_slice(&MAGIC);
    out[8..16].copy_from_slice(&msg.to_le_bytes());
    out[16..HEADER_LEN].copy_from_slice(&idx.to_le_bytes());
    let mut s = mix(seed ^ mix(msg)) ^ u64::from(idx).wrapping_mul(GOLDEN);
    for chunk in out[HEADER_LEN..].chunks_mut(8) {
        s = s.wrapping_add(GOLDEN);
        let w = mix(s).to_le_bytes();
        let n = chunk.len();
        chunk.copy_from_slice(&w[..n]);
    }
    out
}

/// The positions in `bytes` where the magic and a complete header start.
fn candidates(bytes: &[u8]) -> impl Iterator<Item = (usize, u64, u32)> + '_ {
    let last = bytes.len().saturating_sub(HEADER_LEN - 1);
    (0..last).filter_map(move |i| {
        if bytes[i] != MAGIC[0] || bytes[i..i + 8] != MAGIC {
            return None;
        }
        let id = u64::from_le_bytes(bytes[i + 8..i + 16].try_into().ok()?);
        let idx = u32::from_le_bytes(bytes[i + 16..i + HEADER_LEN].try_into().ok()?);
        Some((i, id, idx))
    })
}

impl Registry {
    /// A new message or value of `len` bytes created by node `creator`.
    pub fn new_msg(&self, creator: usize, kind: PayloadKind, len: u64) -> MsgId {
        let mut st = self.st.borrow_mut();
        st.msgs.push(MsgMeta { creator, kind, len });
        MsgId(st.msgs.len() as u64)
    }

    /// Write bytes `offset..offset + out.len()` of the body of `msg` into `out`.
    ///
    /// # Errors
    /// [`PayloadError::UnknownMsg`] for an id this registry never issued, [`PayloadError::OutOfRange`] if the range
    /// reaches past the message.
    pub fn fill(&self, msg: MsgId, offset: u64, out: &mut [u8]) -> Result<(), PayloadError> {
        let meta = self.msg_meta(msg).ok_or(PayloadError::UnknownMsg)?;
        let end = offset.checked_add(out.len() as u64).ok_or(PayloadError::OutOfRange)?;
        if end > meta.len {
            return Err(PayloadError::OutOfRange);
        }
        let mut pos = offset;
        let mut done = 0usize;
        while done < out.len() {
            let idx = pos / BLOCK_LEN as u64;
            let within = (pos % BLOCK_LEN as u64) as usize;
            let b = block(self.seed, msg.0, idx as u32);
            let n = (BLOCK_LEN - within).min(out.len() - done);
            out[done..done + n].copy_from_slice(&b[within..within + n]);
            done += n;
            pos += n as u64;
        }
        Ok(())
    }

    /// The node that created `msg`.
    pub fn creator_of(&self, msg: MsgId) -> Option<usize> {
        self.msg_meta(msg).map(|m| m.creator)
    }

    /// Whether `msg` is a value or an application message.
    pub fn kind_of(&self, msg: MsgId) -> Option<PayloadKind> {
        self.msg_meta(msg).map(|m| m.kind)
    }

    pub(super) fn msg_meta(&self, msg: MsgId) -> Option<MsgMeta> {
        let idx = usize::try_from(msg.0.checked_sub(1)?).ok()?;
        self.st.borrow().msgs.get(idx).copied()
    }

    /// Every block of a registered message visible in `bytes`, at any offset, as `(message, block index)`.
    ///
    /// A candidate counts only when the visible part of the block equals what [`Registry::fill`] writes, so
    /// ciphertext and foreign data are not mistaken for payload (see the module docs for the edge limit).
    pub fn find_blocks<'a>(&'a self, bytes: &'a [u8]) -> impl Iterator<Item = (MsgId, u32)> + 'a {
        candidates(bytes).filter_map(move |(at, id, idx)| {
            let meta = self.msg_meta(MsgId(id))?;
            let start = u64::from(idx) * BLOCK_LEN as u64;
            if start >= meta.len {
                return None;
            }
            let valid = (meta.len - start).min(BLOCK_LEN as u64) as usize;
            let visible = valid.min(bytes.len() - at);
            if visible < HEADER_LEN {
                return None;
            }
            // The bytes after a cut block belong to something else, so only the first `CHECKED` are compared.
            let checked = visible.min(CHECKED);
            let expect = block(self.seed, id, idx);
            (bytes[at..at + checked] == expect[..checked]).then_some((MsgId(id), idx))
        })
    }

    /// Whether `bytes` holds at least one block of a registered message.
    pub fn has_blocks(&self, bytes: &[u8]) -> bool {
        self.find_blocks(bytes).next().is_some()
    }
}
