//! Stream framing of the harness protocols: a 13-byte header `[type:1][len:4][id:8]` (big-endian) followed by `len`
//! body bytes.
//!
//! [`Framer`] reassembles frames from a stream read in arbitrary pieces. Invariants: it holds at most one header and
//! one body under construction; the body grows only with bytes that actually arrived and is refused above
//! [`MAX_BODY`], so a forged length cannot make it allocate; after an error it must be dropped with its stream.

use core::fmt;

/// The length of a frame header.
pub const HDR: usize = 13;
/// A push: the id is its sequence number.
pub const T_PUSH: u8 = 1;
/// A cumulative acknowledgement: the id is the highest sequence number held.
pub const T_ACK: u8 = 2;
/// A request: the id is `(intent id << 24) | response size`.
pub const T_REQ: u8 = 3;
/// A response: the id is the intent id.
pub const T_RESP: u8 = 4;
/// An echo: the id is the intent id.
pub const T_ECHO: u8 = 5;
/// The largest body a frame may announce (the response size field is 24 bits wide).
pub const MAX_BODY: usize = 1 << 24;

/// The header of a frame.
pub fn hdr(ty: u8, len: usize, id: u64) -> [u8; HDR] {
    let mut h = [0u8; HDR];
    h[0] = ty;
    h[1..5].copy_from_slice(&u32::try_from(len).unwrap_or(u32::MAX).to_be_bytes());
    h[5..].copy_from_slice(&id.to_be_bytes());
    h
}

/// One complete frame.
#[derive(Debug, PartialEq, Eq)]
pub struct Frame {
    /// The type.
    pub ty: u8,
    /// The id.
    pub id: u64,
    /// The body, `None` for an empty one.
    pub body: Option<Vec<u8>>,
}

/// Why a stream cannot be framed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameError {
    /// The type byte is not one of the five.
    UnknownType,
    /// The announced body exceeds [`MAX_BODY`].
    TooLarge,
    /// An acknowledgement announced a body.
    AckBody,
}

impl fmt::Display for FrameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::UnknownType => "unknown frame type (stream corrupted or reordered)",
            Self::TooLarge => "frame body is too large (stream corrupted or reordered)",
            Self::AckBody => "acknowledgement with a body (stream corrupted or reordered)",
        })
    }
}

impl core::error::Error for FrameError {}

/// Reassembles frames from the pieces of one stream.
#[derive(Debug, Default)]
pub struct Framer {
    head: [u8; HDR],
    have: usize,
    cur: Option<(u8, usize, u64)>,
    body: Vec<u8>,
}

impl Framer {
    /// A framer at the start of a stream.
    pub fn new() -> Self {
        Self::default()
    }

    /// Consumes `data`, appending every frame it completes to `out`.
    ///
    /// # Errors
    /// A [`FrameError`] when the header is not valid; frames completed before it are already in `out`.
    pub fn feed(&mut self, mut data: &[u8], out: &mut Vec<Frame>) -> Result<(), FrameError> {
        loop {
            let Some((ty, len, id)) = self.cur else {
                let take = (HDR - self.have).min(data.len());
                self.head[self.have..self.have + take].copy_from_slice(&data[..take]);
                self.have += take;
                data = &data[take..];
                if self.have < HDR {
                    return Ok(());
                }
                self.have = 0;
                let ty = self.head[0];
                let len = u32::from_be_bytes([self.head[1], self.head[2], self.head[3], self.head[4]]) as usize;
                let mut idb = [0u8; 8];
                idb.copy_from_slice(&self.head[5..]);
                let id = u64::from_be_bytes(idb);
                if !(T_PUSH..=T_ECHO).contains(&ty) {
                    return Err(FrameError::UnknownType);
                }
                if len > MAX_BODY {
                    return Err(FrameError::TooLarge);
                }
                if ty == T_ACK && len != 0 {
                    return Err(FrameError::AckBody);
                }
                if len == 0 {
                    out.push(Frame { ty, id, body: None });
                } else {
                    self.cur = Some((ty, len, id));
                    self.body.clear();
                }
                continue;
            };
            let take = (len - self.body.len()).min(data.len());
            self.body.extend_from_slice(&data[..take]);
            data = &data[take..];
            if self.body.len() < len {
                return Ok(());
            }
            out.push(Frame {
                ty,
                id,
                body: Some(core::mem::take(&mut self.body)),
            });
            self.cur = None;
        }
    }
}
