//! WebSocket framing (RFC 6455 section 5), client and server, for carrying the protected carrier over a WebSocket.
//!
//! Only the framing is here: the HTTP upgrade belongs to the host. The carrier is a byte stream, so message
//! boundaries carry no meaning and this codec delivers the payload of binary and continuation frames as one stream.
//!
//! Invariants:
//! - A client frame is masked and a server frame is not; the reverse is refused ([`WsError::Mask`]).
//! - Reserved bits, text frames, unknown opcodes, a continuation without a message in progress, a fragmented control
//!   frame and a control payload over 125 bytes are refused.
//! - A payload over [`MAX_PAYLOAD`] is refused before any byte of it is buffered, and the length uses the shortest
//!   form that holds it (a longer form is refused, as RFC 6455 requires).
//! - Decoding unmasks in place and never copies; encoding writes into a caller buffer; nothing allocates.

use core::fmt;

use vinc_wire::Writer;

/// The largest payload one frame may carry: a protected unit and its length prefix.
pub const MAX_PAYLOAD: usize = super::session::MAX_UNIT_LEN + 2;
/// The longest frame header: 2 bytes, an 8-byte length and a 4-byte mask.
pub const MAX_HEADER: usize = 14;

/// Which end of the connection a codec serves; a client masks, a server does not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    /// The dialing end: sends masked frames, expects unmasked ones.
    Client,
    /// The accepting end: sends unmasked frames, expects masked ones.
    Server,
}

/// A frame opcode this codec uses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Opcode {
    /// Continuation of a fragmented message.
    Continuation = 0x0,
    /// Binary data.
    Binary = 0x2,
    /// Close.
    Close = 0x8,
    /// Ping.
    Ping = 0x9,
    /// Pong.
    Pong = 0xA,
}

/// Why a frame was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WsError {
    /// A reserved bit is set.
    Reserved,
    /// An opcode that is not binary, continuation, close, ping or pong (text included).
    Opcode(u8),
    /// A masked frame from a server, or an unmasked one from a client.
    Mask,
    /// A control frame that is fragmented or longer than 125 bytes.
    Control,
    /// A continuation with no message in progress, or a data frame inside one.
    Sequence,
    /// A payload longer than [`MAX_PAYLOAD`].
    TooLong,
    /// A length not in its shortest form.
    LengthForm,
    /// The output buffer is too small.
    NoRoom,
}

impl fmt::Display for WsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reserved => f.write_str("reserved bit set"),
            Self::Opcode(o) => write!(f, "unsupported opcode {o}"),
            Self::Mask => f.write_str("mask bit does not match the sender's role"),
            Self::Control => f.write_str("malformed control frame"),
            Self::Sequence => f.write_str("frame out of sequence"),
            Self::TooLong => f.write_str("payload too long"),
            Self::LengthForm => f.write_str("length is not in its shortest form"),
            Self::NoRoom => f.write_str("output buffer too small"),
        }
    }
}

impl core::error::Error for WsError {}

/// A decoded frame.
#[derive(Debug, PartialEq, Eq)]
pub enum WsFrame<'a> {
    /// Stream bytes: the payload of a binary or continuation frame.
    Data(&'a [u8]),
    /// A ping: answer with [`encode`] of a pong carrying the same payload.
    Ping(&'a [u8]),
    /// A pong; nothing to do.
    Pong(&'a [u8]),
    /// A close, with the status code when the payload has one.
    Close(Option<u16>),
}

/// XOR `data` with the 4-byte mask key (applying it twice restores the data).
pub fn apply_mask(key: [u8; 4], data: &mut [u8]) {
    for (b, k) in data.iter_mut().zip(key.iter().cycle()) {
        *b ^= k;
    }
}

/// Write a frame (FIN set, no fragmentation) with `payload` into `out`; returns the length. A client passes a
/// `mask` key of fresh random bytes, a server passes `None`.
///
/// # Errors
/// [`WsError::NoRoom`], [`WsError::TooLong`] or [`WsError::Control`] for a control payload over 125 bytes.
pub fn encode(opcode: Opcode, payload: &[u8], mask: Option<[u8; 4]>, out: &mut [u8]) -> Result<usize, WsError> {
    if payload.len() > MAX_PAYLOAD {
        return Err(WsError::TooLong);
    }
    let control = (opcode as u8) & 0x8 != 0;
    if control && payload.len() > 125 {
        return Err(WsError::Control);
    }
    let no_room = |_| WsError::NoRoom;
    let mut w = Writer::new(out);
    w.put_u8(0x80 | opcode as u8).map_err(no_room)?;
    let mask_bit = if mask.is_some() { 0x80 } else { 0 };
    match payload.len() {
        n @ 0..=125 => w.put_u8(mask_bit | u8::try_from(n).unwrap_or(0)),
        n => {
            w.put_u8(mask_bit | 0x7e).map_err(no_room)?;
            w.put_u16(u16::try_from(n).map_err(|_| WsError::TooLong)?)
        }
    }
    .map_err(no_room)?;
    if let Some(key) = mask {
        w.put_slice(&key).map_err(no_room)?;
    }
    let start = w.written().len();
    w.put_slice(payload).map_err(no_room)?;
    let end = w.written().len();
    if let Some(key) = mask {
        apply_mask(key, out.get_mut(start..end).ok_or(WsError::NoRoom)?);
    }
    Ok(end)
}

/// The frame decoder of one end.
#[derive(Debug, Clone, Copy)]
pub struct Decoder {
    peer: Role,
    in_message: bool,
}

impl Decoder {
    /// A decoder for the frames a peer of role `peer` sends (a server decodes `Role::Client` frames).
    pub const fn new(peer: Role) -> Self {
        Self {
            peer,
            in_message: false,
        }
    }

    /// Decode the first frame in `buf`, unmasking it in place. Returns the frame and the bytes it used, or `None` if
    /// `buf` does not hold a whole frame yet. After an error the connection is closed.
    ///
    /// # Errors
    /// A [`WsError`] naming the violation.
    pub fn decode<'a>(&mut self, buf: &'a mut [u8]) -> Result<Option<(WsFrame<'a>, usize)>, WsError> {
        let (b0, b1) = match buf {
            [a, b, ..] => (*a, *b),
            _ => return Ok(None),
        };
        if b0 & 0x70 != 0 {
            return Err(WsError::Reserved);
        }
        let fin = b0 & 0x80 != 0;
        let opcode = match b0 & 0x0f {
            0x0 => Opcode::Continuation,
            0x2 => Opcode::Binary,
            0x8 => Opcode::Close,
            0x9 => Opcode::Ping,
            0xA => Opcode::Pong,
            o => return Err(WsError::Opcode(o)),
        };
        let masked = b1 & 0x80 != 0;
        if masked != (self.peer == Role::Client) {
            return Err(WsError::Mask);
        }
        let control = (opcode as u8) & 0x8 != 0;
        let (len, head) = match b1 & 0x7f {
            126 => match buf.get(2..4) {
                Some(&[a, b]) => {
                    let n = usize::from(u16::from_be_bytes([a, b]));
                    if n < 126 {
                        return Err(WsError::LengthForm);
                    }
                    (n, 4)
                }
                _ => return Ok(None),
            },
            127 => match buf.get(2..10).and_then(|s| <[u8; 8]>::try_from(s).ok()) {
                Some(raw) => {
                    let n = u64::from_be_bytes(raw);
                    if n < 65_536 {
                        return Err(WsError::LengthForm);
                    }
                    (usize::try_from(n).map_err(|_| WsError::TooLong)?, 10)
                }
                None => return Ok(None),
            },
            n => (usize::from(n), 2),
        };
        if len > MAX_PAYLOAD {
            return Err(WsError::TooLong);
        }
        if control && (!fin || len > 125) {
            return Err(WsError::Control);
        }
        if !control && (opcode == Opcode::Continuation) != self.in_message {
            return Err(WsError::Sequence);
        }
        let key = if masked {
            match buf.get(head..head + 4).and_then(|s| <[u8; 4]>::try_from(s).ok()) {
                Some(k) => Some(k),
                None => return Ok(None),
            }
        } else {
            None
        };
        let start = head + if masked { 4 } else { 0 };
        let end = start + len;
        let Some(payload) = buf.get_mut(start..end) else {
            return Ok(None);
        };
        if let Some(k) = key {
            apply_mask(k, payload);
        }
        if !control {
            self.in_message = !fin;
        }
        let payload: &'a [u8] = payload;
        let frame = match opcode {
            Opcode::Continuation | Opcode::Binary => WsFrame::Data(payload),
            Opcode::Ping => WsFrame::Ping(payload),
            Opcode::Pong => WsFrame::Pong(payload),
            Opcode::Close => WsFrame::Close(payload.first_chunk::<2>().map(|c| u16::from_be_bytes(*c))),
        };
        Ok(Some((frame, end)))
    }
}
