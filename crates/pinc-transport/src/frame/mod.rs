//! Frames: the typed units inside a sealed packet, parsed in place and encoded into a [`Writer`](`pinc_wire`::Writer).
//!
//! # Wire format
//!
//! A frame is a type, written as a `pinc-wire` varint (one byte below 128), then its fields. All fields written
//! "varint" below are `pinc-wire` varints; `bytes` are raw. Frames follow one another with no separator.
//!
//! | Type | Frame | Fields |
//! |---|---|---|
//! | `0x00` | PADDING | none; a run of zero bytes is one [`Frame::Padding`] |
//! | `0x01` | PING | none |
//! | `0x02` | ACK | largest, `range_count`, `first_range`, (gap, length)* |
//! | `0x04` | `RESET_STREAM` | stream id, error code, final size |
//! | `0x05` | `STOP_SENDING` | stream id, error code |
//! | `0x08`-`0x0f` | STREAM | stream id, offset (optional), length (optional), data |
//! | `0x11` | `MAX_STREAM_DATA` | stream id, max |
//! | `0x12` | `MAX_STREAMS` | limit: the streams the receiver admits in all, of every kind |
//! | `0x1a`, `0x1b` | `PATH_CHALLENGE`, `PATH_RESPONSE` | 8 bytes |
//! | `0x1c` | CLOSE | error code (see [`code`](crate::conn::code)) |
//! | `0x30`, `0x31` | DATAGRAM | without length (data to the end of the packet), with length (varint, then data) |
//! | `0x3a` | `MTU_PROBE_ECHO` | mtu (2 bytes, big-endian) |
//! | `0x3b`, `0x3c` | SLEEP, WAKE | none |
//! | `0x3d` | REKEY | kind (1 byte: 0 request, 1 answer), share (32 bytes), and for an answer the switch packet number (varint) |
//! | `0x3e` | READY | none |
//! | `0x3f` | `NEW_TICKETS` | a ticket batch: count (1 byte, 0 to 4), then per ticket the id (16 bytes) and the lifetime in seconds (4 bytes) |
//! | `0x40` and up | extension | length (varint), body bytes |
//!
//! There is no connection-level credit frame, no blocked frame, no frame to stop a connection, and no frame for
//! connection ids: the receiver grants credit per stream with `MAX_STREAM_DATA` and says how many streams it admits with
//! `MAX_STREAMS`, so an opener never sends a stream the receiver has no room for; a stream that arrives anyway and
//! does not fit is left unacknowledged so its opener retransmits it, and a connection id is derived from the session secret. An ACK carries no delay.
//!
//! STREAM type bits: `0x04` OFF (an offset follows the stream id; absent means 0), `0x02` LEN (a length follows;
//! absent means the data runs to the end of the packet, so the frame must be the last), `0x01` FIN. The stream end
//! (offset plus data length) is at most 2^62 - 1.
//!
//! ACK: `largest` is the highest packet number acknowledged and `first_range` the count of packets below it that
//! are also acknowledged, so the first range is `largest - first_range ..= largest`. Each following pair describes
//! the next lower range: `gap` is the count of unacknowledged packets between the ranges minus one, so the next range
//! ends at `previous_start - gap - 2`, and `length` is the count of further packets below its end, so it starts at
//! `end - length`. There are `range_count + 1` ranges, at most [`MAX_ACK_RANGES`]. This encoding cannot express two
//! ranges that touch or overlap, and no range may go below packet number 0: such an ACK is malformed.
//!
//! Extension frames (type `0x40` and up; the assigned types are named in [`ext`]) are never parsed here. To find where one ends, every extension frame
//! carries a varint length after its type; the body is passed through as [`Frame::Extension`]. Any other type
//! not in the table is an error.
//!
//! # Invariants
//!
//! Decoding borrows stream, datagram and extension bytes from the packet payload and never copies
//! them. Every length is checked before use; a [`FrameIter`] ends at the first error and consumes at least one byte
//! per frame. Encoding checks the frame and the room up front, so a failed write leaves the writer unchanged, and
//! [`Frame::encoded_len`] is exactly what [`Frame::write`] writes. Nothing here allocates or panics.

mod ack;
mod decode;
mod encode;
pub mod ext;

use core::fmt;

use pinc_wire::WireError;

pub use ack::{Ack, AckRanges, MAX_ACK_RANGES, ack_len, write_ack};
pub use decode::FrameIter;
pub use encode::{datagram_overhead, stream_overhead};

use pinc_security::{Rekey, TicketBatch};

/// The first extension frame type; below it every type is assigned or an error.
pub const EXTENSION_BASE: u64 = 0x40;
/// The largest stream end (offset plus length): 2^62 - 1.
pub const MAX_STREAM_END: u64 = (1 << 62) - 1;

/// Frame type values.
pub mod ty {
    /// PADDING.
    pub const PADDING: u64 = 0x00;
    /// PING.
    pub const PING: u64 = 0x01;
    /// ACK.
    pub const ACK: u64 = 0x02;
    /// `RESET_STREAM`.
    pub const RESET_STREAM: u64 = 0x04;
    /// `STOP_SENDING`.
    pub const STOP_SENDING: u64 = 0x05;
    /// STREAM with no flag bits; OR in [`STREAM_OFF`], [`STREAM_LEN`] and [`STREAM_FIN`].
    pub const STREAM: u64 = 0x08;
    /// STREAM flag: an offset is present.
    pub const STREAM_OFF: u64 = 0x04;
    /// STREAM flag: a length is present.
    pub const STREAM_LEN: u64 = 0x02;
    /// STREAM flag: this is the end of the stream.
    pub const STREAM_FIN: u64 = 0x01;
    /// The last STREAM type value.
    pub const STREAM_LAST: u64 = 0x0f;
    /// `MAX_STREAM_DATA`.
    pub const MAX_STREAM_DATA: u64 = 0x11;
    /// `MAX_STREAMS`.
    pub const MAX_STREAMS: u64 = 0x12;
    /// `PATH_CHALLENGE`.
    pub const PATH_CHALLENGE: u64 = 0x1a;
    /// `PATH_RESPONSE`.
    pub const PATH_RESPONSE: u64 = 0x1b;
    /// CLOSE.
    pub const CLOSE: u64 = 0x1c;
    /// DATAGRAM without a length.
    pub const DATAGRAM: u64 = 0x30;
    /// DATAGRAM with a length.
    pub const DATAGRAM_LEN: u64 = 0x31;
    /// `MTU_PROBE_ECHO`.
    pub const MTU_PROBE_ECHO: u64 = 0x3a;
    /// SLEEP.
    pub const SLEEP: u64 = 0x3b;
    /// WAKE.
    pub const WAKE: u64 = 0x3c;
    /// REKEY.
    pub const REKEY: u64 = 0x3d;
    /// READY.
    pub const READY: u64 = 0x3e;
    /// `NEW_TICKETS`.
    pub const NEW_TICKETS: u64 = 0x3f;
}

/// Why a frame was refused to decode or encode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameError {
    /// A varint, length or buffer bound of the wire layer was violated.
    Wire(WireError),
    /// A type below `0x40` that is not assigned.
    UnknownType(u64),
    /// An ACK is not canonical: a range below packet number 0, an empty, touching or overlapping range, or no range.
    Ack,
    /// An ACK has more than [`MAX_ACK_RANGES`] ranges.
    TooManyRanges,
    /// A STREAM frame ends beyond 2^62 - 1.
    StreamEnd,
    /// A REKEY frame whose kind byte is neither 0 nor 1.
    RekeyKind,
}

impl From<WireError> for FrameError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl fmt::Display for FrameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(e) => write!(f, "{e}"),
            Self::UnknownType(t) => write!(f, "unknown frame type {t:#x}"),
            Self::Ack => f.write_str("ack ranges are malformed"),
            Self::TooManyRanges => f.write_str("ack has too many ranges"),
            Self::StreamEnd => f.write_str("stream data ends beyond 2^62 - 1"),
            Self::RekeyKind => f.write_str("rekey kind is not 0 or 1"),
        }
    }
}

impl core::error::Error for FrameError {}

/// A frame, borrowing its data from the packet payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Frame<'a> {
    /// A run of `len` PADDING bytes.
    Padding {
        /// How many zero bytes.
        len: usize,
    },
    /// PING.
    Ping,
    /// ACK; only decoding produces one, [`write_ack`] encodes one.
    Ack(Ack<'a>),
    /// `RESET_STREAM`.
    ResetStream {
        /// The stream.
        id: u64,
        /// The application error code.
        error: u64,
        /// The final size of the stream.
        final_size: u64,
    },
    /// `STOP_SENDING`: the receiver asks the sender to abandon the stream; the sender resets it with `error`.
    StopSending {
        /// The stream.
        id: u64,
        /// The application error code the sender resets with.
        error: u64,
    },
    /// STREAM.
    Stream {
        /// The stream.
        id: u64,
        /// The offset of `data` in the stream; the OFF bit is set when it is not 0.
        offset: u64,
        /// Whether this ends the stream.
        fin: bool,
        /// The data.
        data: &'a [u8],
        /// Whether the length is omitted and the data runs to the end of the packet (the frame must be last).
        implicit_len: bool,
    },
    /// `MAX_STREAM_DATA`.
    MaxStreamData {
        /// The stream.
        id: u64,
        /// The new stream-level limit.
        max: u64,
    },
    /// `MAX_STREAMS`.
    MaxStreams {
        /// The streams the sender admits in all, of every kind.
        limit: u64,
    },
    /// `PATH_CHALLENGE`.
    PathChallenge([u8; 8]),
    /// `PATH_RESPONSE`.
    PathResponse([u8; 8]),
    /// CLOSE: the connection ends with this code, and the sender sends nothing more.
    Close {
        /// The error code.
        error: u64,
    },
    /// DATAGRAM.
    Datagram {
        /// The datagram data.
        data: &'a [u8],
        /// Whether the length is omitted and the data runs to the end of the packet (the frame must be last).
        implicit_len: bool,
    },
    /// `MTU_PROBE_ECHO`.
    MtuProbeEcho {
        /// The size of the probe that arrived.
        mtu: u16,
    },
    /// SLEEP.
    Sleep,
    /// WAKE.
    Wake,
    /// REKEY: one message of a key roll.
    Rekey(Rekey),
    /// READY.
    Ready,
    /// `NEW_TICKETS`: the resumption tickets the server issued, sent inside the protected channel.
    NewTickets(TicketBatch),
    /// An extension frame of type `0x40` or more, passed through unparsed.
    Extension {
        /// The type.
        ty: u64,
        /// The body, after the length.
        body: &'a [u8],
    },
}
