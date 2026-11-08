//! Streams, flow control, datagrams and the buffer pool behind them.
//!
//! The layer is a sans-IO state machine: parsed frames go in as plain arguments, frame descriptions come out, and
//! recovery feedback (acknowledged, lost, late-acknowledged ranges) is applied through the `on_*` methods. All bytes
//! live in the [`pool::BufferPool`]; the stream table, the range maps and the queues are fixed-size and never allocate.
//!
//! Invariants:
//! - every chunk a stream, queue or buffer holds is charged to the pool and returned when its owner closes or drains;
//! - received credit never lets the peer send more than the pool can store at the moment it is granted;
//! - a limit, once advertised or received, never shrinks, and a final size, once fixed, never changes;
//! - a stream id's low bit is the initiator (0 = client) and its second bit is set for unidirectional streams.
#![allow(
    clippy::cast_possible_truncation,
    reason = "offsets are reduced modulo a chunk or ring size before narrowing"
)]
#![allow(clippy::doc_markdown, reason = "frame names such as MAX_DATA are prose, not code")]

mod flow;
mod recv;
mod send;
mod table;

pub mod datagram;
pub mod pool;
mod ranges;

use core::fmt;

pub use table::Streams;

/// A QUIC stream id: initiator in bit 0 (0 = client), unidirectional in bit 1, the sequence number above.
pub type StreamId = u64;

/// The largest representable stream offset (2^62 - 1).
pub const MAX_OFFSET: u64 = (1 << 62) - 1;
/// The default number of streams the peer may open per direction class.
pub const DEFAULT_MAX_STREAMS: u64 = 100;
/// The default initial per-stream and connection receive window (1.25 MiB).
pub const DEFAULT_INITIAL_WINDOW: u64 = 1_310_720;
/// The default per-stream window ceiling (16 MiB).
pub const DEFAULT_MAX_STREAM_WINDOW: u64 = 16 * 1024 * 1024;
/// The default connection window ceiling (24 MiB).
pub const DEFAULT_MAX_CONN_WINDOW: u64 = 24 * 1024 * 1024;
/// The most disjoint ranges a stream tracks per range map (received, acknowledged, lost).
pub const RANGES: usize = 16;

/// Whether `id` is unidirectional.
pub const fn is_uni(id: StreamId) -> bool {
    id & 2 != 0
}

/// Whether `id` was initiated by the client.
pub const fn is_client_initiated(id: StreamId) -> bool {
    id & 1 == 0
}

/// Why a stream operation failed. The first group are protocol violations by the peer (close the connection with
/// the matching transport error); the rest are local conditions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamError {
    /// The peer opened a stream beyond the limit it was granted (STREAM_LIMIT_ERROR).
    StreamLimit,
    /// A frame arrived for a direction the stream does not have, or for a local stream never opened (STREAM_STATE_ERROR).
    StreamState,
    /// Data or a final size went beyond the advertised credit (FLOW_CONTROL_ERROR).
    FlowControl,
    /// The final size changed, or data went beyond it (FINAL_SIZE_ERROR).
    FinalSize,
    /// Retransmitted or overlapping bytes differ from those already stored (PROTOCOL_VIOLATION).
    Conflict,
    /// The stream table has no free slot. Treat a peer-opened stream as STREAM_LIMIT_ERROR.
    TableFull,
    /// The buffer pool has no chunk left; drop the packet unacknowledged and let the peer retransmit.
    Exhausted,
    /// The stream has more disjoint received ranges than it can track; drop the frame unacknowledged.
    Fragmented,
    /// The stream is unknown or already closed.
    UnknownStream,
    /// The stream was already finished or reset.
    Finished,
    /// The call does not fit the stream (a write on a source-backed stream, a source on a buffered one).
    WrongKind,
    /// More bytes were consumed than are readable.
    InvalidConsume,
    /// The bytes of a requested range are no longer available; a source returned fewer bytes than asked.
    DataUnavailable,
    /// The destination of a copy is shorter than the frame.
    BufferTooSmall,
}

impl fmt::Display for StreamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::StreamLimit => "stream limit exceeded",
            Self::StreamState => "frame not valid for the stream",
            Self::FlowControl => "flow control credit exceeded",
            Self::FinalSize => "final size violated",
            Self::Conflict => "overlapping bytes differ",
            Self::TableFull => "stream table full",
            Self::Exhausted => "buffer pool exhausted",
            Self::Fragmented => "too many disjoint ranges",
            Self::UnknownStream => "unknown or closed stream",
            Self::Finished => "stream already finished",
            Self::WrongKind => "call does not fit the stream kind",
            Self::InvalidConsume => "consumed more than readable",
            Self::DataUnavailable => "stream data unavailable",
            Self::BufferTooSmall => "destination too small",
        })
    }
}

impl core::error::Error for StreamError {}

impl From<pool::PoolExhausted> for StreamError {
    fn from(_: pool::PoolExhausted) -> Self {
        Self::Exhausted
    }
}

/// A stream frame ready to be written: the caller copies the data with [`Streams::copy_out`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StreamChunk {
    /// The stream.
    pub id: StreamId,
    /// The offset of the first byte.
    pub offset: u64,
    /// The number of data bytes.
    pub len: usize,
    /// Whether the frame carries the end of the stream.
    pub fin: bool,
}

/// A flow-control, reset or stop frame to send, as plain data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlFrame {
    /// MAX_DATA with the new connection limit.
    MaxData(u64),
    /// MAX_STREAM_DATA with the new stream limit.
    MaxStreamData {
        /// The stream.
        id: StreamId,
        /// The new limit.
        max: u64,
    },
    /// MAX_STREAMS with the new count.
    MaxStreams {
        /// Bidirectional (true) or unidirectional streams.
        bidi: bool,
        /// The new count.
        max: u64,
    },
    /// DATA_BLOCKED at the connection limit.
    DataBlocked(u64),
    /// STREAM_DATA_BLOCKED at the stream limit.
    StreamDataBlocked {
        /// The stream.
        id: StreamId,
        /// The limit that blocked it.
        limit: u64,
    },
    /// STREAMS_BLOCKED at the stream count limit.
    StreamsBlocked {
        /// Bidirectional (true) or unidirectional streams.
        bidi: bool,
        /// The limit that blocked it.
        limit: u64,
    },
    /// RESET_STREAM.
    ResetStream {
        /// The stream.
        id: StreamId,
        /// The application error code.
        error_code: u64,
        /// The final size.
        final_size: u64,
    },
    /// STOP_SENDING.
    StopSending {
        /// The stream.
        id: StreamId,
        /// The application error code.
        error_code: u64,
    },
}

/// The state of the receive side of a stream.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecvStatus {
    /// More data may arrive or is waiting to be read.
    Open,
    /// The end was received and every byte consumed.
    Finished,
    /// The peer reset the stream with this error code.
    Reset(u64),
}

/// Application storage a stream sends from without buffering: lost ranges are read again from it.
pub trait StreamSource {
    /// Fill `dst` with the bytes at `offset`; return how many were written (all of `dst` unless the source ended).
    fn read_at(&mut self, offset: u64, dst: &mut [u8]) -> usize;
}

/// A source type for tables that only carry buffered streams.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoSource;

impl StreamSource for NoSource {
    fn read_at(&mut self, _offset: u64, _dst: &mut [u8]) -> usize {
        0
    }
}

/// What the peer allows us to send, from its transport parameters.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PeerLimits {
    /// Connection-level credit.
    pub max_data: u64,
    /// Credit on bidirectional streams the peer opened.
    pub max_stream_data_bidi_local: u64,
    /// Credit on bidirectional streams we opened.
    pub max_stream_data_bidi_remote: u64,
    /// Credit on unidirectional streams we opened.
    pub max_stream_data_uni: u64,
    /// How many bidirectional streams we may open.
    pub max_streams_bidi: u64,
    /// How many unidirectional streams we may open.
    pub max_streams_uni: u64,
}

/// The stream layer's configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
    /// Whether this endpoint is the client (decides the initiator bit of the streams it opens).
    pub is_client: bool,
    /// The initial receive window of every stream.
    pub initial_stream_window: u64,
    /// The ceiling the stream windows autotune to.
    pub max_stream_window: u64,
    /// The initial connection receive window.
    pub initial_conn_window: u64,
    /// The ceiling the connection window autotunes to.
    pub max_conn_window: u64,
    /// How many bidirectional streams the peer may open.
    pub max_streams_bidi: u64,
    /// How many unidirectional streams the peer may open.
    pub max_streams_uni: u64,
    /// The peer's limits, if already known; otherwise set them with [`Streams::set_peer_limits`].
    pub peer: PeerLimits,
}

impl Config {
    /// The defaults for the given role.
    pub const fn new(is_client: bool) -> Self {
        Self {
            is_client,
            initial_stream_window: DEFAULT_INITIAL_WINDOW,
            max_stream_window: DEFAULT_MAX_STREAM_WINDOW,
            initial_conn_window: DEFAULT_INITIAL_WINDOW,
            max_conn_window: DEFAULT_MAX_CONN_WINDOW,
            max_streams_bidi: DEFAULT_MAX_STREAMS,
            max_streams_uni: DEFAULT_MAX_STREAMS,
            peer: PeerLimits {
                max_data: 0,
                max_stream_data_bidi_local: 0,
                max_stream_data_bidi_remote: 0,
                max_stream_data_uni: 0,
                max_streams_bidi: 0,
                max_streams_uni: 0,
            },
        }
    }
}

/// Counters for events the layer absorbed instead of failing.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StreamStats {
    /// Range maps that were full, so a lost range was widened or an acknowledgement turned back into a retransmission.
    pub range_overflows: u64,
}
