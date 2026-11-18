//! Streams, receive windows, datagrams and the buffer pool behind them.
//!
//! The layer is a sans-IO state machine: parsed frames go in as plain arguments, frame descriptions come out, and
//! recovery feedback (acknowledged, lost, late-acknowledged ranges) is applied through the `on_*` methods. All bytes
//! live in the [`pool::BufferPool`]; the stream table, the range maps and the queues are fixed-size and never allocate.
//!
//! Invariants:
//! - every chunk a stream, queue or buffer holds is charged to the pool and returned when its owner closes or drains;
//! - the bytes buffered never exceed the pool: a frame takes free chunks or is held back (answered with nothing, so its
//!   sender repeats it) and counted in `StreamStats::held_back`;
//! - the pool ledger counts, for each receive half, the chunks its credit may still claim: the first [`FIRST_CHARGE`]
//!   bytes of its window while the stream has carried no data, its whole window from the first byte on; the stream
//!   credit keeps [`FIRST_CHARGE`] for each stream the peer may still open. A window grant is made only while the
//!   ledger, with it, fits the bytes the pool has left. A peer stream inside the credit is admitted with no pool test
//!   (it takes no chunk, and the credit kept its first charge), so a frame that opens many skipped streams at once is
//!   never held back for them. The ledger passes the pool only when streams start to carry data whose windows do not
//!   fit together, or when other users of the pool take chunks; no window is granted until it fits again, so each of
//!   those streams stays within the window it has. The window the peer may use is the full one from the first byte,
//!   and the sum of the windows may exceed the pool;
//! - admitting one more stream (a raise of the stream credit, a peer stream beyond the credit, a stream we open) asks
//!   less than a window grant: that the pool has left a first charge for the new stream beside one for each stream
//!   already open. Streams that carry data and stay open so do not shut out new ones for the size of their windows;
//!   what they may then send together can pass the pool, and the frame that finds no chunk is held back;
//! - a limit, once advertised or received, never shrinks, and a final size, once fixed, never changes;
//! - the peer's streams that count against its limit never exceed the limit; a stream stops counting when what the
//!   peer sent on it is whole and read and our answer has left with nothing queued to be sent again, so a request and
//!   reply stream frees its place when the reply is sent and not a round trip later, while its slot is held until
//!   the reply is acknowledged; an excess peer stream is stored nowhere and its packet goes unacknowledged, so its
//!   opener retransmits it from the start once there is room;
//! - streams are served in order of urgency, then id, so a better stream drains before a worse one gets anything;
//! - a stream id's low bit is the initiator (0 = client) and its second bit is set for unidirectional streams.
#![allow(
    clippy::cast_possible_truncation,
    reason = "offsets are reduced modulo a chunk or ring size before narrowing"
)]

mod credit;
mod flow;
pub(crate) mod lazy;
mod recv;
mod send;
mod table;

pub mod datagram;
pub mod pool;
mod ranges;
pub mod spill;
#[cfg(feature = "trace")]
pub mod trace;

use core::fmt;

pub use table::Streams;

/// A stream id: initiator in bit 0 (0 = client), unidirectional in bit 1, the sequence number above.
pub type StreamId = u64;

/// The largest representable stream offset (2^62 - 1).
pub const MAX_OFFSET: u64 = (1 << 62) - 1;
/// The default number of peer-opened streams that may be live at once.
pub const DEFAULT_MAX_STREAMS: u64 = 100;
/// The default initial per-stream receive window (1.25 MiB).
pub const DEFAULT_INITIAL_WINDOW: u64 = 1_310_720;
/// The default per-stream window ceiling (16 MiB).
pub const DEFAULT_MAX_STREAM_WINDOW: u64 = 16 * 1024 * 1024;
/// The bytes of a receive window the pool ledger counts while the stream has carried no data (4 chunks), and the room
/// the stream credit keeps for each stream the peer may still open. The whole window is counted from the first byte.
pub const FIRST_CHARGE: u64 = 4 * pool::CHUNK_SIZE as u64;
/// The urgency a stream starts with; a lower number is served first.
pub const DEFAULT_URGENCY: u8 = 3;
/// The disjoint ranges a stream tracks inline of what it declared lost; past them the set moves into a slot of the
/// endpoint's spill arena ([`spill::SLOT_RANGES`] ranges), so a loss burst no longer widens a range over bytes that were
/// not lost. With no slot free it widens, as it did before the arena.
pub const RANGES: usize = 16;
/// The disjoint ranges a stream tracks inline of what the peer acknowledged; past them the set moves into a spill slot.
/// Only past that slot, or with no slot free, is a range sent again so the acknowledgement can be taken in order.
pub const ACKED_RANGES: usize = 64;
/// The disjoint ranges a stream tracks inline of what it received; past them the set moves into a spill slot. A packet
/// that fits neither is dropped unacknowledged (`Fragmented`), so the sender repeats it. Inline, the deepest reordering
/// scenario measured needed 65 at 128 packet ranges; scattered drops at a large window need more.
pub const RECV_RANGES: usize = 96;

/// What the send half of a stream knows, for a host that paces work on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SendView {
    /// One past the highest stream offset sent so far.
    pub sent: u64,
    /// The lowest stream offset that was declared lost and waits to be sent again.
    pub lost: Option<u64>,
    /// Nothing more will be sent or sent again: the end and every byte are acknowledged, or the half is closed.
    pub done: bool,
}

/// Whether `id` is unidirectional.
pub const fn is_uni(id: StreamId) -> bool {
    id & 2 != 0
}

/// Whether `id` was initiated by the client.
pub const fn is_client_initiated(id: StreamId) -> bool {
    id & 1 == 0
}

/// Why a stream operation failed. The first group are violations by the peer (close the connection); the rest are
/// local conditions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StreamError {
    /// The peer opened a stream far beyond the next expected one, or we are at the cap of streams we may open.
    StreamLimit,
    /// A frame arrived for a direction the stream does not have, or for a local stream never opened.
    StreamState,
    /// Data or a final size went beyond the advertised credit.
    FlowControl,
    /// The final size changed, or data went beyond it.
    FinalSize,
    /// Retransmitted or overlapping bytes differ from those already stored (a violation by the peer).
    Conflict,
    /// The stream table has no free slot for a stream we open.
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

/// A window update or reset frame to send, as plain data.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ControlFrame {
    /// A new send limit for a stream.
    MaxStreamData {
        /// The stream.
        id: StreamId,
        /// The new limit.
        max: u64,
    },
    /// A request to the sender to stop sending on a stream.
    StopSending {
        /// The stream.
        id: StreamId,
        /// The application error code the sender resets with.
        error_code: u64,
    },
    /// A new limit on the streams the peer may have opened in all (`MAX_STREAMS`).
    MaxStreams {
        /// The new limit.
        limit: u64,
    },
    /// A stream reset.
    ResetStream {
        /// The stream.
        id: StreamId,
        /// The application error code.
        error_code: u64,
        /// The final size.
        final_size: u64,
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

/// What the peer allows us to send, from its credit record.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PeerLimits {
    /// The send window of every stream we write to.
    pub window: u64,
    /// How many streams we may have open at once.
    pub max_streams: u64,
}

/// The stream layer's configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Config {
    /// Whether this endpoint is the client (decides the initiator bit of the streams it opens).
    pub is_client: bool,
    /// The initial receive window of every stream, and the least a window is ever sized to.
    pub initial_stream_window: u64,
    /// The ceiling the stream windows grow to.
    pub max_stream_window: u64,
    /// How many peer-opened streams may be open at once.
    pub max_streams: u64,
    /// The peer's limits, if already known; otherwise set them with [`Streams::set_peer_limits`].
    pub peer: PeerLimits,
    /// Whether the table gives the peer stream credit and keeps the pool for it. Turn it off only for a table used on
    /// its own, with no peer that honours the credit: it then advertises none.
    pub credit: bool,
}

impl Config {
    /// The defaults for the given role.
    pub const fn new(is_client: bool) -> Self {
        Self {
            is_client,
            initial_stream_window: DEFAULT_INITIAL_WINDOW,
            max_stream_window: DEFAULT_MAX_STREAM_WINDOW,
            max_streams: DEFAULT_MAX_STREAMS,
            peer: PeerLimits {
                window: 0,
                max_streams: 0,
            },
            credit: true,
        }
    }
}

/// Counters for events the layer absorbed instead of failing.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StreamStats {
    /// Range maps that were full (inline with no spill slot to take, or in their slot), so a lost range was widened, an
    /// acknowledgement turned back into a retransmission, or a received frame was refused (`Fragmented`; its packet went
    /// unacknowledged). A spill refused for want of an arena slot is counted by the pool (`spill_refused`).
    pub range_overflows: u64,
    /// Times a range map outgrew its inline array and moved into an arena slot (received, lost or acknowledged ranges).
    /// A map that holds at most half its inline capacity again moves back and returns the slot, so a stream can count
    /// more than once.
    pub range_spills: u64,
    /// Peer stream frames held back for want of a slot or of a free chunk in the pool (their packet went
    /// unacknowledged). Nonzero means the peer opened streams beyond the credit it was given, or the pool was full:
    /// other users took it, or more windows were in use at once than it holds.
    pub held_back: u64,
}
