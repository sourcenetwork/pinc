//! Test-only observation of the stream table, for trace validation (cargo feature `trace`, off by default).
//!
//! [`Streams::trace_view`](super::Streams::trace_view) shows the state the receive and credit path works on: per
//! slot the held chunk numbers, the stored ranges, the read position, the credit and the send half's state that
//! frees the slot and the stop request; per table the counters, the window target, the delivery meter and the pool
//! chunks the others hold. Nothing here is compiled without the feature, and nothing here feeds back into the table.

use alloc::vec::Vec;

use super::StreamId;

/// One slot of the table.
#[allow(
    clippy::struct_excessive_bools,
    reason = "a plain record of the flags the model compares"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlotView {
    /// The stream id, or `u64::MAX` for a free slot.
    pub id: StreamId,
    /// The receive half is open.
    pub open: bool,
    /// The chunk numbers the receive ring holds.
    pub held: Vec<u64>,
    /// The stored ranges, ascending.
    pub ranges: Vec<(u64, u64)>,
    /// The read position.
    pub read: u64,
    /// The highest offset received.
    pub highest: u64,
    /// The end of the prefix stored without holes.
    pub contig: u64,
    /// The final size, if fixed.
    pub fin: Option<u64>,
    /// The receive limit advertised.
    pub limit: u64,
    /// The window size the limit is kept ahead of the read position.
    pub size: u64,
    /// A new limit is waiting to be sent.
    pub pending: bool,
    /// A grant is due but the pool had no room.
    pub deferred: bool,
    /// The peer's reset code, if the stream was reset.
    pub reset: Option<u64>,
    /// The application has seen the end.
    pub observed: bool,
    /// The send half is closed, or its end marker and every byte are acknowledged.
    pub send_done: bool,
    /// The send half's reset: 0 none, 1 pending, 2 sent, 3 acknowledged.
    pub send_reset: u8,
    /// The error code of the send half's reset until it is acknowledged.
    pub send_code: Option<u64>,
    /// The receive half's stop request: 0 none, 1 pending, 2 sent, 3 acknowledged.
    pub stop: u8,
    /// The error code of the stop request until it is acknowledged.
    pub stop_code: Option<u64>,
}

/// The table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableView {
    /// Every slot, free ones included.
    pub slots: Vec<SlotView>,
    /// The next peer stream index per class (bidirectional, unidirectional).
    pub remote_next: [u64; 2],
    /// The streams this endpoint opened per class.
    pub local_opened: [u64; 2],
    /// Live peer-opened streams.
    pub remote_live: u64,
    /// Live locally opened streams.
    pub local_live: u64,
    /// Pool chunks charged and not held by a receive ring.
    pub ext: u64,
    /// The window size the delivery rate asks for.
    pub target: u64,
    /// The delivery meter: the epoch start, the bytes in it, the last rate.
    pub meter: (Option<u64>, u64, u64),
}
