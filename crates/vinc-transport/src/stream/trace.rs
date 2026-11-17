//! Test-only observation of the stream table, for trace validation (cargo feature `trace`, off by default).
//!
//! [`Streams::trace_view`](super::Streams::trace_view) shows the state the receive and credit path works on: per
//! slot the held chunk numbers, the stored ranges, the read position, the credit, the delivery meter, the send half's
//! state that
//! frees the slot, the stop request and the ordinal of a stream we opened; per table the counters,
//! the pool chunks the others hold and whether opens may pass the peer's limit. Nothing here is
//! compiled without the feature, and nothing here feeds back into the table.

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
    /// The delivery meter of this stream: the epoch start, the bytes in it, the last rate.
    pub meter: (Option<u64>, u64, u64),
    /// A new limit is waiting to be sent.
    pub pending: bool,
    /// A grant is due but the pool had no room.
    pub deferred: bool,
    /// The peer's reset code, if the stream was reset.
    pub reset: Option<u64>,
    /// The application has seen the end.
    pub observed: bool,
    /// The application abandoned the receive half (a stop): what arrives is checked and discarded.
    pub dropped: bool,
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
    /// For a stream we opened, how many we had opened in all, itself included: its first frame waits until the peer's
    /// limit covers it. 0 for a stream the peer opened.
    pub ordinal: u64,
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
    /// The mark of the slots: one past the highest slot a stream holds; every slot past it is new.
    pub high_water: u64,
    /// The stream credit: the limit on the streams we may open in all, the limit last advertised, and the streams
    /// admitted when it was set.
    pub admit: [u64; 3],
    /// A `MAX_STREAMS` frame is waiting to be sent.
    pub admit_pend: bool,
    /// Opens may pass the limit on what we may open, which the peer has not stated yet.
    pub early: bool,
}

/// An early-data buffer with a pool of its own, for trace validation of the buffer of packets held for want of keys.
#[derive(Debug)]
pub struct EarlyProbe {
    pool: super::pool::BufferPool<'static>,
    early: super::datagram::EarlyData,
}

impl EarlyProbe {
    /// The most packets the buffer holds.
    pub const MAX: usize = super::datagram::MAX_EARLY_PACKETS;

    /// An empty buffer over a pool of `chunks` chunks.
    pub fn new(chunks: usize) -> Self {
        Self {
            pool: super::pool::BufferPool::new_boxed(chunks),
            early: super::datagram::EarlyData::new(),
        }
    }

    /// Hold a packet; whether it was kept.
    pub fn push(&mut self, packet: &[u8]) -> bool {
        self.early.push(&mut self.pool, packet)
    }

    /// The oldest packet held.
    pub fn front(&self) -> Option<Vec<u8>> {
        self.early.front(&self.pool).map(<[u8]>::to_vec)
    }

    /// Remove the oldest packet.
    pub fn pop(&mut self) {
        self.early.pop(&mut self.pool);
    }

    /// Drop every packet.
    pub fn clear(&mut self) {
        self.early.clear(&mut self.pool);
    }

    /// How many packets are held.
    pub fn len(&self) -> usize {
        self.early.len()
    }

    /// Whether no packet is held.
    pub fn is_empty(&self) -> bool {
        self.early.is_empty()
    }

    /// The packets dropped so far.
    pub fn dropped(&self) -> u64 {
        self.early.dropped()
    }

    /// The pool chunks the buffer holds.
    pub fn used_chunks(&self) -> usize {
        self.pool.used_chunks()
    }
}
