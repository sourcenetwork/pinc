//! Test-only observation of the stream table, for trace validation (cargo feature `trace`, off by default).
//!
//! [`Streams::trace_view`](super::Streams::trace_view) shows the state the receive and credit path works on: per
//! slot the held chunk numbers, the stored ranges, the read position, the credit, the delivery meter, the send half's
//! state that
//! frees the slot, the stop request and the ordinal of a stream we opened; per table the counters,
//! the pool chunks the others hold and whether opens may pass the peer's limit. Nothing here is
//! compiled without the feature, and nothing here feeds back into the table.

use alloc::vec::Vec;

use super::send::Send as Half;
use super::{ControlFrame, SendView, StreamChunk, StreamError, StreamId, StreamSource};

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
    /// The stream credit: the limit on the streams we may open in all and the limit last advertised.
    pub admit: [u64; 2],
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

/// The state of one send half.
#[allow(
    clippy::struct_excessive_bools,
    reason = "a plain record of the flags the model compares"
)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SendHalfView {
    /// The half is open.
    pub open: bool,
    /// The stream sends from application storage.
    pub is_source: bool,
    /// The source is still held.
    pub has_source: bool,
    /// The bytes written.
    pub written: u64,
    /// One past the highest offset sent.
    pub sent_max: u64,
    /// The send limit.
    pub limit: u64,
    /// The ranges declared lost and queued, ascending.
    pub lost: Vec<(u64, u64)>,
    /// The ranges acknowledged, ascending.
    pub acked: Vec<(u64, u64)>,
    /// The end of the acknowledged prefix.
    pub acked_prefix: u64,
    /// The final size, if fixed.
    pub final_size: Option<u64>,
    /// The end marker: 0 none, 1 pending, 2 sent, 3 acknowledged.
    pub fin: u8,
    /// The reset: 0 none, 1 pending, 2 sent, 3 acknowledged.
    pub reset: u8,
    /// The reset's error code while it is pending or sent.
    pub reset_code: Option<u64>,
    /// The reset's final size while it is pending or sent.
    pub reset_final: Option<u64>,
    /// A write was cut short by the connection's send buffer cap.
    pub cap_cut: bool,
    /// The chunk numbers the ring holds.
    pub held: Vec<u64>,
    /// The bytes written and not acknowledged.
    pub buffered: u64,
    /// A retransmission or end marker waits, fresh data waits.
    pub wants: (bool, bool),
    /// Everything this half will send has left.
    pub flushed: bool,
    /// Nothing more will be sent.
    pub done: bool,
    /// A stop request would reset this half now.
    pub can_stop: bool,
    /// A reset frame waits to be taken.
    pub control_pending: bool,
    /// What a host that paces on the half sees.
    pub view: SendView,
    /// The half is closed or its end and every byte are acknowledged.
    pub fin_done: bool,
    /// The chunks the pool has free.
    pub available: u64,
    /// The chunks other users of the pool hold.
    pub ext: u64,
}

/// A send half with a pool of its own and the chunks other users of the pool hold, for trace validation.
pub struct SendProbe<S: StreamSource, const C: usize> {
    pool: super::pool::BufferPool<'static>,
    half: Half<S, C>,
    ext: Vec<super::pool::Chunk>,
}

impl<S: StreamSource, const C: usize> SendProbe<S, C> {
    /// A half over a pool of `chunks` chunks, open with the send limit `limit`, or unopened for `None` (the send half
    /// of a receive-only stream).
    pub fn new(chunks: usize, limit: Option<u64>) -> Self {
        let mut half = Half::NEW;
        if let Some(limit) = limit {
            half.init(limit);
        }
        Self {
            pool: super::pool::BufferPool::new_boxed(chunks),
            half,
            ext: Vec::new(),
        }
    }

    /// `Send::write`.
    ///
    /// # Errors
    /// As `Send::write`.
    pub fn write(&mut self, data: &[u8], room: u64) -> Result<usize, StreamError> {
        self.half.write(&mut self.pool, data, room)
    }

    /// `Send::finish`.
    ///
    /// # Errors
    /// As `Send::finish`.
    pub fn finish(&mut self) -> Result<(), StreamError> {
        self.half.finish()
    }

    /// `Send::open_source`.
    ///
    /// # Errors
    /// As `Send::open_source`.
    pub fn open_source(&mut self, source: S, len: u64) -> Result<(), StreamError> {
        self.half.open_source(source, len)
    }

    /// `Send::reset`.
    ///
    /// # Errors
    /// As `Send::reset`.
    pub fn reset(&mut self, code: u64) -> Result<(), StreamError> {
        self.half.reset(&mut self.pool, code)
    }

    /// `Send::raise_limit`.
    pub fn raise_limit(&mut self, limit: u64) {
        self.half.raise_limit(limit);
    }

    /// `Send::next_frame`.
    pub fn next_frame(&mut self, id: StreamId, retx: bool, budget: usize) -> Option<StreamChunk> {
        self.half.next_frame(id, retx, budget)
    }

    /// `Send::copy_out`.
    ///
    /// # Errors
    /// As `Send::copy_out`.
    pub fn copy_out(&mut self, chunk: &StreamChunk, dst: &mut [u8]) -> Result<usize, StreamError> {
        self.half.copy_out(&self.pool, chunk, dst)
    }

    /// `Send::on_lost`.
    pub fn on_lost(&mut self, offset: u64, len: u64, fin: bool) -> usize {
        self.half.on_lost(offset, len, fin)
    }

    /// `Send::on_acked`.
    pub fn on_acked(&mut self, offset: u64, len: u64, fin: bool) -> usize {
        self.half.on_acked(&mut self.pool, offset, len, fin)
    }

    /// `Send::is_acked`.
    pub fn is_acked(&self, offset: u64, len: u64) -> bool {
        self.half.is_acked(offset, len)
    }

    /// `Send::clip`.
    pub fn clip(&self, offset: u64) -> u64 {
        self.half.clip(offset)
    }

    /// `Send::take_control`.
    pub fn take_control(&mut self, id: StreamId) -> Option<ControlFrame> {
        self.half.take_control(id)
    }

    /// `Send::control_lost`.
    pub fn control_lost(&mut self, frame: &ControlFrame) {
        self.half.control_lost(frame);
    }

    /// `Send::reset_acked`.
    pub fn reset_acked(&mut self) {
        self.half.reset_acked();
    }

    /// Other users of the pool now hold `n` chunks (fewer if the pool has no more); the count held.
    pub fn set_ext(&mut self, n: usize) -> usize {
        while self.ext.len() < n {
            let Ok(c) = self.pool.alloc_chunk() else { break };
            self.ext.push(c);
        }
        while self.ext.len() > n {
            if let Some(c) = self.ext.pop() {
                self.pool.free_chunk(c);
            }
        }
        self.ext.len()
    }

    /// The whole state of the half.
    pub fn view(&self) -> SendHalfView {
        self.half.trace_half(&self.pool, self.ext.len() as u64)
    }
}
