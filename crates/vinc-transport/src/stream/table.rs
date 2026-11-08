//! The stream table: ids, limits, the control-frame queue and the glue between the halves of each stream.
//!
//! Invariants: `ids[i]` is the id held by slot `i` (or `NONE`) and `hot[i]` is a superset of what slot `i` can emit
//! (a stale bit costs one failed attempt, a missing bit would starve the slot, so every mutator refreshes it); a slot
//! is freed only when both halves are done, which returns all of its chunks to the pool and credits a peer-opened
//! stream back to the peer through MAX_STREAMS; stream ids of a class are opened in order and never reused.

use super::flow::{ConnRecv, ConnSend, Tune, Window};
use super::pool::{BufferPool, CHUNK_SIZE};
use super::recv::Recv;
use super::send::Send;
use super::{
    Config, ControlFrame, NoSource, PeerLimits, RecvStatus, StreamChunk, StreamError, StreamId, StreamSource,
    StreamStats, is_uni,
};

const NONE: u64 = u64::MAX;
const HOT_RETX: u8 = 1;
const HOT_NEW: u8 = 2;
const HOT_CTL: u8 = 4;

#[derive(Debug)]
struct Slot<S, const C: usize> {
    recv: Recv<C>,
    send: Send<S, C>,
}

impl<S: StreamSource, const C: usize> Slot<S, C> {
    const NEW: Self = Self {
        recv: Recv::NEW,
        send: Send::NEW,
    };
}

/// The class index of a stream id: 0 for bidirectional, 1 for unidirectional.
const fn class(id: StreamId) -> usize {
    if is_uni(id) { 1 } else { 0 }
}

/// The stream table of a connection: `N` slots, each with receive and send chunk rings of `C` entries.
///
/// All bytes live in the [`BufferPool`] passed to the mutating calls; the table itself is a fixed-size value that never
/// allocates. A slot is about `8 * C` bytes plus a few hundred, so a large `C` wants the value boxed or static.
pub struct Streams<S: StreamSource = NoSource, const N: usize = 100, const C: usize = 1025> {
    is_client: bool,
    ids: [u64; N],
    hot: [u8; N],
    slots: [Slot<S, C>; N],
    conn_recv: ConnRecv,
    conn_send: ConnSend,
    stream_window: u64,
    max_stream_window: u64,
    peer: PeerLimits,
    local_opened: [u64; 2],
    open_limit: [u64; 2],
    remote_next: [u64; 2],
    remote_limit: [u64; 2],
    max_streams_pending: [bool; 2],
    blocked_sent: [Option<u64>; 2],
    blocked_pending: [bool; 2],
    open: usize,
    rr: usize,
    stats: StreamStats,
}

impl<S: StreamSource, const N: usize, const C: usize> Streams<S, N, C> {
    /// A table for `config`. Windows are clamped to what the chunk rings and half of the pool's budget can hold, and
    /// the peer-opened stream limits to the table size.
    pub fn new(config: &Config, pool: &BufferPool<'_>) -> Self {
        const { assert!(C >= 2 && N >= 1) };
        let chunk = CHUNK_SIZE as u64;
        let half = pool.budget_bytes() / 2 / chunk * chunk;
        let max_stream = config.max_stream_window.min((C as u64 - 1) * chunk).min(half);
        let max_conn = config.max_conn_window.min(half);
        let conn_window = config.initial_conn_window.min(max_conn);
        let cap = N as u64;
        let mut streams = Self {
            is_client: config.is_client,
            ids: [NONE; N],
            hot: [0; N],
            slots: [const { Slot::NEW }; N],
            conn_recv: ConnRecv {
                win: Window::new(conn_window, max_conn),
                received: 0,
                consumed: 0,
            },
            conn_send: ConnSend::new(0),
            stream_window: config.initial_stream_window.min(max_stream),
            max_stream_window: max_stream,
            peer: PeerLimits::default(),
            local_opened: [0; 2],
            open_limit: [0; 2],
            remote_next: [0; 2],
            remote_limit: [config.max_streams_bidi.min(cap), config.max_streams_uni.min(cap)],
            max_streams_pending: [false; 2],
            blocked_sent: [None; 2],
            blocked_pending: [false; 2],
            open: 0,
            rr: 0,
            stats: StreamStats::default(),
        };
        streams.set_peer_limits(&config.peer);
        streams
    }

    /// Counters of absorbed events.
    pub const fn stats(&self) -> StreamStats {
        self.stats
    }

    /// The number of streams currently in the table.
    pub const fn open_streams(&self) -> usize {
        self.open
    }

    /// The connection receive limit last advertised.
    pub const fn recv_limit(&self) -> u64 {
        self.conn_recv.win.limit
    }

    /// The current connection receive window.
    pub const fn recv_window(&self) -> u64 {
        self.conn_recv.win.size()
    }

    /// The receive window and advertised limit of a stream.
    pub fn stream_recv_window(&self, id: StreamId) -> Option<(u64, u64)> {
        let win = &self.slot(self.find(id)?)?.recv.win;
        Some((win.size(), win.limit))
    }

    /// Apply the peer's limits (its transport parameters, or later raises). Limits only grow.
    pub fn set_peer_limits(&mut self, limits: &PeerLimits) {
        self.peer = *limits;
        self.conn_send.limit = self.conn_send.limit.max(limits.max_data);
        self.open_limit[0] = self.open_limit[0].max(limits.max_streams_bidi);
        self.open_limit[1] = self.open_limit[1].max(limits.max_streams_uni);
        for i in 0..N {
            let limit = self.ids.get(i).map(|&id| self.send_limit(id));
            if let (Some(limit), Some(slot)) = (limit, self.slots.get_mut(i)) {
                slot.send.raise_limit(limit);
            }
            self.refresh(i);
        }
    }

    fn is_local(&self, id: StreamId) -> bool {
        (id & 1 == 0) == self.is_client
    }

    fn send_limit(&self, id: StreamId) -> u64 {
        match (is_uni(id), self.is_local(id)) {
            (true, _) => self.peer.max_stream_data_uni,
            (false, true) => self.peer.max_stream_data_bidi_remote,
            (false, false) => self.peer.max_stream_data_bidi_local,
        }
    }

    fn find(&self, id: StreamId) -> Option<usize> {
        self.ids.iter().position(|&x| x == id)
    }

    fn slot(&self, i: usize) -> Option<&Slot<S, C>> {
        self.slots.get(i)
    }

    fn refresh(&mut self, i: usize) {
        let Some(slot) = self.slots.get(i) else { return };
        let (retx, new) = slot.send.wants();
        let ctl = (slot.recv.win.pending && slot.recv.open)
            || slot.recv.stop_pending.is_some()
            || slot.send.control_pending();
        let hot = (u8::from(retx) * HOT_RETX) | (u8::from(new) * HOT_NEW) | (u8::from(ctl) * HOT_CTL);
        if let Some(h) = self.hot.get_mut(i) {
            *h = hot;
        }
    }

    /// Refresh the slot, and free it when both halves are done.
    fn settle(&mut self, pool: &mut BufferPool<'_>, i: usize) {
        let done = self.slots.get(i).is_some_and(|s| s.recv.is_done() && s.send.is_done());
        if !done {
            self.refresh(i);
            return;
        }
        let id = self.ids.get(i).copied().unwrap_or(NONE);
        if let Some(slot) = self.slots.get_mut(i) {
            slot.recv.release_all(pool);
            slot.send.release_all(pool);
            *slot = Slot::NEW;
        }
        if let Some(x) = self.ids.get_mut(i) {
            *x = NONE;
        }
        if let Some(h) = self.hot.get_mut(i) {
            *h = 0;
        }
        self.open = self.open.saturating_sub(1);
        if id != NONE && !self.is_local(id) {
            let c = class(id);
            if let (Some(limit), Some(pending)) = (self.remote_limit.get_mut(c), self.max_streams_pending.get_mut(c)) {
                *limit += 1;
                *pending = true;
            }
        }
    }

    fn alloc_slot(&mut self, id: StreamId) -> Result<usize, StreamError> {
        let i = self.find(NONE).ok_or(StreamError::TableFull)?;
        let local = self.is_local(id);
        let limit = self.send_limit(id);
        let (window, max) = (self.stream_window, self.max_stream_window);
        let slot = self.slots.get_mut(i).ok_or(StreamError::TableFull)?;
        if !is_uni(id) || !local {
            slot.recv.init(window, max);
        }
        if !is_uni(id) || local {
            slot.send.init(limit);
        }
        if let Some(x) = self.ids.get_mut(i) {
            *x = id;
        }
        self.open += 1;
        self.refresh(i);
        Ok(i)
    }

    /// The slot of `id`, opening peer streams implicitly; `None` if it was already closed.
    fn locate(&mut self, id: StreamId) -> Result<Option<usize>, StreamError> {
        let (c, index) = (class(id), id >> 2);
        if self.is_local(id) {
            if index >= self.local_opened.get(c).copied().unwrap_or(0) {
                return Err(StreamError::StreamState);
            }
            return Ok(self.find(id));
        }
        let next = self.remote_next.get(c).copied().unwrap_or(0);
        if index < next {
            return Ok(self.find(id));
        }
        if index >= self.remote_limit.get(c).copied().unwrap_or(0) {
            return Err(StreamError::StreamLimit);
        }
        let mut last = None;
        for n in next..=index {
            let low = (n << 2) | (id & 3);
            last = Some(self.alloc_slot(low)?);
            if let Some(r) = self.remote_next.get_mut(c) {
                *r = n + 1;
            }
        }
        Ok(last)
    }

    fn require(&self, id: StreamId) -> Result<usize, StreamError> {
        self.find(id).ok_or(StreamError::UnknownStream)
    }

    /// Open a stream we initiate.
    ///
    /// # Errors
    /// [`StreamError::StreamLimit`] at the peer's limit (a STREAMS_BLOCKED is queued), [`StreamError::TableFull`] when
    /// the table has no slot.
    pub fn open_stream(&mut self, bidi: bool) -> Result<StreamId, StreamError> {
        let c = usize::from(!bidi);
        let opened = self.local_opened.get(c).copied().unwrap_or(0);
        let limit = self.open_limit.get(c).copied().unwrap_or(0);
        if opened >= limit {
            if self.blocked_sent.get(c).copied().flatten() != Some(limit)
                && let Some(p) = self.blocked_pending.get_mut(c)
            {
                *p = true;
            }
            return Err(StreamError::StreamLimit);
        }
        let id = (opened << 2) | if bidi { 0 } else { 2 } | u64::from(!self.is_client);
        self.alloc_slot(id)?;
        if let Some(o) = self.local_opened.get_mut(c) {
            *o += 1;
        }
        Ok(id)
    }

    // ---- receive ----------------------------------------------------------------------------------------------

    /// A STREAM frame arrived.
    ///
    /// # Errors
    /// A protocol violation ([`StreamError::StreamLimit`], [`StreamError::StreamState`], [`StreamError::FlowControl`],
    /// [`StreamError::FinalSize`], [`StreamError::Conflict`]) or a local shortage ([`StreamError::Exhausted`],
    /// [`StreamError::Fragmented`], [`StreamError::TableFull`]); on a local shortage nothing was stored.
    pub fn on_stream_frame(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        offset: u64,
        data: &[u8],
        fin: bool,
    ) -> Result<(), StreamError> {
        if is_uni(id) && self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(id)? else { return Ok(()) };
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.recv.on_data(pool, &mut self.conn_recv, offset, data, fin);
        self.settle(pool, i);
        result
    }

    /// A RESET_STREAM frame arrived.
    ///
    /// # Errors
    /// As [`Streams::on_stream_frame`].
    pub fn on_reset_stream(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        error_code: u64,
        final_size: u64,
    ) -> Result<(), StreamError> {
        if is_uni(id) && self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(id)? else { return Ok(()) };
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.recv.on_reset(pool, &mut self.conn_recv, error_code, final_size);
        self.settle(pool, i);
        result
    }

    /// The contiguous readable bytes of a stream (up to the end of one chunk), borrowed from the pool.
    pub fn read_chunk<'a>(&self, pool: &'a BufferPool<'_>, id: StreamId) -> Option<&'a [u8]> {
        self.slot(self.find(id)?)?.recv.read_chunk(pool)
    }

    /// Release `n` readable bytes of a stream, freeing the chunks they filled and crediting the peer. `now` and `srtt`
    /// are the monotonic time and smoothed round trip in the same unit; they drive window autotuning. Consuming zero
    /// bytes after the end (or a reset) was seen lets the stream close.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], or [`StreamError::InvalidConsume`] if `n` exceeds the readable bytes.
    pub fn consume(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        n: usize,
        now: u64,
        srtt: u64,
    ) -> Result<RecvStatus, StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let tune: Option<Tune> = Some((now, srtt));
        slot.recv.consume(pool, &mut self.conn_recv, n as u64, tune)?;
        let status = slot.recv.status();
        self.settle(pool, i);
        Ok(status)
    }

    /// The state of a stream's receive side; `None` if it is unknown or closed.
    pub fn recv_status(&self, id: StreamId) -> Option<RecvStatus> {
        Some(self.slot(self.find(id)?)?.recv.status())
    }

    /// Ask the peer to stop sending on a stream and discard what it still sends.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`] or [`StreamError::StreamState`] for a send-only stream.
    pub fn stop_sending(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        error_code: u64,
    ) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        if !slot.recv.open {
            return Err(StreamError::StreamState);
        }
        slot.recv.stop(pool, &mut self.conn_recv, error_code);
        self.settle(pool, i);
        Ok(())
    }

    // ---- frames from the peer that move limits -----------------------------------------------------------------

    /// MAX_DATA arrived.
    pub fn on_max_data(&mut self, max: u64) {
        self.conn_send.limit = self.conn_send.limit.max(max);
        for i in 0..N {
            self.refresh(i);
        }
    }

    /// MAX_STREAM_DATA arrived.
    ///
    /// # Errors
    /// [`StreamError::StreamState`] for a stream we cannot send on or never opened.
    pub fn on_max_stream_data(&mut self, id: StreamId, max: u64) -> Result<(), StreamError> {
        if is_uni(id) && !self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(id)? else { return Ok(()) };
        if let Some(slot) = self.slots.get_mut(i) {
            slot.send.raise_limit(max);
        }
        self.refresh(i);
        Ok(())
    }

    /// MAX_STREAMS arrived.
    pub fn on_max_streams(&mut self, bidi: bool, max: u64) {
        if let Some(v) = self.open_limit.get_mut(usize::from(!bidi)) {
            *v = (*v).max(max);
        }
    }

    /// DATA_BLOCKED arrived: the peer is out of credit, so send the current limit again.
    pub fn on_data_blocked(&mut self, _limit: u64) {
        self.conn_recv.win.pending = true;
    }

    /// STREAM_DATA_BLOCKED arrived.
    ///
    /// # Errors
    /// [`StreamError::StreamState`] for a stream we cannot receive on or never opened.
    pub fn on_stream_data_blocked(&mut self, id: StreamId, _limit: u64) -> Result<(), StreamError> {
        if is_uni(id) && self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(id)? else { return Ok(()) };
        if let Some(slot) = self.slots.get_mut(i) {
            slot.recv.win.pending = true;
        }
        self.refresh(i);
        Ok(())
    }

    /// STREAMS_BLOCKED arrived: send the current stream-count limit again.
    pub fn on_streams_blocked(&mut self, bidi: bool, _limit: u64) {
        if let Some(p) = self.max_streams_pending.get_mut(usize::from(!bidi)) {
            *p = true;
        }
    }

    /// STOP_SENDING arrived: abandon the send side with the same code.
    ///
    /// # Errors
    /// [`StreamError::StreamState`] for a stream we cannot send on or never opened.
    pub fn on_stop_sending(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        error_code: u64,
    ) -> Result<(), StreamError> {
        if is_uni(id) && !self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(id)? else { return Ok(()) };
        if let Some(slot) = self.slots.get_mut(i) {
            slot.send.reset(pool, error_code)?;
        }
        self.settle(pool, i);
        Ok(())
    }

    // ---- send ---------------------------------------------------------------------------------------------------

    /// Buffer up to `data.len()` bytes for sending (one copy into pool chunks); returns how many were accepted. Zero
    /// means the peer's credit, the pool or the stream's buffer is full; a BLOCKED frame is queued when credit ran out.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], [`StreamError::StreamState`], [`StreamError::WrongKind`] on a source-backed
    /// stream, [`StreamError::Finished`] after `finish` or `reset`.
    pub fn write(&mut self, pool: &mut BufferPool<'_>, id: StreamId, data: &[u8]) -> Result<usize, StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.send.write(pool, &mut self.conn_send, data);
        self.refresh(i);
        result
    }

    /// Back a stream with application storage of `len_hint` bytes: nothing is buffered, bytes are read from `source`
    /// when a frame is built and again when a range is lost, and the end is sent after byte `len_hint`.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], [`StreamError::StreamState`], [`StreamError::WrongKind`] if data was already
    /// written or a source set.
    pub fn open_source(&mut self, id: StreamId, source: S, len_hint: u64) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.send.open_source(source, len_hint);
        self.refresh(i);
        result
    }

    /// End a buffered stream after the bytes written so far.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], [`StreamError::StreamState`], [`StreamError::WrongKind`], [`StreamError::Finished`].
    pub fn finish(&mut self, id: StreamId) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.send.finish();
        self.refresh(i);
        result
    }

    /// Abandon the send side: drop its buffers and queue a RESET_STREAM.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`] or [`StreamError::StreamState`] for a receive-only stream.
    pub fn reset(&mut self, pool: &mut BufferPool<'_>, id: StreamId, error_code: u64) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.send.reset(pool, error_code);
        self.settle(pool, i);
        result
    }

    /// The next stream frame of at most `budget` data bytes: retransmissions first (lowest hole first), then new data,
    /// round-robin over the streams. Copy its data with [`Streams::copy_out`].
    pub fn next_stream_frame(&mut self, budget: usize) -> Option<StreamChunk> {
        for (flag, retx) in [(HOT_RETX, true), (HOT_NEW, false)] {
            for step in 0..N {
                let i = (self.rr + step) % N;
                if self.hot.get(i).is_none_or(|h| h & flag == 0) {
                    continue;
                }
                let id = self.ids.get(i).copied().unwrap_or(NONE);
                let frame = self
                    .slots
                    .get_mut(i)
                    .and_then(|slot| slot.send.next_frame(id, retx, budget, &mut self.conn_send));
                self.refresh(i);
                if frame.is_some() {
                    self.rr = (i + 1) % N;
                    return frame;
                }
            }
        }
        None
    }

    /// Copy the data of a frame returned by [`Streams::next_stream_frame`] into `dst`; returns its length.
    ///
    /// # Errors
    /// [`StreamError::BufferTooSmall`], or [`StreamError::DataUnavailable`] if a source returned fewer bytes than asked
    /// (the range is queued again).
    pub fn copy_out(
        &mut self,
        pool: &BufferPool<'_>,
        chunk: &StreamChunk,
        dst: &mut [u8],
    ) -> Result<usize, StreamError> {
        let i = self.require(chunk.id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.send.copy_out(pool, chunk, dst);
        self.refresh(i);
        result
    }

    // ---- feedback from recovery ---------------------------------------------------------------------------------

    /// The frame was acknowledged: free the bytes it covered.
    pub fn on_acked(&mut self, pool: &mut BufferPool<'_>, id: StreamId, offset: u64, len: u64, fin: bool) {
        if let Some(i) = self.find(id) {
            let overflows = self
                .slots
                .get_mut(i)
                .map_or(0, |s| s.send.on_acked(pool, offset, len, fin));
            self.stats.range_overflows += overflows as u64;
            self.settle(pool, i);
        }
    }

    /// The frame was declared lost: queue its range again, lowest first.
    pub fn on_lost(&mut self, id: StreamId, offset: u64, len: u64, fin: bool) {
        if let Some(i) = self.find(id) {
            let overflows = self.slots.get_mut(i).map_or(0, |s| s.send.on_lost(offset, len, fin));
            self.stats.range_overflows += overflows as u64;
            self.refresh(i);
        }
    }

    /// A frame declared lost was acknowledged after all: cancel its queued retransmission. This is the same operation
    /// as [`Streams::on_acked`], which also removes the range from the retransmission queue.
    pub fn on_late_acked(&mut self, pool: &mut BufferPool<'_>, id: StreamId, offset: u64, len: u64, fin: bool) {
        self.on_acked(pool, id, offset, len, fin);
    }

    /// A control frame from [`Streams::pending_control`] was declared lost (or could not be sent): queue it again unless
    /// it was superseded.
    pub fn on_control_lost(&mut self, frame: &ControlFrame) {
        match *frame {
            ControlFrame::MaxData(v) if v >= self.conn_recv.win.limit => self.conn_recv.win.pending = true,
            ControlFrame::DataBlocked(l) => self.conn_send.requeue_blocked(l),
            ControlFrame::MaxStreams { bidi, max } => {
                let c = usize::from(!bidi);
                if max >= self.remote_limit.get(c).copied().unwrap_or(0)
                    && let Some(p) = self.max_streams_pending.get_mut(c)
                {
                    *p = true;
                }
            }
            ControlFrame::StreamsBlocked { bidi, limit } => {
                let c = usize::from(!bidi);
                if limit == self.open_limit.get(c).copied().unwrap_or(0)
                    && let (Some(p), Some(s)) = (self.blocked_pending.get_mut(c), self.blocked_sent.get_mut(c))
                {
                    *p = true;
                    *s = None;
                }
            }
            ControlFrame::MaxStreamData { id, max } => {
                if let Some(i) = self.find(id) {
                    if let Some(slot) = self.slots.get_mut(i)
                        && max >= slot.recv.win.limit
                    {
                        slot.recv.win.pending = true;
                    }
                    self.refresh(i);
                }
            }
            ControlFrame::StopSending { id, error_code } => {
                if let Some(i) = self.find(id) {
                    if let Some(slot) = self.slots.get_mut(i) {
                        slot.recv.requeue_stop(error_code);
                    }
                    self.refresh(i);
                }
            }
            ControlFrame::StreamDataBlocked { id, .. } | ControlFrame::ResetStream { id, .. } => {
                if let Some(i) = self.find(id) {
                    if let Some(slot) = self.slots.get_mut(i) {
                        slot.send.control_lost(frame);
                    }
                    self.refresh(i);
                }
            }
            ControlFrame::MaxData(_) => {}
        }
    }

    /// A control frame was acknowledged. Only a RESET_STREAM matters: the stream may close once it is acknowledged.
    pub fn on_control_acked(&mut self, pool: &mut BufferPool<'_>, frame: &ControlFrame) {
        if let ControlFrame::ResetStream { id, .. } = *frame
            && let Some(i) = self.find(id)
        {
            if let Some(slot) = self.slots.get_mut(i) {
                slot.send.reset_acked();
            }
            self.settle(pool, i);
        }
    }

    /// The next control frame to send, if any. The frame counts as sent; if it is not sent after all, give it back
    /// with [`Streams::on_control_lost`].
    pub fn pending_control(&mut self) -> Option<ControlFrame> {
        if self.conn_recv.win.pending {
            self.conn_recv.win.pending = false;
            return Some(ControlFrame::MaxData(self.conn_recv.win.limit));
        }
        if self.conn_send.blocked_pending {
            return Some(ControlFrame::DataBlocked(self.conn_send.take_blocked()));
        }
        for c in 0..2 {
            let bidi = c == 0;
            if self.max_streams_pending.get(c).copied().unwrap_or(false) {
                if let Some(p) = self.max_streams_pending.get_mut(c) {
                    *p = false;
                }
                let max = self.remote_limit.get(c).copied().unwrap_or(0);
                return Some(ControlFrame::MaxStreams { bidi, max });
            }
            if self.blocked_pending.get(c).copied().unwrap_or(false) {
                let limit = self.open_limit.get(c).copied().unwrap_or(0);
                if let (Some(p), Some(s)) = (self.blocked_pending.get_mut(c), self.blocked_sent.get_mut(c)) {
                    *p = false;
                    *s = Some(limit);
                }
                return Some(ControlFrame::StreamsBlocked { bidi, limit });
            }
        }
        for i in 0..N {
            if self.hot.get(i).is_none_or(|h| h & HOT_CTL == 0) {
                continue;
            }
            let id = self.ids.get(i).copied().unwrap_or(NONE);
            let frame = self.slots.get_mut(i).and_then(|slot| {
                if let Some(f) = slot.send.take_control(id) {
                    return Some(f);
                }
                if let Some(error_code) = slot.recv.stop_pending.take() {
                    return Some(ControlFrame::StopSending { id, error_code });
                }
                if slot.recv.win.pending {
                    slot.recv.win.pending = false;
                    return Some(ControlFrame::MaxStreamData {
                        id,
                        max: slot.recv.win.limit,
                    });
                }
                None
            });
            self.refresh(i);
            if frame.is_some() {
                return frame;
            }
        }
        None
    }

    /// Close every stream and return all their chunks to the pool (the connection is going away).
    pub fn close_all(&mut self, pool: &mut BufferPool<'_>) {
        for i in 0..N {
            if let Some(slot) = self.slots.get_mut(i) {
                slot.recv.release_all(pool);
                slot.send.release_all(pool);
                *slot = Slot::NEW;
            }
            if let Some(x) = self.ids.get_mut(i) {
                *x = NONE;
            }
            if let Some(h) = self.hot.get_mut(i) {
                *h = 0;
            }
        }
        self.open = 0;
    }
}
