//! The stream table: ids, limits, the control-frame queue and the glue between the halves of each stream.
//!
//! Invariants: `ids[i]` is the id held by slot `i` (or `NONE`) and `hot[i]` is a superset of what slot `i` can emit
//! (a stale bit costs one failed attempt, a missing bit would starve the slot, so every mutator refreshes it); a slot
//! is freed only when both halves are done, which returns all of its chunks to the pool; `buffered` is the sum over
//! slots of the written-and-unacknowledged bytes; `local_live` and `remote_live` count the live streams each side
//! opened; a refused peer stream is remembered in `refused` until its reset is acknowledged and is never stored;
//! stream ids of a class are opened in order and never reused.

use super::flow::Meter;
use super::pool::{BufferPool, CHUNK_SIZE};
use super::recv::Recv;
use super::send::Send;
use super::{
    BUSY, Config, ControlFrame, DEFAULT_URGENCY, NoSource, PeerLimits, RecvStatus, StreamChunk, StreamError, StreamId,
    StreamSource, StreamStats, is_uni,
};

const NONE: u64 = u64::MAX;
const HOT_RETX: u8 = 1;
const HOT_NEW: u8 = 2;
const HOT_CTL: u8 = 4;
/// How many refused peer streams are remembered until their reset is acknowledged.
const REFUSED: usize = 16;

#[derive(Debug)]
struct Slot<S, const C: usize> {
    recv: Recv<C>,
    send: Send<S, C>,
    urgency: u8,
}

impl<S: StreamSource, const C: usize> Slot<S, C> {
    const NEW: Self = Self {
        recv: Recv::NEW,
        send: Send::NEW,
        urgency: DEFAULT_URGENCY,
    };
}

/// A refused peer stream waiting for its reset to be sent and acknowledged.
#[derive(Debug, Clone, Copy)]
struct Refused {
    id: StreamId,
    sent: bool,
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
    stream_window: u64,
    max_stream_window: u64,
    target: u64,
    meter: Meter,
    peer: PeerLimits,
    max_remote: u64,
    local_opened: [u64; 2],
    remote_next: [u64; 2],
    local_live: u64,
    remote_live: u64,
    refused: [Option<Refused>; REFUSED],
    open: usize,
    buffered: u64,
    stats: StreamStats,
}

impl<S: StreamSource, const N: usize, const C: usize> Streams<S, N, C> {
    /// A table for `config`. The window ceiling is clamped to what the chunk rings and half of the pool's budget can
    /// hold, and the peer-opened stream cap to the table size.
    pub fn new(config: &Config, pool: &BufferPool<'_>) -> Self {
        const { assert!(C >= 2 && N >= 1) };
        let chunk = CHUNK_SIZE as u64;
        let half = pool.budget_bytes() / 2 / chunk * chunk;
        let max_stream = config.max_stream_window.min((C as u64 - 1) * chunk).min(half);
        let stream_window = config.initial_stream_window.min(max_stream);
        let mut streams = Self {
            is_client: config.is_client,
            ids: [NONE; N],
            hot: [0; N],
            slots: [const { Slot::NEW }; N],
            stream_window,
            max_stream_window: max_stream,
            target: stream_window,
            meter: Meter::NEW,
            peer: PeerLimits::default(),
            max_remote: config.max_streams.min(N as u64),
            local_opened: [0; 2],
            remote_next: [0; 2],
            local_live: 0,
            remote_live: 0,
            refused: [None; REFUSED],
            open: 0,
            buffered: 0,
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

    /// The initial receive window of a stream, which the connection advertises.
    pub const fn recv_window(&self) -> u64 {
        self.stream_window
    }

    /// The receive window size and advertised limit of a stream.
    pub fn stream_recv_window(&self, id: StreamId) -> Option<(u64, u64)> {
        let win = &self.slot(self.find(id)?)?.recv.win;
        Some((win.size, win.limit))
    }

    /// The receive credit granted to the peer and not yet received, summed over the open streams. It is recomputed by
    /// a scan of the table.
    pub fn granted_unreceived(&self) -> u64 {
        self.slots
            .iter()
            .fold(0, |sum, s| sum.saturating_add(s.recv.unreceived()))
    }

    /// The bytes written and not yet acknowledged, over all buffered streams.
    pub const fn buffered(&self) -> u64 {
        self.buffered
    }

    /// Apply the peer's limits (its credit record, or later raises). Limits only grow.
    pub fn set_peer_limits(&mut self, limits: &PeerLimits) {
        self.peer.window = self.peer.window.max(limits.window);
        self.peer.max_streams = self.peer.max_streams.max(limits.max_streams);
        let window = self.peer.window;
        for slot in &mut self.slots {
            if slot.send.open {
                slot.send.raise_limit(window);
            }
        }
        for i in 0..N {
            self.refresh(i);
        }
    }

    fn is_local(&self, id: StreamId) -> bool {
        (id & 1 == 0) == self.is_client
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
        let ctl = (slot.recv.win.pending && slot.recv.open) || slot.send.control_pending();
        let hot = (u8::from(retx) * HOT_RETX) | (u8::from(new) * HOT_NEW) | (u8::from(ctl) * HOT_CTL);
        if let Some(h) = self.hot.get_mut(i) {
            *h = hot;
        }
    }

    /// Run `f` on the send half of slot `i`, keeping the `buffered` counter in step with what it did.
    fn with_send<R>(&mut self, i: usize, f: impl FnOnce(&mut Send<S, C>) -> R) -> Option<R> {
        let slot = self.slots.get_mut(i)?;
        let before = slot.send.buffered();
        let out = f(&mut slot.send);
        let after = slot.send.buffered();
        self.buffered = self.buffered.saturating_add(after).saturating_sub(before);
        Some(out)
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
            self.buffered = self.buffered.saturating_sub(slot.send.buffered());
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
        if id != NONE {
            let live = if self.is_local(id) {
                &mut self.local_live
            } else {
                &mut self.remote_live
            };
            *live = live.saturating_sub(1);
        }
    }

    fn alloc_slot(&mut self, id: StreamId) -> Result<usize, StreamError> {
        let i = self.find(NONE).ok_or(StreamError::TableFull)?;
        let local = self.is_local(id);
        let (window, limit) = (self.stream_window, self.peer.window);
        let slot = self.slots.get_mut(i).ok_or(StreamError::TableFull)?;
        if !is_uni(id) || !local {
            slot.recv.init(window);
        }
        if !is_uni(id) || local {
            slot.send.init(limit);
        }
        if let Some(x) = self.ids.get_mut(i) {
            *x = id;
        }
        self.open += 1;
        if local {
            self.local_live += 1;
        } else {
            self.remote_live += 1;
        }
        self.refresh(i);
        Ok(i)
    }

    /// Remember `id` as refused so a reset answers it; nothing of the stream is stored.
    fn refuse(&mut self, id: StreamId) -> Result<Option<usize>, StreamError> {
        let entry = self
            .refused
            .iter_mut()
            .find(|e| e.is_none())
            .ok_or(StreamError::Exhausted)?;
        *entry = Some(Refused { id, sent: false });
        Err(StreamError::Busy)
    }

    /// Whether `count` more peer streams of class `c` starting at index `next` can be admitted: under the cap, with
    /// slots, with their initial windows covered by the pool, and without passing a stream still being refused.
    fn admits(&self, pool: &BufferPool<'_>, c: usize, next: u64, count: u64) -> bool {
        let free = self.ids.iter().filter(|&&x| x == NONE).count() as u64;
        let window = count.saturating_mul(self.stream_window);
        let behind_refused = self
            .refused
            .iter()
            .flatten()
            .any(|r| class(r.id) == c && (r.id >> 2) >= next && (r.id >> 2) < next + count);
        !behind_refused
            && self.remote_live + count <= self.max_remote
            && free >= count
            && self.granted_unreceived().saturating_add(window) <= pool.available_bytes()
    }

    /// The slot of `id`, opening peer streams implicitly; `None` if it was already closed.
    fn locate(&mut self, pool: &BufferPool<'_>, id: StreamId) -> Result<Option<usize>, StreamError> {
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
        if self.refused.iter().flatten().any(|r| r.id == id) {
            return Err(StreamError::Busy);
        }
        if index >= next.saturating_add(self.max_remote) {
            return Err(StreamError::StreamLimit);
        }
        if !self.admits(pool, c, next, index - next + 1) {
            return self.refuse(id);
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
    /// [`StreamError::StreamLimit`] when the live streams we opened are already as many as the peer allows,
    /// [`StreamError::TableFull`] when the table has no slot.
    pub fn open_stream(&mut self, bidi: bool) -> Result<StreamId, StreamError> {
        if self.local_live >= self.peer.max_streams {
            return Err(StreamError::StreamLimit);
        }
        let c = usize::from(!bidi);
        let opened = self.local_opened.get(c).copied().unwrap_or(0);
        let id = (opened << 2) | if bidi { 0 } else { 2 } | u64::from(!self.is_client);
        self.alloc_slot(id)?;
        if let Some(o) = self.local_opened.get_mut(c) {
            *o += 1;
        }
        Ok(id)
    }

    /// Set the urgency of a stream; a lower number is served first (the default is [`DEFAULT_URGENCY`]).
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`].
    pub fn set_urgency(&mut self, id: StreamId, urgency: u8) -> Result<(), StreamError> {
        let i = self.require(id)?;
        self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?.urgency = urgency;
        Ok(())
    }

    // ---- receive ----------------------------------------------------------------------------------------------

    /// A stream data frame arrived.
    ///
    /// # Errors
    /// A violation by the peer ([`StreamError::StreamLimit`], [`StreamError::StreamState`], [`StreamError::FlowControl`],
    /// [`StreamError::FinalSize`], [`StreamError::Conflict`]), a refused stream ([`StreamError::Busy`]: a reset answers
    /// it, nothing was stored) or a local shortage ([`StreamError::Exhausted`], [`StreamError::Fragmented`]); on a
    /// local shortage nothing was stored and the packet should go unacknowledged.
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
        let Some(i) = self.locate(pool, id)? else { return Ok(()) };
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.recv.on_data(pool, offset, data, fin);
        self.settle(pool, i);
        result
    }

    /// A stream reset frame arrived.
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
        let Some(i) = self.locate(pool, id)? else { return Ok(()) };
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.recv.on_reset(pool, error_code, final_size);
        self.settle(pool, i);
        result
    }

    /// The contiguous readable bytes of a stream (up to the end of one chunk), borrowed from the pool.
    pub fn read_chunk<'a>(&self, pool: &'a BufferPool<'_>, id: StreamId) -> Option<&'a [u8]> {
        self.slot(self.find(id)?)?.recv.read_chunk(pool)
    }

    /// Release `n` readable bytes of a stream, freeing the chunks they filled and moving the peer's window forward.
    /// `now` and `srtt` are the monotonic time and smoothed round trip in the same unit; they feed the delivery-rate
    /// meter that sizes the windows. Consuming zero bytes after the end (or a reset) was seen lets the stream close.
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
        slot.recv.consume(pool, n as u64)?;
        let status = slot.recv.status();
        let rate = self.meter.consumed(n as u64, now, srtt);
        self.target = rate
            .saturating_mul(2)
            .max(self.stream_window)
            .min(self.max_stream_window);
        self.grant(pool, i);
        self.settle(pool, i);
        Ok(status)
    }

    /// Move the window of slot `first`, and of every slot whose grant was deferred, to the current target. A grant is
    /// queued only while the credit already granted and not yet received, plus the increase, fits in the pool;
    /// otherwise the slot stays deferred and is tried again after a later consume.
    fn grant(&mut self, pool: &BufferPool<'_>, first: usize) {
        let mut granted: Option<u64> = None;
        for i in 0..N {
            let target = self.target;
            let Some(slot) = self.slots.get_mut(i) else { continue };
            if !slot.recv.open || !(i == first || slot.recv.win.deferred) {
                continue;
            }
            slot.recv.win.size = slot.recv.win.size.max(target);
            let Some((candidate, increase)) = slot.recv.due() else {
                slot.recv.win.deferred = false;
                continue;
            };
            let sum = *granted.get_or_insert_with(|| self.granted_unreceived());
            let Some(slot) = self.slots.get_mut(i) else { continue };
            if sum.saturating_add(increase) <= pool.available_bytes() {
                slot.recv.win.limit = candidate;
                slot.recv.win.pending = true;
                slot.recv.win.deferred = false;
                granted = Some(sum + increase);
            } else {
                slot.recv.win.deferred = true;
            }
            self.refresh(i);
        }
    }

    /// Whether the bytes `offset..offset + len` of a stream are acknowledged (an empty range asks about the end
    /// marker). A stream that is gone counts as acknowledged.
    pub fn is_acked(&self, id: StreamId, offset: u64, len: u64) -> bool {
        self.find(id)
            .and_then(|i| self.slot(i))
            .is_none_or(|s| s.send.is_acked(offset, len))
    }

    /// Whether a stream sends from application storage instead of a buffer.
    pub fn is_source(&self, id: StreamId) -> bool {
        self.find(id)
            .and_then(|i| self.slot(i))
            .is_some_and(|s| s.send.is_source())
    }

    /// The state of a stream's receive side; `None` if it is unknown or closed.
    pub fn recv_status(&self, id: StreamId) -> Option<RecvStatus> {
        Some(self.slot(self.find(id)?)?.recv.status())
    }

    // ---- frames from the peer that move limits -----------------------------------------------------------------

    /// A send limit update for a stream arrived.
    ///
    /// # Errors
    /// [`StreamError::StreamState`] for a stream we cannot send on or never opened; the errors of opening a peer
    /// stream as in [`Streams::on_stream_frame`].
    pub fn on_max_stream_data(&mut self, pool: &BufferPool<'_>, id: StreamId, max: u64) -> Result<(), StreamError> {
        if is_uni(id) && !self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(pool, id)? else { return Ok(()) };
        if let Some(slot) = self.slots.get_mut(i) {
            slot.send.raise_limit(max);
        }
        self.refresh(i);
        Ok(())
    }

    // ---- send ---------------------------------------------------------------------------------------------------

    /// Buffer up to `data.len()` bytes for sending (one copy into pool chunks); returns how many were accepted. The
    /// write is bounded by the stream's send window, the ring, the pool and `buffer_cap - buffered()`, the room the
    /// connection leaves in its send buffer. Zero means one of those is full; a write cut short by the cap is woken
    /// through [`Streams::poll_writable`], one cut by the window by the next window update.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], [`StreamError::StreamState`], [`StreamError::WrongKind`] on a source-backed
    /// stream, [`StreamError::Finished`] after `finish` or `reset`.
    pub fn write(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        data: &[u8],
        buffer_cap: u64,
    ) -> Result<usize, StreamError> {
        let i = self.require(id)?;
        let room = buffer_cap.saturating_sub(self.buffered);
        let result = self
            .with_send(i, |send| send.write(pool, data, room))
            .unwrap_or(Err(StreamError::UnknownStream));
        self.refresh(i);
        result
    }

    /// A stream whose write was cut short by the send buffer cap, once `buffered() < buffer_cap`; one stream per call,
    /// and its mark is cleared.
    pub fn poll_writable(&mut self, buffer_cap: u64) -> Option<StreamId> {
        if self.buffered >= buffer_cap {
            return None;
        }
        let i = self.slots.iter().position(|s| s.send.cap_cut)?;
        if let Some(slot) = self.slots.get_mut(i) {
            slot.send.cap_cut = false;
        }
        self.ids.get(i).copied()
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

    /// Abandon the send side: drop its buffers and queue a stream reset.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`] or [`StreamError::StreamState`] for a receive-only stream.
    pub fn reset(&mut self, pool: &mut BufferPool<'_>, id: StreamId, error_code: u64) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let result = self
            .with_send(i, |send| send.reset(pool, error_code))
            .unwrap_or(Err(StreamError::UnknownStream));
        self.settle(pool, i);
        result
    }

    /// The slot after `floor` in (urgency, id) order that has a frame to send, with its key.
    fn next_hot(&self, floor: Option<(u8, u64)>) -> Option<((u8, u64), usize)> {
        (0..N)
            .filter(|&i| self.hot.get(i).is_some_and(|h| h & (HOT_RETX | HOT_NEW) != 0))
            .filter_map(|i| {
                let key = (self.slots.get(i)?.urgency, self.ids.get(i).copied()?);
                floor.is_none_or(|f| key > f).then_some((key, i))
            })
            .min()
    }

    /// The next stream frame of at most `budget` data bytes: the first stream in (urgency, id) order that has anything
    /// to send, its retransmissions first (lowest hole first), then new data. A better stream drains before a worse
    /// one gets anything. Copy its data with [`Streams::copy_out`].
    pub fn next_stream_frame(&mut self, budget: usize) -> Option<StreamChunk> {
        let mut floor = None;
        while let Some((key, i)) = self.next_hot(floor) {
            let frame = self.slots.get_mut(i).and_then(|slot| {
                slot.send
                    .next_frame(key.1, true, budget)
                    .or_else(|| slot.send.next_frame(key.1, false, budget))
            });
            self.refresh(i);
            if frame.is_some() {
                return frame;
            }
            floor = Some(key);
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
                .with_send(i, |send| send.on_acked(pool, offset, len, fin))
                .unwrap_or(0);
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
            ControlFrame::ResetStream { id, .. } => {
                if let Some(r) = self.refused.iter_mut().flatten().find(|r| r.id == id) {
                    r.sent = false;
                } else if let Some(i) = self.find(id) {
                    if let Some(slot) = self.slots.get_mut(i) {
                        slot.send.control_lost(frame);
                    }
                    self.refresh(i);
                }
            }
        }
    }

    /// A control frame was acknowledged. Only a stream reset matters: the stream may close once it is acknowledged, and
    /// a refused stream is forgotten.
    pub fn on_control_acked(&mut self, pool: &mut BufferPool<'_>, frame: &ControlFrame) {
        if let ControlFrame::ResetStream { id, .. } = *frame {
            if let Some(e) = self.refused.iter_mut().find(|e| e.is_some_and(|r| r.id == id)) {
                *e = None;
            } else if let Some(i) = self.find(id) {
                if let Some(slot) = self.slots.get_mut(i) {
                    slot.send.reset_acked();
                }
                self.settle(pool, i);
            }
        }
    }

    /// The next control frame to send, if any. The frame counts as sent; if it is not sent after all, give it back
    /// with [`Streams::on_control_lost`].
    pub fn pending_control(&mut self) -> Option<ControlFrame> {
        if let Some(r) = self.refused.iter_mut().flatten().find(|r| !r.sent) {
            r.sent = true;
            return Some(ControlFrame::ResetStream {
                id: r.id,
                error_code: BUSY,
                final_size: 0,
            });
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
        }
        self.ids = [NONE; N];
        self.hot = [0; N];
        self.refused = [None; REFUSED];
        self.open = 0;
        self.buffered = 0;
        self.local_live = 0;
        self.remote_live = 0;
    }
}
