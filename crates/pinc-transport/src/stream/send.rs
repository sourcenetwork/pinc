//! The send half of a stream: buffered or source-backed data, the retransmission queue and the final size.
//!
//! Invariants: `lost` never holds an offset at or beyond `sent_max` and is served lowest first; `acked_prefix` is the
//! end of the acknowledged prefix and a buffered stream holds chunks only from the one containing it; credit is spent
//! once per byte (at write time for buffered streams, at first transmission for source-backed ones) and
//! retransmissions are free; the bytes a buffered stream holds are exactly `written - acked_prefix`.

use super::pool::{BufferPool, CHUNK_SIZE, Ring};
use super::ranges::RangeSet;
use super::{ACKED_RANGES, ControlFrame, MAX_OFFSET, RANGES, StreamChunk, StreamError, StreamId, StreamSource};

/// The end-of-stream marker's life.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fin {
    /// No end set yet.
    None,
    /// To be sent (first time or after a loss).
    Pending,
    Sent,
    Acked,
}

/// A stream reset's life.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reset {
    None,
    Pending { code: u64, final_size: u64 },
    Sent { code: u64, final_size: u64 },
    Acked,
}

#[derive(Debug)]
pub(super) struct Send<S, const C: usize> {
    pub(super) open: bool,
    is_source: bool,
    source: Option<S>,
    ring: Ring<C>,
    written: u64,
    sent_max: u64,
    pub(super) limit: u64,
    lost: RangeSet<RANGES>,
    acked: RangeSet<ACKED_RANGES>,
    acked_prefix: u64,
    final_size: Option<u64>,
    fin: Fin,
    reset: Reset,
    /// A write was cut short by the connection's send buffer cap and the application has not been woken since.
    pub(super) cap_cut: bool,
}

impl<S: StreamSource, const C: usize> Send<S, C> {
    pub(super) const NEW: Self = Self {
        open: false,
        is_source: false,
        source: None,
        ring: Ring::EMPTY,
        written: 0,
        sent_max: 0,
        limit: 0,
        lost: RangeSet::EMPTY,
        acked: RangeSet::EMPTY,
        acked_prefix: 0,
        final_size: None,
        fin: Fin::None,
        reset: Reset::None,
        cap_cut: false,
    };

    pub(super) const fn init(&mut self, limit: u64) {
        self.open = true;
        self.limit = limit;
    }

    /// Credit spent so far.
    const fn used(&self) -> u64 {
        if self.is_source { self.sent_max } else { self.written }
    }

    fn live(&self) -> bool {
        self.open && matches!(self.reset, Reset::None)
    }

    /// Bytes written and not yet acknowledged; they occupy the send buffer.
    pub(super) const fn buffered(&self) -> u64 {
        if self.is_source || !self.open || !matches!(self.reset, Reset::None) {
            0
        } else {
            self.written - self.acked_prefix
        }
    }

    /// Bytes ready to go out for the first time (ignoring credit).
    fn unsent(&self) -> u64 {
        if self.is_source {
            self.final_size.unwrap_or(0).saturating_sub(self.sent_max)
        } else {
            self.written.saturating_sub(self.sent_max)
        }
    }

    pub(super) fn release_all(&mut self, pool: &mut BufferPool<'_>) {
        self.ring.release_all(pool);
    }

    /// Whether the send half is closed or its end and every byte are acknowledged, and the state of its reset
    /// (0 none, 1 pending, 2 sent, 3 acknowledged), and the error code of a reset that is not yet acknowledged.
    #[cfg(feature = "trace")]
    pub(super) fn trace_state(&self) -> (bool, u8, Option<u64>) {
        let fin_done = !self.open || (self.fin == Fin::Acked && self.final_size == Some(self.acked_prefix));
        let (reset, code) = match self.reset {
            Reset::None => (0, None),
            Reset::Pending { code, .. } => (1, Some(code)),
            Reset::Sent { code, .. } => (2, Some(code)),
            Reset::Acked => (3, None),
        };
        (fin_done, reset, code)
    }

    /// The whole state of the half, for trace validation; `ext` is the chunks other users of `pool` hold.
    #[cfg(feature = "trace")]
    pub(super) fn trace_half(&self, pool: &BufferPool<'_>, ext: u64) -> super::trace::SendHalfView {
        let (fin_done, reset, reset_code) = self.trace_state();
        let reset_final = match self.reset {
            Reset::Pending { final_size, .. } | Reset::Sent { final_size, .. } => Some(final_size),
            Reset::None | Reset::Acked => None,
        };
        super::trace::SendHalfView {
            open: self.open,
            is_source: self.is_source,
            has_source: self.source.is_some(),
            written: self.written,
            sent_max: self.sent_max,
            limit: self.limit,
            lost: self.lost.to_vec(),
            acked: self.acked.to_vec(),
            acked_prefix: self.acked_prefix,
            final_size: self.final_size,
            fin: match self.fin {
                Fin::None => 0,
                Fin::Pending => 1,
                Fin::Sent => 2,
                Fin::Acked => 3,
            },
            reset,
            reset_code,
            reset_final,
            cap_cut: self.cap_cut,
            held: self.ring.numbers(self.acked_prefix / CHUNK_SIZE as u64),
            buffered: self.buffered(),
            wants: self.wants(),
            flushed: self.flushed(),
            done: self.is_done(),
            can_stop: self.can_stop(),
            control_pending: self.control_pending(),
            view: self.view(),
            fin_done,
            available: pool.available_chunks() as u64,
            ext,
        }
    }

    /// Nothing more will be sent or retransmitted.
    pub(super) fn is_done(&self) -> bool {
        !self.open
            || matches!(self.reset, Reset::Acked)
            || (self.fin == Fin::Acked && self.final_size == Some(self.acked_prefix))
    }

    /// Whether everything this half will send has left and nothing waits to be sent again: its end or its reset was
    /// sent, and no lost range is queued. Only the acknowledgement is still to come.
    pub(super) fn flushed(&self) -> bool {
        !self.open
            || matches!(self.reset, Reset::Sent { .. } | Reset::Acked)
            || (matches!(self.fin, Fin::Sent | Fin::Acked) && !self.wants().0)
    }

    /// What the host may pace on: how far it sent, the lowest byte waiting to be sent again, and whether it is done.
    pub(super) fn view(&self) -> super::SendView {
        super::SendView {
            sent: self.sent_max,
            lost: self.lost.first().map(|r| r.start),
            done: self.is_done(),
        }
    }

    /// Whether a stop request would reset this half now: it is open and neither reset nor finished with.
    pub(super) fn can_stop(&self) -> bool {
        self.open && matches!(self.reset, Reset::None) && !self.is_done()
    }

    /// Whether a frame is waiting: a retransmission, or the end marker (bit 0), or fresh data (bit 1).
    pub(super) fn wants(&self) -> (bool, bool) {
        if !self.live() {
            return (false, false);
        }
        let fin_only = self.fin == Fin::Pending && self.final_size == Some(self.sent_max);
        let credit = !self.is_source || self.limit > self.sent_max;
        (!self.lost.is_empty() || fin_only, self.unsent() > 0 && credit)
    }

    pub(super) const fn control_pending(&self) -> bool {
        matches!(self.reset, Reset::Pending { .. })
    }

    /// Accept up to `data.len()` bytes into the buffer, bounded by credit, the ring, the pool and `room` (what is left
    /// of the connection's send buffer cap).
    pub(super) fn write(&mut self, pool: &mut BufferPool<'_>, data: &[u8], room: u64) -> Result<usize, StreamError> {
        if !self.open {
            return Err(StreamError::StreamState);
        }
        if self.is_source {
            return Err(StreamError::WrongKind);
        }
        if self.final_size.is_some() || !matches!(self.reset, Reset::None) {
            return Err(StreamError::Finished);
        }
        let want = data.len() as u64;
        let stream_credit = self.limit.saturating_sub(self.written);
        let base = self.acked_prefix / CHUNK_SIZE as u64 * CHUNK_SIZE as u64;
        let ring_room = (base + C as u64 * CHUNK_SIZE as u64).saturating_sub(self.written);
        let tail_room = match self.written % CHUNK_SIZE as u64 {
            0 => 0,
            at => CHUNK_SIZE as u64 - at,
        };
        let pool_room = pool.available_bytes() + tail_room;
        let n = want.min(stream_credit).min(room).min(ring_room).min(pool_room);
        self.cap_cut |= room <= n && room < want;
        let n = n as usize;
        self.ring.write(pool, self.written, data.get(..n).unwrap_or(&[]))?;
        self.written += n as u64;
        Ok(n)
    }

    /// Mark the end of a buffered stream.
    pub(super) fn finish(&mut self) -> Result<(), StreamError> {
        if !self.open {
            return Err(StreamError::StreamState);
        }
        if self.is_source {
            return Err(StreamError::WrongKind);
        }
        if !matches!(self.reset, Reset::None) {
            return Err(StreamError::Finished);
        }
        if self.final_size.is_none() {
            self.final_size = Some(self.written);
            self.fin = Fin::Pending;
        }
        Ok(())
    }

    /// Back the stream with `source` of `len` bytes; the end is sent after the last of them.
    pub(super) fn open_source(&mut self, source: S, len: u64) -> Result<(), StreamError> {
        if !self.open {
            return Err(StreamError::StreamState);
        }
        if self.is_source || self.written > 0 || self.final_size.is_some() {
            return Err(StreamError::WrongKind);
        }
        if len > MAX_OFFSET {
            return Err(StreamError::FlowControl);
        }
        self.is_source = true;
        self.source = Some(source);
        self.final_size = Some(len);
        self.fin = Fin::Pending;
        Ok(())
    }

    /// Abandon the stream: drop the buffers and queue a stream reset.
    pub(super) fn reset(&mut self, pool: &mut BufferPool<'_>, code: u64) -> Result<(), StreamError> {
        if !self.open {
            return Err(StreamError::StreamState);
        }
        if !matches!(self.reset, Reset::None) || self.is_done() {
            return Ok(());
        }
        self.reset = Reset::Pending {
            code,
            final_size: self.used(),
        };
        self.source = None;
        self.lost.clear();
        self.acked.clear();
        self.release_all(pool);
        Ok(())
    }

    /// Whether the bytes `offset..offset + len` (or, for an empty range, the end marker) are acknowledged.
    pub(super) fn is_acked(&self, offset: u64, len: u64) -> bool {
        if len == 0 {
            return self.fin == Fin::Acked;
        }
        self.acked.gaps(offset..offset.saturating_add(len)).next().is_none()
    }

    /// Whether the stream sends from application storage instead of a buffer.
    pub(super) const fn is_source(&self) -> bool {
        self.is_source
    }

    pub(super) fn raise_limit(&mut self, limit: u64) {
        self.limit = self.limit.max(limit);
    }

    /// The next frame: `retx` selects the retransmission pass, otherwise fresh data.
    pub(super) fn next_frame(&mut self, id: StreamId, retx: bool, budget: usize) -> Option<StreamChunk> {
        if !self.live() {
            return None;
        }
        let frame = |offset: u64, len: u64, fin: bool| StreamChunk {
            id,
            offset,
            len: len as usize,
            fin,
        };
        if retx {
            while let Some(r) = self.lost.take_front(budget as u64) {
                let fin = self.fin == Fin::Pending && self.final_size == Some(r.end);
                // The acknowledged prefix is never sent again: its chunks are released.
                let start = self.clip(r.start).min(r.end);
                if start == r.end && !fin {
                    continue;
                }
                if fin {
                    self.fin = Fin::Sent;
                }
                return Some(frame(start, r.end - start, fin));
            }
            if self.lost.is_empty() && self.fin == Fin::Pending && self.final_size == Some(self.sent_max) {
                self.fin = Fin::Sent;
                return Some(frame(self.sent_max, 0, true));
            }
            return None;
        }
        let mut n = self.unsent().min(budget as u64);
        if n == 0 {
            return None;
        }
        if self.is_source {
            n = n.min(self.limit.saturating_sub(self.sent_max));
            if n == 0 {
                return None;
            }
        }
        let offset = self.sent_max;
        self.sent_max += n;
        let fin = self.fin == Fin::Pending && self.final_size == Some(self.sent_max);
        if fin {
            self.fin = Fin::Sent;
        }
        Some(frame(offset, n, fin))
    }

    /// The lowest offset at or after `offset` that is not in the acknowledged prefix, so a range can be cut to the
    /// bytes still held.
    pub(super) fn clip(&self, offset: u64) -> u64 {
        offset.max(self.acked_prefix)
    }

    /// Copy the data of `chunk` into `dst`.
    pub(super) fn copy_out(
        &mut self,
        pool: &BufferPool<'_>,
        chunk: &StreamChunk,
        dst: &mut [u8],
    ) -> Result<usize, StreamError> {
        let out = dst.get_mut(..chunk.len).ok_or(StreamError::BufferTooSmall)?;
        // A released chunk's slot may hold a later chunk's bytes once the ring has wrapped: refuse the copy.
        if self.source.is_none() && chunk.offset / (CHUNK_SIZE as u64) < self.acked_prefix / (CHUNK_SIZE as u64) {
            self.requeue(chunk.offset, chunk.len as u64, chunk.fin);
            return Err(StreamError::DataUnavailable);
        }
        let got = match self.source.as_mut() {
            Some(source) => source.read_at(chunk.offset, out),
            None => self.ring.read(pool, chunk.offset, out),
        };
        if got == chunk.len {
            return Ok(got);
        }
        // The frame cannot be completed: queue its range for another attempt rather than lose it.
        self.requeue(chunk.offset, chunk.len as u64, chunk.fin);
        Err(StreamError::DataUnavailable)
    }

    fn requeue(&mut self, offset: u64, len: u64, fin: bool) -> usize {
        if !self.live() {
            return 0;
        }
        if fin && self.fin != Fin::Acked {
            self.fin = Fin::Pending;
        }
        let range = offset..offset.saturating_add(len).min(self.sent_max);
        let mut widened = 0;
        for gap in self.acked.gaps(range) {
            widened += usize::from(self.lost.insert_widening(gap));
        }
        widened
    }

    /// The range was declared lost. Returns how many range-map overflows were absorbed.
    pub(super) fn on_lost(&mut self, offset: u64, len: u64, fin: bool) -> usize {
        self.requeue(offset, len, fin)
    }

    /// The range was acknowledged (also when it had been declared lost and is still queued). Returns how many
    /// range-map overflows were absorbed.
    pub(super) fn on_acked(&mut self, pool: &mut BufferPool<'_>, offset: u64, len: u64, fin: bool) -> usize {
        if !self.live() {
            return 0;
        }
        let mut overflows = 0;
        if fin {
            self.fin = Fin::Acked;
        }
        let range = offset..offset.saturating_add(len).min(self.sent_max);
        if range.start < range.end {
            if self.acked.insert(range.clone()).is_err() {
                // Too many holes to remember: send it again, so the acknowledgement can be taken in order.
                self.lost.insert_widening(range);
                overflows += 1;
            } else if self.lost.remove(&range).is_err() {
                // The cut would split a full map: the range stays queued and is sent once more, harmlessly.
                overflows += 1;
            }
        }
        let prefix = self.acked.first().filter(|r| r.start == 0).map_or(0, |r| r.end);
        if !self.is_source {
            let old = self.acked_prefix / CHUNK_SIZE as u64;
            for k in old..prefix / CHUNK_SIZE as u64 {
                self.ring.release(pool, k);
            }
        }
        self.acked_prefix = prefix;
        if self.is_done() {
            self.release_all(pool);
        }
        overflows
    }

    /// The next control frame of this stream, if any.
    pub(super) fn take_control(&mut self, id: StreamId) -> Option<ControlFrame> {
        if let Reset::Pending { code, final_size } = self.reset {
            self.reset = Reset::Sent { code, final_size };
            return Some(ControlFrame::ResetStream {
                id,
                error_code: code,
                final_size,
            });
        }
        None
    }

    /// A stream reset was lost.
    pub(super) fn control_lost(&mut self, frame: &ControlFrame) {
        if let ControlFrame::ResetStream {
            error_code, final_size, ..
        } = *frame
            && matches!(self.reset, Reset::Sent { .. })
        {
            self.reset = Reset::Pending {
                code: error_code,
                final_size,
            };
        }
    }

    /// A stream reset was acknowledged.
    pub(super) fn reset_acked(&mut self) {
        if matches!(self.reset, Reset::Sent { .. } | Reset::Pending { .. }) {
            self.reset = Reset::Acked;
        }
    }
}
