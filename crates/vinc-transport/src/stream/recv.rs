//! The receive half of a stream: reassembly into pool chunks, final-size rules and window credit.
//!
//! Invariants: bytes live in the chunk ring at their absolute offset; `ranges` records which offsets were stored and
//! `contig` is the end of the prefix stored without holes; chunks wholly below `read_off` are returned to the pool; a
//! byte received twice must be identical.

use super::flow::{ConnRecv, Tune, Window};
use super::pool::{BufferPool, CHUNK_SIZE, Ring};
use super::ranges::RangeSet;
use super::{MAX_OFFSET, RANGES, RecvStatus, StreamError};

#[derive(Debug)]
pub(super) struct Recv<const C: usize> {
    pub(super) open: bool,
    ring: Ring<C>,
    ranges: RangeSet<RANGES>,
    pub(super) read_off: u64,
    highest: u64,
    contig: u64,
    final_size: Option<u64>,
    pub(super) win: Window,
    reset: Option<u64>,
    discard: bool,
    /// The application has seen the end (a consume after the final size, or a reset).
    observed: bool,
    pub(super) stop_pending: Option<u64>,
}

impl<const C: usize> Recv<C> {
    pub(super) const NEW: Self = Self {
        open: false,
        ring: Ring::EMPTY,
        ranges: RangeSet::EMPTY,
        read_off: 0,
        highest: 0,
        contig: 0,
        final_size: None,
        win: Window::new(0, 0),
        reset: None,
        discard: false,
        observed: false,
        stop_pending: None,
    };

    pub(super) const fn init(&mut self, size: u64, max: u64) {
        self.open = true;
        self.win = Window::new(size, max);
    }

    pub(super) fn status(&self) -> RecvStatus {
        match (self.reset, self.final_size) {
            (Some(code), _) => RecvStatus::Reset(code),
            (None, Some(f)) if f == self.read_off => RecvStatus::Finished,
            _ => RecvStatus::Open,
        }
    }

    /// Nothing more will be stored or read, and the application has seen the end.
    pub(super) fn is_done(&self) -> bool {
        !self.open || (self.observed && self.status() != RecvStatus::Open)
    }

    pub(super) fn release_all(&mut self, pool: &mut BufferPool<'_>) {
        self.ring.release_all(pool);
        self.ranges.clear();
    }

    fn readable(&self) -> u64 {
        if self.reset.is_some() {
            return 0;
        }
        self.contig.saturating_sub(self.read_off)
    }

    /// Store a STREAM frame.
    pub(super) fn on_data(
        &mut self,
        pool: &mut BufferPool<'_>,
        conn: &mut ConnRecv,
        offset: u64,
        data: &[u8],
        fin: bool,
    ) -> Result<(), StreamError> {
        let end = offset
            .checked_add(data.len() as u64)
            .filter(|&e| e <= MAX_OFFSET)
            .ok_or(StreamError::FlowControl)?;
        match self.final_size {
            Some(f) if end > f || (fin && end != f) => return Err(StreamError::FinalSize),
            None if fin && end < self.highest => return Err(StreamError::FinalSize),
            _ => {}
        }
        if end > self.win.limit {
            return Err(StreamError::FlowControl);
        }
        let delta = end.saturating_sub(self.highest);
        if !conn.admits(delta) {
            return Err(StreamError::FlowControl);
        }
        if self.reset.is_none() && !self.discard {
            self.store(pool, offset, data, end)?;
        }
        conn.received += delta;
        self.highest = self.highest.max(end);
        if fin {
            self.final_size = Some(end);
        }
        if self.discard {
            let n = self.highest - self.read_off;
            self.read_off = self.highest;
            self.contig = self.read_off;
            conn.consumed(n, None, pool.available_bytes());
        }
        Ok(())
    }

    fn store(&mut self, pool: &mut BufferPool<'_>, offset: u64, data: &[u8], end: u64) -> Result<(), StreamError> {
        let lo = offset.max(self.read_off);
        if lo >= end {
            return Ok(());
        }
        let body = usize::try_from(lo - offset)
            .ok()
            .and_then(|skip| data.get(skip..))
            .ok_or(StreamError::FlowControl)?;
        let first = lo / CHUNK_SIZE as u64;
        let last = (end - 1) / CHUNK_SIZE as u64;
        if last - self.read_off / CHUNK_SIZE as u64 >= C as u64 {
            return Err(StreamError::FlowControl);
        }
        if lo < self.highest {
            for ov in self.ranges.overlaps(lo..end) {
                let part = body.get((ov.start - lo) as usize..(ov.end - lo) as usize);
                if part.is_none_or(|p| !self.ring.matches(pool, ov.start, p)) {
                    return Err(StreamError::Conflict);
                }
            }
        }
        if self.ring.missing(first, last) > pool.available_chunks() {
            return Err(StreamError::Exhausted);
        }
        self.ranges.insert(lo..end).map_err(|_| StreamError::Fragmented)?;
        self.ring.write(pool, lo, body)?;
        self.contig = self.ranges.first().filter(|r| r.start == 0).map_or(0, |r| r.end);
        Ok(())
    }

    /// The contiguous readable bytes at the read position, up to the end of their chunk.
    pub(super) fn read_chunk<'a>(&self, pool: &'a BufferPool<'_>) -> Option<&'a [u8]> {
        let avail = self.readable();
        if avail == 0 {
            return None;
        }
        let at = (self.read_off % CHUNK_SIZE as u64) as usize;
        let len = (avail as usize).min(CHUNK_SIZE - at);
        self.ring.span(pool, self.read_off / CHUNK_SIZE as u64, at, len)
    }

    /// Release `n` readable bytes and credit them.
    pub(super) fn consume(
        &mut self,
        pool: &mut BufferPool<'_>,
        conn: &mut ConnRecv,
        n: u64,
        tune: Option<Tune>,
    ) -> Result<(), StreamError> {
        if n > self.readable() {
            return Err(StreamError::InvalidConsume);
        }
        let old = self.read_off / CHUNK_SIZE as u64;
        self.read_off += n;
        for k in old..self.read_off / CHUNK_SIZE as u64 {
            self.ring.release(pool, k);
        }
        if self.final_size == Some(self.read_off) {
            self.release_all(pool);
        }
        conn.consumed(n, tune, pool.available_bytes());
        let cap = self.final_size.unwrap_or(MAX_OFFSET);
        self.win.consumed(self.read_off, n, tune, cap);
        self.observed |= self.status() != RecvStatus::Open;
        Ok(())
    }

    /// The peer reset the stream: fix the final size, drop the buffered bytes and credit them to the connection.
    pub(super) fn on_reset(
        &mut self,
        pool: &mut BufferPool<'_>,
        conn: &mut ConnRecv,
        code: u64,
        final_size: u64,
    ) -> Result<(), StreamError> {
        if final_size > MAX_OFFSET || self.final_size.is_some_and(|f| f != final_size) || final_size < self.highest {
            return Err(StreamError::FinalSize);
        }
        if final_size > self.win.limit {
            return Err(StreamError::FlowControl);
        }
        if self.reset.is_some() {
            return Ok(());
        }
        let delta = final_size - self.highest;
        if !conn.admits(delta) {
            return Err(StreamError::FlowControl);
        }
        conn.received += delta;
        self.highest = final_size;
        self.final_size = Some(final_size);
        self.reset = Some(code);
        let n = final_size.saturating_sub(self.read_off);
        self.read_off = final_size;
        self.contig = final_size;
        self.release_all(pool);
        conn.consumed(n, None, pool.available_bytes());
        Ok(())
    }

    /// The application discards the rest of the stream: drop what is buffered and credit later bytes on arrival.
    pub(super) fn stop(&mut self, pool: &mut BufferPool<'_>, conn: &mut ConnRecv, code: u64) {
        if !self.open || self.discard || self.status() != RecvStatus::Open {
            return;
        }
        self.discard = true;
        self.observed = true;
        self.stop_pending = Some(code);
        let n = self.highest - self.read_off;
        self.read_off = self.highest;
        self.contig = self.read_off;
        self.release_all(pool);
        conn.consumed(n, None, pool.available_bytes());
    }

    /// STOP_SENDING needs retransmitting while the peer has not ended the stream.
    pub(super) fn requeue_stop(&mut self, code: u64) {
        if self.discard && self.status() == RecvStatus::Open {
            self.stop_pending = Some(code);
        }
    }
}
