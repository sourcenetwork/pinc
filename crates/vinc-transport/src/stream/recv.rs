//! The receive half of a stream: reassembly into pool chunks and the final-size rules.
//!
//! Invariants: bytes live in the chunk ring at their absolute offset; `ranges` records which offsets were stored and
//! `contig` is the end of the prefix stored without holes; chunks wholly below `read_off` are returned to the pool; a
//! byte received twice must be identical. Window grants are decided by the table, which owns the pool accounting.

use super::flow::Window;
use super::pool::{BufferPool, CHUNK_SIZE, Ring};
use super::ranges::RangeSet;
use super::{FIRST_CHARGE, MAX_OFFSET, RECV_RANGES, RecvStatus, StreamError};

/// A request to the sender to stop, and where it stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Stop {
    None,
    Pending(u64),
    Sent(u64),
    Acked,
}

#[derive(Debug)]
pub(super) struct Recv<const C: usize> {
    pub(super) open: bool,
    ring: Ring<C>,
    ranges: RangeSet<RECV_RANGES>,
    pub(super) read_off: u64,
    highest: u64,
    contig: u64,
    final_size: Option<u64>,
    pub(super) win: Window,
    reset: Option<u64>,
    stop: Stop,
    /// The application has seen the end (a consume after the final size, or a reset).
    observed: bool,
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
        win: Window::new(0),
        reset: None,
        stop: Stop::None,
        observed: false,
    };

    pub(super) const fn init(&mut self, size: u64) {
        self.open = true;
        self.win = Window::new(size);
    }

    /// The slot view of the receive half; the table fills in the id and the send half.
    #[cfg(feature = "trace")]
    pub(super) fn trace_view(&self) -> super::trace::SlotView {
        super::trace::SlotView {
            id: u64::MAX,
            open: self.open,
            held: self.ring.numbers(self.read_off / CHUNK_SIZE as u64),
            ranges: self.ranges.to_vec(),
            read: self.read_off,
            highest: self.highest,
            contig: self.contig,
            fin: self.final_size,
            limit: self.win.limit,
            size: self.win.size,
            pending: self.win.pending,
            deferred: self.win.deferred,
            reset: self.reset,
            observed: self.observed,
            send_done: false,
            send_reset: 0,
            send_code: None,
            stop: match self.stop {
                Stop::None => 0,
                Stop::Pending(_) => 1,
                Stop::Sent(_) => 2,
                Stop::Acked => 3,
            },
            stop_code: match self.stop {
                Stop::Pending(c) | Stop::Sent(c) => Some(c),
                Stop::None | Stop::Acked => None,
            },
        }
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

    /// Ask the sender to stop with `code`. Nothing is queued if the sender already ended the stream or a request was made.
    pub(super) fn request_stop(&mut self, code: u64) {
        if self.open && self.reset.is_none() && self.final_size.is_none() && self.stop == Stop::None {
            self.stop = Stop::Pending(code);
        }
    }

    pub(super) const fn stop_pending(&self) -> bool {
        matches!(self.stop, Stop::Pending(_))
    }

    /// The stop request to send now, if one waits.
    pub(super) fn take_stop(&mut self) -> Option<u64> {
        let Stop::Pending(code) = self.stop else { return None };
        self.stop = Stop::Sent(code);
        Some(code)
    }

    /// The request was lost: send it again unless the sender has ended the stream meanwhile.
    pub(super) fn stop_lost(&mut self) {
        if let Stop::Sent(code) = self.stop
            && self.reset.is_none()
            && self.final_size.is_none()
        {
            self.stop = Stop::Pending(code);
        }
    }

    pub(super) fn stop_acked(&mut self) {
        if matches!(self.stop, Stop::Sent(_) | Stop::Pending(_)) {
            self.stop = Stop::Acked;
        }
    }

    pub(super) fn release_all(&mut self, pool: &mut BufferPool<'_>) {
        self.ring.release_all(pool);
        self.ranges.clear();
    }

    /// The pool bytes the credit up to the granted limit may still claim, as the ledger counts them
    /// ([`Recv::charged_demand`]): every chunk of the span from the read position to the limit that is not held yet. A
    /// byte received out of order claims its whole chunk, and a hole below the highest byte received is credit not yet
    /// used, so neither is counted by bytes.
    pub(super) fn unreceived(&self) -> u64 {
        self.charged_demand(self.win.limit)
    }

    /// The pool bytes credit up to `limit` may claim, as the ledger counts them: the first [`FIRST_CHARGE`] bytes while
    /// the stream has carried no data, the whole span once it has.
    pub(super) fn charged_demand(&self, limit: u64) -> u64 {
        let reach = if self.highest == 0 {
            limit.min(FIRST_CHARGE)
        } else {
            limit
        };
        self.pool_demand(reach)
    }

    /// The pool bytes credit up to `limit` may claim, as [`Recv::unreceived`].
    pub(super) fn pool_demand(&self, limit: u64) -> u64 {
        let reach = self.final_size.map_or(limit, |f| f.min(limit));
        if !self.open || reach <= self.read_off {
            return 0;
        }
        let chunk = CHUNK_SIZE as u64;
        let span = (reach - 1) / chunk - self.read_off / chunk + 1;
        span.saturating_sub(self.ring.held() as u64).saturating_mul(chunk)
    }

    /// The limit the window is due to move to, when at least an eighth of the window was freed.
    pub(super) fn due(&self) -> Option<u64> {
        if !self.open {
            return None;
        }
        let cap = self.final_size.unwrap_or(MAX_OFFSET);
        let candidate = self.read_off.saturating_add(self.win.size).min(cap);
        let limit = self.win.limit;
        (candidate > limit && candidate >= limit.saturating_add(self.win.size / 8)).then_some(candidate)
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
        if self.reset.is_none() {
            self.store(pool, offset, data, end)?;
        }
        self.highest = self.highest.max(end);
        if fin {
            self.final_size = Some(end);
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

    /// The stored bytes from absolute offset `at`, to the end of the stored run holding it or of its chunk; the run
    /// may lie beyond a hole. `None` below the read position, past a reset, or where nothing is stored.
    pub(super) fn read_at<'a>(&self, pool: &'a BufferPool<'_>, at: u64) -> Option<&'a [u8]> {
        if self.reset.is_some() || at < self.read_off {
            return None;
        }
        let run = self.ranges.containing(at)?;
        let chunk = CHUNK_SIZE as u64;
        let len = usize::try_from((run.end - at).min(chunk - at % chunk)).ok()?;
        self.ring.span(pool, at / chunk, (at % chunk) as usize, len)
    }

    /// The first stored run that reaches past `from`, cut to start at `from` or later.
    pub(super) fn stored_after(&self, from: u64) -> Option<core::ops::Range<u64>> {
        if self.reset.is_some() {
            return None;
        }
        let from = from.max(self.read_off);
        self.ranges.first_ending_after(from).map(|r| r.start.max(from)..r.end)
    }

    /// Release `n` readable bytes.
    pub(super) fn consume(&mut self, pool: &mut BufferPool<'_>, n: u64) -> Result<(), StreamError> {
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
        self.observed |= self.status() != RecvStatus::Open;
        Ok(())
    }

    /// The peer reset the stream: fix the final size and drop the buffered bytes.
    pub(super) fn on_reset(
        &mut self,
        pool: &mut BufferPool<'_>,
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
        self.highest = final_size;
        self.final_size = Some(final_size);
        self.reset = Some(code);
        self.read_off = final_size;
        self.contig = final_size;
        self.release_all(pool);
        Ok(())
    }
}
