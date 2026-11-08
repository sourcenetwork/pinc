//! Flow-control credit: the receive window with autotuning, and the connection-level send and receive counters.
//!
//! Invariants: a limit only ever grows; a window never exceeds its maximum; the connection receive limit never grants
//! more unreceived credit than the buffer pool can still hold when the grant is made.

/// `(now, srtt)` in the same monotonic nanosecond unit, passed by the caller on a read.
pub(super) type Tune = (u64, u64);

/// A receive window that slides as the application consumes, and doubles when it is consumed fast.
#[derive(Debug, Clone, Copy)]
pub(super) struct Window {
    /// The highest offset the peer may send, as last advertised.
    pub(super) limit: u64,
    size: u64,
    max: u64,
    /// Time and consumed offset at the start of the current measurement.
    epoch: Option<(u64, u64)>,
    /// A new limit is waiting to be sent.
    pub(super) pending: bool,
}

impl Window {
    pub(super) const fn new(size: u64, max: u64) -> Self {
        Self {
            limit: size,
            size,
            max,
            epoch: None,
            pending: false,
        }
    }

    pub(super) const fn size(&self) -> u64 {
        self.size
    }

    /// `n` more bytes were consumed, `total` in all. A window consumed in under two round trips doubles (up to its
    /// maximum); once an eighth of the window is freed, a new limit of `total + size` (at most `cap`) is queued.
    pub(super) fn consumed(&mut self, total: u64, n: u64, tune: Option<Tune>, cap: u64) {
        if let Some((now, srtt)) = tune {
            let (start, base) = *self.epoch.get_or_insert((now, total.saturating_sub(n)));
            if total.saturating_sub(base) >= self.size {
                if now.saturating_sub(start) < srtt.saturating_mul(2) {
                    self.size = self.size.saturating_mul(2).min(self.max);
                }
                self.epoch = Some((now, total));
            }
        }
        let candidate = total.saturating_add(self.size).min(cap);
        if candidate > self.limit && candidate >= self.limit.saturating_add(self.size / 8) {
            self.limit = candidate;
            self.pending = true;
        }
    }
}

/// The connection-level receive side.
#[derive(Debug, Clone, Copy)]
pub(super) struct ConnRecv {
    pub(super) win: Window,
    /// Sum over streams of the highest offset received.
    pub(super) received: u64,
    pub(super) consumed: u64,
}

impl ConnRecv {
    /// Whether `delta` new bytes fit under the limit.
    pub(super) const fn admits(&self, delta: u64) -> bool {
        match self.received.checked_add(delta) {
            Some(total) => total <= self.win.limit,
            None => false,
        }
    }

    /// `n` bytes were consumed; `pool_free` is what the pool can still hold.
    pub(super) fn consumed(&mut self, n: u64, tune: Option<Tune>, pool_free: u64) {
        self.consumed = self.consumed.saturating_add(n);
        let cap = self.received.saturating_add(pool_free);
        self.win.consumed(self.consumed, n, tune, cap);
    }
}

/// The connection-level send side.
#[derive(Debug, Clone, Copy)]
pub(super) struct ConnSend {
    /// The peer's MAX_DATA.
    pub(super) limit: u64,
    /// Credit spent: bytes accepted by buffered streams plus bytes first sent by source streams.
    pub(super) used: u64,
    blocked_sent: Option<u64>,
    pub(super) blocked_pending: bool,
}

impl ConnSend {
    pub(super) const fn new(limit: u64) -> Self {
        Self {
            limit,
            used: 0,
            blocked_sent: None,
            blocked_pending: false,
        }
    }

    pub(super) const fn credit(&self) -> u64 {
        self.limit.saturating_sub(self.used)
    }

    /// Queue a DATA_BLOCKED for the current limit, once per limit.
    pub(super) const fn block(&mut self) {
        if !matches!(self.blocked_sent, Some(l) if l == self.limit) {
            self.blocked_pending = true;
        }
    }

    pub(super) const fn take_blocked(&mut self) -> u64 {
        self.blocked_pending = false;
        self.blocked_sent = Some(self.limit);
        self.limit
    }

    pub(super) const fn requeue_blocked(&mut self, limit: u64) {
        if limit == self.limit {
            self.blocked_sent = None;
            self.blocked_pending = true;
        }
    }
}
