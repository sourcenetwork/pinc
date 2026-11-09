//! Receive-window state and the delivery-rate meter that sizes it.
//!
//! Invariants: a window limit only ever grows and never drops below the bytes already received; the meter counts the
//! bytes the application consumed per smoothed round trip and nothing else, so the window it asks for follows what
//! the application actually drains.

/// A stream's receive window: the highest offset the peer may send and the size the limit is kept ahead of the reader.
#[derive(Debug, Clone, Copy)]
pub(super) struct Window {
    /// The highest offset the peer may send, as last advertised.
    pub(super) limit: u64,
    /// How far ahead of the read position the limit is kept.
    pub(super) size: u64,
    /// A new limit is waiting to be sent.
    pub(super) pending: bool,
    /// A grant is due but the buffer pool had no room for it yet.
    pub(super) deferred: bool,
}

impl Window {
    pub(super) const fn new(size: u64) -> Self {
        Self {
            limit: size,
            size,
            pending: false,
            deferred: false,
        }
    }
}

/// Bytes consumed per smoothed round trip, measured over successive epochs of at least one round trip.
#[derive(Debug, Clone, Copy)]
pub(super) struct Meter {
    start: Option<u64>,
    bytes: u64,
    rate: u64,
}

impl Meter {
    pub(super) const NEW: Self = Self {
        start: None,
        bytes: 0,
        rate: 0,
    };

    /// `n` more bytes were consumed at `now`; returns the latest completed per-round-trip rate (zero before the first
    /// epoch closes). `now` and `srtt` share one unit; a zero `srtt` never closes an epoch.
    pub(super) fn consumed(&mut self, n: u64, now: u64, srtt: u64) -> u64 {
        let start = *self.start.get_or_insert(now);
        self.bytes = self.bytes.saturating_add(n);
        let elapsed = now.saturating_sub(start);
        if srtt > 0 && elapsed >= srtt {
            let rate = u128::from(self.bytes) * u128::from(srtt) / u128::from(elapsed);
            self.rate = u64::try_from(rate).unwrap_or(u64::MAX);
            self.start = Some(now);
            self.bytes = 0;
        }
        self.rate
    }
}
