//! A hybrid logical clock: a physical millisecond reading plus a logical counter.
//!
//! Invariants: timestamps are totally ordered by `(wall, counter)`; [`Hlc::tick`] and [`Hlc::observe`] return a
//! value strictly greater than their receiver (until the 32-bit counter saturates, which needs 2^32 events inside one
//! millisecond) and never below the physical reading they are given; nothing reads a clock, the caller passes the
//! physical time. Every operation is saturating, so none panics.

/// A hybrid logical timestamp.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Hlc {
    /// The physical component, in milliseconds.
    pub wall: u64,
    /// The logical component, which orders events inside one millisecond.
    pub counter: u32,
}

impl Hlc {
    /// A timestamp from its parts.
    pub const fn new(wall: u64, counter: u32) -> Self {
        Self { wall, counter }
    }

    /// The timestamp of a local or send event at physical time `now`.
    #[must_use]
    pub const fn tick(self, now: u64) -> Self {
        if now > self.wall {
            Self::new(now, 0)
        } else {
            Self::new(self.wall, self.counter.saturating_add(1))
        }
    }

    /// The timestamp of a receive event for `remote` at physical time `now`.
    #[must_use]
    pub fn observe(self, remote: Self, now: u64) -> Self {
        let wall = self.wall.max(remote.wall).max(now);
        let counter = if wall == self.wall && wall == remote.wall {
            self.counter.max(remote.counter).saturating_add(1)
        } else if wall == self.wall {
            self.counter.saturating_add(1)
        } else if wall == remote.wall {
            remote.counter.saturating_add(1)
        } else {
            0
        };
        Self::new(wall, counter)
    }

    /// The physical time (milliseconds) at which a lifetime of `lifetime_ms` from this timestamp ends.
    pub const fn expires_at(self, lifetime_ms: u64) -> u64 {
        self.wall.saturating_add(lifetime_ms)
    }
}
