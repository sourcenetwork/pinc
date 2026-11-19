//! The anti-amplification budget of one path.
//!
//! Invariants: before the path is validated, a send of `n` bytes is allowed only while
//! `tx + n + OVERHEAD <= 3 * rx`; after validation there is no limit. A caller that sends only when
//! [`AmpBudget::can_send`] holds keeps `tx <= 3 * rx` for the whole unvalidated phase. Counters saturate, and the
//! comparison is done in 128 bits, so no input overflows it.

/// The per-datagram overhead counted against the budget, in bytes.
pub const OVERHEAD: usize = 48;
/// How many bytes may be sent per byte received before validation.
pub const FACTOR: u64 = 3;

/// Bytes received and sent on a path, and whether the peer's address is validated.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AmpBudget {
    rx: u64,
    tx: u64,
    validated: bool,
}

impl AmpBudget {
    /// A fresh, unvalidated budget.
    pub const fn new() -> Self {
        Self {
            rx: 0,
            tx: 0,
            validated: false,
        }
    }

    /// Count `n` bytes received.
    pub const fn on_receive(&mut self, n: u64) {
        self.rx = self.rx.saturating_add(n);
    }

    /// Count `n` bytes sent.
    pub const fn on_send(&mut self, n: u64) {
        self.tx = self.tx.saturating_add(n);
    }

    /// Whether a datagram of `n` bytes may be sent now.
    pub fn can_send(&self, n: u64) -> bool {
        self.validated
            || u128::from(self.tx) + u128::from(n) + OVERHEAD as u128 <= u128::from(self.rx) * u128::from(FACTOR)
    }

    /// Mark the path validated: there is no limit from now on.
    pub const fn validate(&mut self) {
        self.validated = true;
    }

    /// Whether the path is validated.
    pub const fn is_validated(&self) -> bool {
        self.validated
    }

    /// Bytes received.
    pub const fn received(&self) -> u64 {
        self.rx
    }

    /// Bytes sent.
    pub const fn sent(&self) -> u64 {
        self.tx
    }
}
