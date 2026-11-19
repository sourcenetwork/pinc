//! Incarnations and the address tag.
//!
//! An incarnation word is a 48-bit epoch in the high bits and a 16-bit record sequence in the low bits. The epoch
//! names one life of the node; the sequence orders the records of that life. Both only ever go up.
//!
//! With a persistent store the epoch is a counter: one more than the unsealed value, sealed before it is used. With
//! none it is a hybrid logical clock: the wall clock in milliseconds, but never at or below any epoch the node has
//! remembered or heard about itself, so a clock that jumped back cannot reissue an old incarnation.
//!
//! Invariants: [`Incarnation::word`] never decreases over the life of the value; a new epoch is sealed before the
//! word that carries it is returned; the sequence never wraps within an epoch (a full sequence starts a new epoch).

use crate::session::{Local, Nanos, StoreError};

const EPOCH_MAX: u64 = (1 << 48) - 1;

/// Why an incarnation could not be issued.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IncarnationError {
    /// The store failed.
    Store(StoreError),
    /// The 48-bit epoch space is used up.
    Exhausted,
}

impl From<StoreError> for IncarnationError {
    fn from(e: StoreError) -> Self {
        Self::Store(e)
    }
}

impl core::fmt::Display for IncarnationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Store(e) => e.fmt(f),
            Self::Exhausted => f.write_str("the incarnation epoch space is used up"),
        }
    }
}

impl core::error::Error for IncarnationError {}

/// The node's incarnation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Incarnation {
    epoch: u64,
    seq: u16,
}

impl Incarnation {
    /// Start a new life. `wall_ms` is the wall clock in milliseconds; `floor` is any epoch the host remembers by
    /// other means (0 for none).
    ///
    /// # Errors
    /// [`IncarnationError`] if the store fails or the epoch space is used up.
    pub fn start<L: Local>(local: &mut L, wall_ms: u64, floor: u64) -> Result<Self, IncarnationError> {
        let remembered = if local.persistent() {
            local.unseal_counter()?.unwrap_or(0)
        } else {
            0
        };
        let base = remembered.max(floor);
        let epoch = if local.persistent() {
            base.saturating_add(1)
        } else {
            wall_ms.saturating_add(1).max(base.saturating_add(1))
        };
        Self::seal(local, epoch)?;
        Ok(Self { epoch, seq: 0 })
    }

    fn seal<L: Local>(local: &mut L, epoch: u64) -> Result<(), IncarnationError> {
        if epoch > EPOCH_MAX {
            return Err(IncarnationError::Exhausted);
        }
        if local.persistent() {
            local.seal_counter(epoch)?;
        }
        Ok(())
    }

    /// The incarnation word.
    pub fn word(&self) -> u64 {
        (self.epoch << 16) | u64::from(self.seq)
    }

    /// The epoch alone.
    pub const fn epoch(&self) -> u64 {
        self.epoch
    }

    /// The next record of this life. A full sequence starts the next epoch.
    ///
    /// # Errors
    /// [`IncarnationError`] if a new epoch was needed and could not be sealed; the value is unchanged.
    pub fn next_record<L: Local>(&mut self, local: &mut L) -> Result<u64, IncarnationError> {
        if let Some(s) = self.seq.checked_add(1) {
            self.seq = s;
        } else {
            let epoch = self.epoch.saturating_add(1);
            Self::seal(local, epoch)?;
            *self = Self { epoch, seq: 0 };
        }
        Ok(self.word())
    }

    /// A peer reported the incarnation word `seen` for this node. If it is above ours, the node was reincarnated
    /// behind our back (a clock that jumped back, a lost store): move above it. Returns whether the word changed.
    ///
    /// # Errors
    /// [`IncarnationError`] if the new epoch could not be sealed; the value is unchanged.
    pub fn observe<L: Local>(&mut self, local: &mut L, seen: u64) -> Result<bool, IncarnationError> {
        if seen <= self.word() {
            return Ok(false);
        }
        let epoch = (seen >> 16).max(self.epoch).saturating_add(1);
        Self::seal(local, epoch)?;
        *self = Self { epoch, seq: 0 };
        Ok(true)
    }
}

/// The address tag: the hash of the identity ticket with a move counter folded in, so every handover changes the
/// tag, and the previous tag is kept for a settle time so one handover changes it once, not twice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct AddressTag {
    moves: u8,
    moved_at: Option<Nanos>,
    current: Option<[u8; 8]>,
}

/// How long after a move the previous tag is kept while the new reflexive address is unknown.
pub const MOVE_SETTLE: Nanos = 3_000_000_000;

impl AddressTag {
    /// The address changed (a handover). Several changes at one instant count once.
    pub fn moved(&mut self, now: Nanos) {
        if self.moved_at != Some(now) {
            self.moves = self.moves.wrapping_add(1);
        }
        self.moved_at = Some(now);
    }

    /// The current tag.
    pub fn tag<L: Local>(&mut self, now: Nanos, local: &L) -> [u8; 8] {
        let settling = self
            .moved_at
            .is_some_and(|t| now.saturating_sub(t) < MOVE_SETTLE && !local.reflexive_known());
        match self.current {
            Some(prev) if settling => prev,
            _ => {
                let t = local.address_hash(self.moves);
                self.current = Some(t);
                t
            }
        }
    }

    /// How many moves were counted, modulo 256.
    pub const fn moves(&self) -> u8 {
        self.moves
    }
}
