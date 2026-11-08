//! The anti-replay window: a sliding bitmap of recently accepted packet numbers.
//!
//! Invariants: a packet number is accepted at most once; a number at or below `highest - BITS` is refused as too
//! old; the window never accepts a number it has seen and never refuses an unseen number inside it. The bitmap is a
//! ring indexed by `pn % BITS`, so a slide only clears the positions that fall out of the window. Call
//! [`ReplayWindow::check`] before the (expensive) decryption and [`ReplayWindow::insert`] only after the packet
//! authenticated, so a forged packet cannot occupy a slot.

use core::fmt;

const WORDS: usize = 16;
/// The largest window, in packet numbers.
pub const MAX_BITS: usize = WORDS * 64;

/// Why a packet number was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReplayError {
    /// The packet number was already accepted.
    Duplicate,
    /// The packet number is below the window.
    TooOld,
}

impl fmt::Display for ReplayError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Duplicate => "packet number already received",
            Self::TooOld => "packet number below the replay window",
        })
    }
}

impl core::error::Error for ReplayError {}

/// A window of the last `BITS` packet numbers (1 to [`MAX_BITS`]).
#[derive(Debug, Clone)]
pub struct ReplayWindow<const BITS: usize> {
    words: [u64; WORDS],
    highest: u64,
    started: bool,
}

impl<const BITS: usize> Default for ReplayWindow<BITS> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const BITS: usize> ReplayWindow<BITS> {
    const VALID: () = assert!(BITS >= 1 && BITS <= MAX_BITS, "the window is 1 to 1024 packet numbers");

    /// An empty window.
    pub const fn new() -> Self {
        let () = Self::VALID;
        Self {
            words: [0; WORDS],
            highest: 0,
            started: false,
        }
    }

    /// The highest packet number accepted so far.
    pub const fn highest(&self) -> Option<u64> {
        if self.started { Some(self.highest) } else { None }
    }

    /// The ring position of `pn`: a word index and a bit mask.
    #[allow(
        clippy::cast_possible_truncation,
        reason = "the remainder is below BITS, at most 1024"
    )]
    const fn slot(pn: u64) -> (usize, u64) {
        let pos = (pn % BITS as u64) as usize;
        (pos / 64, 1 << (pos % 64))
    }

    fn is_set(&self, pn: u64) -> bool {
        let (word, bit) = Self::slot(pn);
        self.words.get(word).is_some_and(|w| w & bit != 0)
    }

    fn assign(&mut self, pn: u64, on: bool) {
        let (word, bit) = Self::slot(pn);
        if let Some(w) = self.words.get_mut(word) {
            if on {
                *w |= bit;
            } else {
                *w &= !bit;
            }
        }
    }

    /// Whether `pn` would be accepted, without recording it.
    ///
    /// # Errors
    /// [`ReplayError::Duplicate`] if `pn` was accepted before; [`ReplayError::TooOld`] if it is below the window.
    pub fn check(&self, pn: u64) -> Result<(), ReplayError> {
        if !self.started || pn > self.highest {
            return Ok(());
        }
        if self.highest - pn >= BITS as u64 {
            return Err(ReplayError::TooOld);
        }
        if self.is_set(pn) {
            Err(ReplayError::Duplicate)
        } else {
            Ok(())
        }
    }

    /// Record `pn` as received, sliding the window if it is the highest so far.
    ///
    /// # Errors
    /// As [`ReplayWindow::check`]; nothing is recorded on error.
    pub fn insert(&mut self, pn: u64) -> Result<(), ReplayError> {
        self.check(pn)?;
        if !self.started || pn.saturating_sub(self.highest) >= BITS as u64 {
            self.words = [0; WORDS];
        } else if pn > self.highest {
            // Positions of the numbers that leave the window: those between the old and the new highest.
            for gone in self.highest + 1..=pn {
                self.assign(gone, false);
            }
        }
        if !self.started || pn > self.highest {
            self.highest = pn;
            self.started = true;
        }
        self.assign(pn, true);
        Ok(())
    }
}
