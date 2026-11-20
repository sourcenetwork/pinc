//! The one error type of every table: what was refused and why, with no state changed.

use core::fmt;

use crate::storage::Storage;

/// Why a table refused an operation. The table is unchanged after any of them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The table holds as many records as it was made for.
    Full,
    /// A key, a value or a record has not the length the table was made for.
    Length,
    /// A position is past the end of the table.
    Position,
    /// The block is smaller than the table needs; `need` is the size it needs.
    Storage {
        /// The bytes the table needs.
        need: usize,
    },
    /// The capacity is more than the table's index can number, or the size it implies is more than any block.
    Capacity,
    /// The slot was given back already, or is not one this pool is holding (an old or forged handle). A handle of
    /// another pool of the same kind is not detected; a handle of another kind does not compile. An old handle is
    /// refused until its slot has been taken 2^31 times since.
    Stale,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Full => f.write_str("the table is full"),
            Self::Length => f.write_str("the key, value or record has the wrong length"),
            Self::Position => f.write_str("the position is past the end of the table"),
            Self::Storage { need } => write!(f, "the block is too small; the table needs {need} bytes"),
            Self::Capacity => f.write_str("the capacity is more than the table can hold"),
            Self::Stale => f.write_str("the slot was already given back"),
        }
    }
}

impl core::error::Error for Error {}

/// A constructor's refusal: the [`Error`] and the block it was given, handed back so a block that cannot be had
/// again (a `'static` one) can make a smaller table. Its `Debug` prints the block's length only.
#[derive(Debug)]
pub struct Refused {
    /// What was refused.
    pub error: Error,
    /// The block the constructor was given, untouched.
    pub storage: Storage,
}

impl fmt::Display for Refused {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.error, f)
    }
}

impl core::error::Error for Refused {}
