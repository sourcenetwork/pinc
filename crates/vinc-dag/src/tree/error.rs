//! Errors of the tree module.
//!
//! One `Copy` enum for layout, outboard building, range encoding and range verification, so a caller matches once.

use core::fmt;

/// Why a tree operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TreeError {
    /// The group size is not a supported power-of-two multiple of the 1024-byte chunk.
    InvalidGroupSize,
    /// The requested byte range extends past the end of the value.
    RangeOutOfBounds,
    /// More bytes were supplied than the value length declares.
    TooMuchData,
    /// The input ended before the declared value length was reached.
    Incomplete,
    /// The outboard buffer does not have the size its layout requires.
    OutboardSize,
    /// The output buffer is too small for the encoded stream.
    OutputTooSmall,
    /// A parent pair does not hash to the chaining value it must match.
    ParentMismatch,
    /// A group does not hash to the chaining value it must match.
    GroupMismatch,
    /// The root does not match the hash of the empty value.
    RootMismatch,
    /// The proof stack is exhausted; unreachable for any layout this crate accepts.
    StackOverflow,
}

impl fmt::Display for TreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidGroupSize => "group size is not a supported power-of-two multiple of 1024 bytes",
            Self::RangeOutOfBounds => "byte range extends past the end of the value",
            Self::TooMuchData => "more data than the declared value length",
            Self::Incomplete => "input ended before the declared value length",
            Self::OutboardSize => "outboard buffer has the wrong size",
            Self::OutputTooSmall => "output buffer is too small",
            Self::ParentMismatch => "proof node does not match its expected hash",
            Self::GroupMismatch => "data group does not match its expected hash",
            Self::RootMismatch => "root does not match the empty value",
            Self::StackOverflow => "proof stack exhausted",
        })
    }
}

impl core::error::Error for TreeError {}
