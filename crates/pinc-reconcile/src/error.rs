//! The errors of a reconciliation session.
//!
//! Invariants: every failure on the wire or in the index is one of these values; nothing panics on any input.

use core::fmt;

/// What is wrong with a message from the peer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    /// The three-byte length does not match the bytes received.
    Frame,
    /// The message ends inside a field.
    Truncated,
    /// A part tag that is unknown or not allowed for this role.
    Tag,
    /// A range bound that cannot be decoded, is longer than an item may be, or is out of order.
    Bound,
    /// A count that is wrong for its part, or too large for the part kind.
    Count,
    /// An item that is longer than the limit, or items that are not strictly ascending.
    Item,
    /// A part or message that arrives in a state that cannot receive it.
    State,
}

impl fmt::Display for Reason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Frame => "the message length does not match its frame",
            Self::Truncated => "the message ends early",
            Self::Tag => "a part is unknown or not allowed here",
            Self::Bound => "a range bound is invalid",
            Self::Count => "a count is wrong for its part",
            Self::Item => "an item is too long or out of order",
            Self::State => "a part arrived in the wrong state",
        })
    }
}

/// Why a session step failed; `E` is the item index's own error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error<E> {
    /// The item index failed.
    Index(E),
    /// The item index is not strictly ascending, or returned a longer item than the buffer it was given.
    BadIndex,
    /// The peer sent a malformed message.
    Malformed(Reason),
    /// A message from the peer is longer than the message limit, or the item limit is too large for any message.
    MessageTooLarge,
    /// An item, or the set reference, is longer than the item limit.
    ItemTooLarge,
    /// The reported difference would be larger than the report limit. The host sets that limit; the protocol has none.
    ReportTooLarge,
    /// The exchange needed more rounds than the round limit, or held more suspended messages than a valid one needs.
    TooManyRounds,
    /// The final fingerprint still disagrees after the exact pass: the peer is faulty, or the index changed.
    Mismatch,
}

impl<E> From<Reason> for Error<E> {
    fn from(r: Reason) -> Self {
        Self::Malformed(r)
    }
}

impl<E: fmt::Debug> fmt::Display for Error<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Index(e) => write!(f, "the item index failed: {e:?}"),
            Self::BadIndex => f.write_str("the item index is unsorted or returned an item longer than its buffer"),
            Self::Malformed(r) => write!(f, "malformed message: {r}"),
            Self::MessageTooLarge => f.write_str("a message exceeds the message limit"),
            Self::ItemTooLarge => f.write_str("an item or the set reference exceeds the item limit"),
            Self::ReportTooLarge => f.write_str("the difference exceeds the report limit"),
            Self::TooManyRounds => f.write_str("the exchange exceeded the round limit"),
            Self::Mismatch => f.write_str("the sets still disagree after the exact pass"),
        }
    }
}

impl<E: fmt::Debug> core::error::Error for Error<E> {}
