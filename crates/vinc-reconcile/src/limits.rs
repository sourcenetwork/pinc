//! The bounds of a session.
//!
//! Invariants: a session allocates its buffers from these once (a few times `max_item`, plus the message and report
//! buffers, which grow only up to their limit) and never past them.

/// The longest message the three-byte length can describe, without the length itself.
pub const FRAME_MAX: usize = 0x00ff_ffff;

/// The memory and work bounds of one session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The longest item, and the longest set reference, in bytes.
    pub max_item: usize,
    /// The longest message body in bytes; at most [`FRAME_MAX`].
    pub max_message: usize,
    /// The most bytes of difference the initiator keeps for its report.
    pub max_report: usize,
    /// The most messages one side handles in a session.
    pub max_rounds: u32,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_item: 4096,
            max_message: FRAME_MAX,
            max_report: 64 << 20,
            max_rounds: 256,
        }
    }
}

impl Limits {
    /// The message limit clamped to what the frame can carry.
    #[cfg(feature = "alloc")]
    pub(crate) fn cap(&self) -> usize {
        self.max_message.min(FRAME_MAX)
    }
}
