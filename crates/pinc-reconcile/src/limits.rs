//! The bounds of a session.
//!
//! Invariants: a session allocates its buffers from these once (a few times `max_item`, plus the message and report
//! buffers, which grow only up to their limit) and never past them. A session holds at most a fixed number of
//! received messages that did not fit one reply, each at most the message limit.

use pinc_wire::varint;

use crate::hash::FP_LEN;

/// The longest message the three-byte length can describe, without the length itself.
pub const FRAME_MAX: usize = 0x00ff_ffff;

/// The memory and work bounds of one session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The longest item, and the longest set reference, in bytes.
    pub max_item: usize,
    /// The longest run of parts in a message body in bytes; at most [`FRAME_MAX`]. What frames the parts comes on top
    /// ([`max_body`](Self::max_body)). A difference of any size is spread over as many
    /// messages as it needs, as long as the limit is at least [`min_message`](Self::min_message).
    pub max_message: usize,
    /// The most bytes of difference the initiator keeps for its report. This is the host's choice of how much memory a
    /// session may take, not a limit of the protocol.
    pub max_report: usize,
    /// The most messages one side handles in a session. The messages follow the difference and the message limit, so
    /// this is a guard against a peer that never converges; the default is far above any valid exchange.
    pub max_rounds: u32,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_item: 4096,
            max_message: FRAME_MAX,
            max_report: 64 << 20,
            max_rounds: 1 << 24,
        }
    }
}

impl Limits {
    /// The message limit from which every valid exchange fits: a range is cut in two with up to four bounds of
    /// `max_item` bytes, and a leaf of one item is no larger. Below it a session still works while the keys are
    /// shorter than `max_item`, and fails with [`Error::MessageTooLarge`](crate::Error::MessageTooLarge) when a
    /// single part cannot fit.
    pub fn min_message(&self) -> usize {
        let bound = 1 + varint::encoded_len(self.max_item as u64) + self.max_item;
        4 * bound + 2 * (1 + FP_LEN) + 16
    }

    /// The longest message body a peer with these limits writes, and the longest one a reader accepts: the parts up
    /// to the message limit, plus what frames them (two bounds, the part count, and in the first message the set
    /// reference and the item count). A host that buffers messages bounds a body by this, and no more.
    pub fn max_body(&self) -> usize {
        (self.max_message.min(FRAME_MAX) + 2 * self.max_item + 4 * varint::MAX_LEN).min(FRAME_MAX)
    }

    /// The message limit clamped to what the frame can carry.
    #[cfg(feature = "alloc")]
    pub(crate) fn cap(&self) -> usize {
        self.max_message.min(FRAME_MAX)
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, clippy::cast_possible_truncation, reason = "tests may assert")]
mod tests {
    use alloc::vec::Vec;

    use super::*;
    use crate::{Initiator, MemIndex, Responder};

    /// An honest first message with a long set reference and a full part is longer than `max_message` and no longer
    /// than `max_body`; the responder takes it, and a body one byte over `max_body` is refused.
    #[test]
    fn the_longest_honest_body_is_within_max_body_and_one_byte_more_is_refused() {
        let base = Limits {
            max_item: 16,
            ..Limits::default()
        };
        let lim = Limits {
            max_message: base.min_message(),
            ..base
        };
        let items: Vec<[u8; 16]> = (0u16..17).map(|i| [i as u8; 16]).collect();
        let idx = MemIndex::from_sorted(items.iter().map(<[u8; 16]>::as_slice)).unwrap();
        let mut init = Initiator::new(lim);
        let mut msg = Vec::new();
        init.start(&idx, &[0x5a; 16], &mut msg).unwrap();
        let body = msg.len() - 3;
        assert!(
            body > lim.max_message && body <= lim.max_body(),
            "body {body}, limit {}",
            lim.max_message
        );
        let empty = MemIndex::from_sorted(core::iter::empty::<&[u8]>()).unwrap();
        let mut out = Vec::new();
        assert!(Responder::new(lim).handle(&empty, &msg, &mut out).is_ok());
        let over = lim.max_body() + 1;
        let mut long = alloc::vec![(over >> 16) as u8, (over >> 8) as u8, over as u8];
        long.resize(3 + over, 0);
        assert!(Responder::new(lim).handle(&empty, &long, &mut out).is_err());
    }
}
