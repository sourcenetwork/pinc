//! The credit record: each side's flow-control limits, carried authenticated in the handshake.
//!
//! The record is a fixed 6 bytes, three big-endian `u16` values: the stream window in units of
//! [`WINDOW_UNIT`] (16 KiB), the most concurrent streams the sender accepts, and the largest datagram frame in bytes
//! the sender accepts (0: no datagrams). The idle timeout is not carried: it is the same fixed value on every node.
//! The record is absorbed into the transcript as its own field, so tampering with it breaks the handshake. A ticket
//! remembers the issuing side's record and mixes it into the ticket's pre-shared key, so a resumption only succeeds
//! against the record the client remembers.
//!
//! Invariants: a [`CreditRecord`] is `Copy`, exactly [`CREDIT_RECORD_LEN`] bytes on the wire, and every 6-byte string
//! decodes to exactly one record that re-encodes to the same bytes. `Default` is the record assumed before the peer
//! is heard: no window, no streams, no datagrams.

use core::fmt;

/// The size of the record on the wire.
pub const CREDIT_RECORD_LEN: usize = 6;
/// The unit of the stream window: 16 KiB.
pub const WINDOW_UNIT: u64 = 16 * 1024;

/// What one side lets the other send.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct CreditRecord {
    /// The stream window, in units of [`WINDOW_UNIT`].
    pub window_units: u16,
    /// The most concurrent streams the sender accepts.
    pub max_streams: u16,
    /// The largest datagram frame in bytes the sender accepts; 0 means it accepts none.
    pub max_datagram: u16,
}

impl CreditRecord {
    /// No credit at all: the record assumed before the peer is heard.
    pub const NONE: Self = Self {
        window_units: 0,
        max_streams: 0,
        max_datagram: 0,
    };

    /// A record granting a window of at least `window_bytes` bytes (rounded down to whole units, saturating at the
    /// largest the field holds), `max_streams` concurrent streams and `max_datagram` bytes per datagram frame.
    #[allow(clippy::cast_possible_truncation, reason = "the value is clamped to u16::MAX first")]
    pub const fn new(window_bytes: u64, max_streams: u16, max_datagram: u16) -> Self {
        let units = window_bytes / WINDOW_UNIT;
        Self {
            window_units: if units > u16::MAX as u64 {
                u16::MAX
            } else {
                units as u16
            },
            max_streams,
            max_datagram,
        }
    }

    /// The stream window in bytes.
    pub const fn window_bytes(&self) -> u64 {
        self.window_units as u64 * WINDOW_UNIT // lossless widening; `u64::from` is not const
    }

    /// The record as bytes.
    pub const fn encode(&self) -> [u8; CREDIT_RECORD_LEN] {
        let w = self.window_units.to_be_bytes();
        let s = self.max_streams.to_be_bytes();
        let d = self.max_datagram.to_be_bytes();
        [w[0], w[1], s[0], s[1], d[0], d[1]]
    }

    /// The record of 6 bytes.
    pub const fn decode(b: &[u8; CREDIT_RECORD_LEN]) -> Self {
        Self {
            window_units: u16::from_be_bytes([b[0], b[1]]),
            max_streams: u16::from_be_bytes([b[2], b[3]]),
            max_datagram: u16::from_be_bytes([b[4], b[5]]),
        }
    }

    /// Whether every limit of this record is at least `other`'s: a side that remembered `other` in a ticket can
    /// still honour what 0-RTT data relied on.
    pub const fn covers(&self, other: &Self) -> bool {
        self.window_units >= other.window_units
            && self.max_streams >= other.max_streams
            && self.max_datagram >= other.max_datagram
    }
}

impl fmt::Debug for CreditRecord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CreditRecord(window {} KiB, {} streams, datagram {} B)",
            self.window_bytes() / 1024,
            self.max_streams,
            self.max_datagram
        )
    }
}
