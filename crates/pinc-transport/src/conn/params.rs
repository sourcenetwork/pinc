//! The credit record as a connection uses it: what each endpoint tells the other about its limits, carried
//! authenticated in the handshake.
//!
//! The record is `pinc_security::CreditRecord`, a fixed 6 bytes: the stream window in 16 KiB units (`u16`), the
//! concurrent-stream limit (`u16`) and the datagram limit in bytes (`u16`). It has no idle timeout (idle is the same
//! fixed value on every node), no connection-level credit and no negotiated options. Before the peer is heard the
//! record is [`CreditRecord::NONE`]: no window, no streams, no datagrams. A ticket remembers the issuer's record,
//! and 0-RTT data may rely on it only up to what the record says.
//!
//! This module turns the record into the numbers the stream layer takes. Applying the concurrency limit and the
//! per-stream window on the stream side is the stream layer's job; the decoded values are exposed here and through
//! [`Connection::peer_credit`](super::Connection::peer_credit).

pub use pinc_security::CreditRecord;

use crate::stream::{self, PeerLimits};

/// The datagram frame size an endpoint advertises by default: the largest the record holds.
const DEFAULT_MAX_DATAGRAM: u16 = u16::MAX;

/// The record that matches a stream layer configured with `cfg`: its stream window, its concurrent-stream limit
/// (saturating at the field's width) and the default datagram limit.
#[allow(clippy::cast_possible_truncation, reason = "the value is clamped to u16::MAX first")]
pub const fn credit_for_streams(cfg: &stream::Config) -> CreditRecord {
    let streams = if cfg.max_streams > u16::MAX as u64 {
        u16::MAX
    } else {
        cfg.max_streams as u16
    };
    CreditRecord::new(cfg.initial_stream_window, streams, DEFAULT_MAX_DATAGRAM)
}

/// What the peer's record lets us send, as the stream layer takes it: its window for every stream, and how many
/// streams we may have open at once.
pub const fn peer_limits(c: &CreditRecord) -> PeerLimits {
    PeerLimits {
        window: c.window_bytes(),
        max_streams: c.max_streams as u64,
    }
}
