//! How long an unestablished handshake lasts: the limits the transport and the endpoint both ask.

use super::{CONNECT_TIMEOUT, RESPONDER_HOLD};

/// How long an unestablished handshake lasts, on either side: 30 s, twice that on a thin node. An endpoint keeps a
/// session whose peer is not authenticated yet for the same time, so a responder on a slow link still holds the session
/// when the dialer's Finish arrives late.
#[must_use]
pub const fn connect_limit(thin: bool) -> u64 {
    if thin { CONNECT_TIMEOUT * 2 } else { CONNECT_TIMEOUT }
}

/// How long an unestablished handshake lasts for a node that is thin or not and a responder that has answered or not:
/// the connect limit, and at least [`RESPONDER_HOLD`] once the responder's flight went out. Nothing exceeds 60 s.
#[must_use]
pub const fn handshake_limit(thin: bool, answered: bool) -> u64 {
    let base = connect_limit(thin);
    if answered && base < RESPONDER_HOLD {
        RESPONDER_HOLD
    } else {
        base
    }
}

/// The first instant at which an unestablished handshake begun at `created` has run out: the limit is exceeded, not
/// reached, so a session is still there at `created + limit` and gone one tick past it. The transport's own deadline
/// and the endpoint's half-open sweep both ask this, so they cannot disagree.
#[must_use]
pub const fn handshake_end(created: u64, thin: bool, answered: bool) -> u64 {
    created
        .saturating_add(handshake_limit(thin, answered))
        .saturating_add(1)
}
