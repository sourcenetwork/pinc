//! The typed reasons a handshake step or a record operation is refused.
//!
//! Invariants: every type is `Copy`, holds no key material and names a cause, never a secret value. A [`Failure`] is
//! either fatal (the state machine stops, and the same reason is queued as an event) or a dropped input (the state
//! machine is unchanged); [`Failure::is_fatal`] tells which.

use core::fmt;

use pinc_crypto::CryptoError;
use pinc_wire::WireError;

/// Why a handshake step was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Failure {
    /// The received message is malformed; it is dropped and the state is unchanged.
    Malformed(WireError),
    /// The authenticated content of a message is malformed.
    BadPayload(WireError),
    /// A message that does not belong to the current state; it is dropped and the state is unchanged.
    UnexpectedMessage,
    /// A key response that matches no outstanding request; it is dropped and the state is unchanged.
    UnexpectedKeyResponse,
    /// A first message that differs from the one this session holds, under the same connection ids: the held one was
    /// damaged or forged on the way, so the host may start the session again from this one. It is dropped and the state
    /// is unchanged.
    DifferentFirst,
    /// The peer speaks another protocol version.
    UnsupportedVersion,
    /// The requested ALPN is not served.
    UnknownAlpn,
    /// The peer's AEAD offer or choice shares nothing with ours.
    NoCommonAead,
    /// A parameter given to the state machine is out of range.
    InvalidParameter,
    /// The peer's key share or encapsulation key is invalid.
    InvalidPeerKey,
    /// A message did not authenticate: a tag, binder, confirmation or signature failed, or a check before it did (a
    /// dialing side reports every refusal of a Reply or resume Reply this way, since nothing in one has authenticated
    /// before the responder's signature or confirmation). The message is dropped and the state is unchanged, so the
    /// peer's resend can still complete the handshake.
    Authentication,
    /// The peer's signature does not verify.
    BadSignature,
    /// The responder is not the node that was dialed. A dialing side does not end on it: such a Reply has not
    /// authenticated as the dialed node, so it is dropped as [`Failure::Authentication`].
    WrongPeer,
    /// The host failed or refused a key operation.
    KeyOperation,
    /// The caller's random generator failed.
    Randomness,
    /// The ticket store could not find a fresh ticket id: the generator kept returning ids already stored.
    TicketId,
    /// The state machine already failed.
    Closed,
    /// The connection's buffer pool had no chunk for the handshake.
    OutOfMemory,
    /// A primitive refused its input.
    Crypto(CryptoError),
}

impl Failure {
    /// Whether this reason stops the state machine. The others drop the input and leave the state unchanged.
    pub const fn is_fatal(self) -> bool {
        !matches!(
            self,
            Self::Malformed(_)
                | Self::Authentication
                | Self::UnexpectedMessage
                | Self::UnexpectedKeyResponse
                | Self::DifferentFirst
                | Self::Closed
        )
    }
}

impl From<CryptoError> for Failure {
    fn from(e: CryptoError) -> Self {
        Self::Crypto(e)
    }
}

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(e) => write!(f, "malformed message: {e}"),
            Self::BadPayload(e) => write!(f, "malformed authenticated content: {e}"),
            Self::UnexpectedMessage => f.write_str("message does not fit the current state"),
            Self::UnexpectedKeyResponse => f.write_str("key response without an outstanding request"),
            Self::DifferentFirst => f.write_str("a different first message under the same connection ids"),
            Self::UnsupportedVersion => f.write_str("unsupported protocol version"),
            Self::UnknownAlpn => f.write_str("application protocol not served"),
            Self::NoCommonAead => f.write_str("no common AEAD"),
            Self::InvalidParameter => f.write_str("parameter out of range"),
            Self::InvalidPeerKey => f.write_str("invalid peer key"),
            Self::Authentication => f.write_str("authentication failed"),
            Self::BadSignature => f.write_str("signature does not verify"),
            Self::WrongPeer => f.write_str("peer is not the node that was dialed"),
            Self::KeyOperation => f.write_str("key operation failed"),
            Self::Randomness => f.write_str("random generator failed"),
            Self::TicketId => f.write_str("no fresh ticket id"),
            Self::Closed => f.write_str("handshake already failed"),
            Self::OutOfMemory => f.write_str("no buffer available for the handshake"),
            Self::Crypto(e) => write!(f, "{e}"),
        }
    }
}

impl core::error::Error for Failure {}
