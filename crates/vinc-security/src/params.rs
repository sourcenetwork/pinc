//! Opaque transport parameters carried in the handshake.
//!
//! The handshake never reads them: it carries at most [`MAX_PARAMS_LEN`] bytes from each side, binds them into the
//! transcript as their own length-prefixed field (so tampering with them breaks the handshake), and hands the peer's
//! bytes to the transport in [`crate::Established`]. A ticket remembers the server's parameters of the session that
//! issued it, and they are mixed into the ticket's pre-shared key, so a resumption only succeeds against the
//! parameters the client remembers.
//! Invariant: a [`Params`] value never holds more than [`MAX_PARAMS_LEN`] bytes.

use core::fmt;

/// The most bytes of transport parameters either side may send.
pub const MAX_PARAMS_LEN: usize = 256;

/// A bounded copy of transport parameters.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Params {
    len: u16,
    bytes: [u8; MAX_PARAMS_LEN],
}

impl Params {
    /// No parameters.
    pub const EMPTY: Self = Self {
        len: 0,
        bytes: [0; MAX_PARAMS_LEN],
    };

    /// A copy of `bytes`, or `None` if there are more than [`MAX_PARAMS_LEN`].
    pub fn new(bytes: &[u8]) -> Option<Self> {
        let mut out = Self::EMPTY;
        out.bytes.get_mut(..bytes.len())?.copy_from_slice(bytes);
        out.len = u16::try_from(bytes.len()).ok()?;
        Some(out)
    }

    /// The bytes.
    pub fn as_bytes(&self) -> &[u8] {
        self.bytes.get(..usize::from(self.len)).unwrap_or_default()
    }
}

impl Default for Params {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl fmt::Debug for Params {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Params({} bytes)", self.len)
    }
}
