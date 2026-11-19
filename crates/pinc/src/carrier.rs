//! The byte-stream carriers a member and a relay share, named once for both halves of the API.
//!
//! A carrier is a reliable byte stream the host opens (a member, toward a relay) or accepts (a relay, from a member).
//! The host does the transport work: the TCP connect or accept, the HTTP upgrade of a WebSocket. This crate sees only
//! the finished stream through the host's closures.
//!
//! # The buffer convention
//!
//! A carrier operation can outlive any one caller, so the buffers are owned and come back with the result:
//!
//! - `read(&S, Vec<u8>) -> (Result<usize>, Vec<u8>)`: fills at most `buf.len()` bytes from the start of the vector and
//!   returns the count; the vector's length is not changed and its contents past the count are unspecified; zero means
//!   the peer closed. A host implements it with `read(&mut buf[..])` on any runtime.
//! - `write(&S, Vec<u8>, usize) -> (Result<usize>, Vec<u8>)`: writes the vector from the given offset to its end and
//!   returns how many bytes went out, which may be fewer; the caller writes the rest.
//! - `close(S)`: ends the stream.
//!
//! On a [`CarrierKind::WsMessages`] stream a read returns at most one message and every write is one message; on the
//! other kinds the bytes are a plain stream and the boundaries of reads and writes mean nothing.
//!
//! The same names and shapes serve the client side (`open(&Relay, CarrierKind)`) and the server side of the relay.

/// How a carrier frames bytes on the wire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CarrierKind {
    /// A raw TCP stream: the bytes are PINC's own framing.
    Tcp,
    /// A WebSocket stream carrying PINC's own framing across its binary messages.
    Ws,
    /// A WebSocket as a browser uses it: one PINC frame per binary message, with no framing of its own.
    WsMessages,
}

impl CarrierKind {
    /// Every kind, in a stable order.
    pub const ALL: [Self; 3] = [Self::Tcp, Self::Ws, Self::WsMessages];

    /// Whether the transport keeps message boundaries, so PINC's own framing is not needed on top.
    #[must_use]
    pub const fn is_message_framed(self) -> bool {
        matches!(self, Self::WsMessages)
    }
}

#[cfg(test)]
mod tests {
    use super::CarrierKind;
    use alloc::vec::Vec;

    #[test]
    fn only_browser_websocket_keeps_message_boundaries() {
        let framed: Vec<_> = CarrierKind::ALL.into_iter().filter(|k| k.is_message_framed()).collect();
        assert_eq!(framed, [CarrierKind::WsMessages]);
    }
}
