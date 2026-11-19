//! The abstract session: what the value protocol needs from a connection layer, as static generic traits.
//!
//! A later step implements these over `pinc-core`; the tests implement them in memory. Nothing here owns bytes: the
//! session keeps received stream bytes until the value layer [`consume`](Session::consume)s them, so the value layer
//! hashes bytes where they sit (the incremental verifier) and the packet buffers are released only after the group
//! they carry has verified.
//!
//! # Conventions
//!
//! - A [`StreamId`] is a handle unique within one [`Session`] across all peers, and it is also the id written into
//!   the range-proof extension frames, so both ends agree on it.
//! - Stream offsets in this interface are absolute offsets in the stream, not offsets in a buffer.
//! - Time is a monotonic nanosecond count supplied by the caller; nothing here reads a clock.

use pinc_transport::stream::StreamId;

use crate::source::ValueSource;
use crate::store::ValueRead;

/// A provider of values: an opaque handle the host maps to a peer and its connection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Provider(pub u32);

/// What the connection layer knows about a provider's session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PeerInfo {
    /// The smoothed round trip in nanoseconds, if sampled.
    pub rtt_ns: Option<u64>,
    /// Whether a probe timeout is pending.
    pub pto: bool,
    /// The time the last packet arrived.
    pub last_rx: u64,
}

/// Why a stream could not be opened.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenError {
    /// There is no usable session to the provider.
    NotConnected,
    /// The session has no stream credit or table room now.
    Busy,
}

/// Stream-level operations shared by both sides.
pub trait Session {
    /// Call `f` on the pieces of present bytes of `stream` from absolute offset `from`, in order, stopping at the
    /// first hole. `f` returns how many bytes of the piece it took; if that is less than the piece, the visit stops.
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, stream: StreamId, from: u64, f: F);
    /// Whether every byte of `[from, from + len)` of `stream` is present.
    fn has(&self, stream: StreamId, from: u64, len: u64) -> bool;
    /// Release the in-order bytes of `stream` below absolute offset `upto`.
    fn consume(&mut self, stream: StreamId, upto: u64);
    /// Write all of `data` to `stream` and end it if `fin`; false if it was not all accepted.
    fn write(&mut self, stream: StreamId, data: &[u8], fin: bool) -> bool;
    /// Abandon `stream` in both directions with `code`.
    fn reset(&mut self, stream: StreamId, code: u64);
    /// Send a reliable extension frame of type `ty` with `body` to the peer of `stream`; false if it was not queued.
    fn send_ext(&mut self, stream: StreamId, ty: u64, body: &[u8]) -> bool;
}

/// The requesting side: sessions to providers.
pub trait Outbound: Session {
    /// Whether a session to `provider` is up.
    fn is_connected(&self, provider: Provider) -> bool;
    /// Start a session to `provider` unless one is being set up; the outcome arrives as an event.
    fn dial(&mut self, provider: Provider);
    /// Close the session to `provider` so the next dial starts afresh.
    fn hangup(&mut self, provider: Provider);
    /// Open a bidirectional stream to `provider` at `urgency`.
    ///
    /// # Errors
    /// [`OpenError`] when there is no session or no room.
    fn open_stream(&mut self, provider: Provider, urgency: u8) -> Result<StreamId, OpenError>;
    /// What the session to `provider` knows, if it is up.
    fn peer_info(&self, provider: Provider) -> Option<PeerInfo>;
}

/// The serving side: back a stream with a store-reading source.
pub trait Inbound<H: ValueRead>: Session {
    /// Whether the host serves the value under `root` at all. A request for a root that is not provided is refused
    /// as unavailable even if the store holds it. The default serves every value the store holds whole.
    fn provided(&self, _root: &[u8; 32]) -> bool {
        true
    }

    /// Make `stream` send `len` bytes read from `source` when frames are built, and end it after the last.
    /// False if the stream is gone.
    fn serve(&mut self, stream: StreamId, source: ValueSource<H>, len: u64) -> bool;
}
