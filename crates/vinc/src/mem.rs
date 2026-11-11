//! The shape of the endpoint a driver runs, and the memory its connections use.
//!
//! The endpoint's tables are const-generic, so the driver builds one of a ladder of shapes: the smallest of
//! [`CAPACITIES`](crate::CAPACITIES) that holds [`Limits::connections`] sessions. Every shape has [`STREAMS`] stream slots per session
//! and [`RING`] chunk entries per stream half. What varies at run time is the pool of 16 KiB chunks each session may
//! use ([`Limits::pool_chunks`]). The endpoint owns all of it: it is allocated once, when the endpoint is built, on the
//! heap and piece by piece, and freed when the endpoint is dropped; nothing is leaked and nothing is shared.
//!
//! # Memory
//!
//! Per session, reserved up front for every slot of the shape: about 360 KiB of tables (a connection of 156 KiB and a
//! stream table of 203 KiB, both built when the engine starts) plus the endpoint's own tables of about 1 KiB. The
//! 16 KiB chunk pool of a session is zero-filled memory the system commits only as it is used, so an idle session
//! costs address space for `pool_chunks` chunks and almost no resident memory beyond its tables. Per endpoint, besides
//! the sessions: about 470 KiB of fixed tables. So the default 1024 sessions hold about 370 MiB of tables, 4096 hold
//! about 1.4 GiB, and the ceiling of 65536 holds about 23 GiB. The shape is rounded up to the next capacity of the
//! ladder, which doubles at each step: ask for what you need, not for a round number above it.
//!
//! Invariants: the memory of a session returns to its slot when the session ends; the slot table never grows.

use vinc_core::Endpoint;
use vinc_crypto::Software;
use vinc_transport::stream::NoSource;

use crate::error::{Error, Result};

/// The most sessions an engine can hold: the top of [`CAPACITIES`](crate::CAPACITIES).
pub const MAX_CONNECTIONS: usize = 65_536;
/// The stream slots of a session, both directions of opening counted.
pub const STREAMS: usize = 72;
/// The chunk entries of one stream half.
pub const RING: usize = 81;
pub(crate) const FLIGHT: usize = vinc_transport::recovery::SENT_PACKETS;
pub(crate) const PATHS: usize = 4;
pub(crate) const PREKEYS: usize = 8;
pub(crate) const TICKETS: usize = 64;
pub(crate) const CLIENT_TICKETS: usize = 32;

/// The endpoint a driver runs, for a table of `K` sessions and `D` connection id entries (ten per session).
pub(crate) type Ep<'s, 'a, const K: usize, const D: usize> =
    Endpoint<'s, 'a, Software, NoSource, STREAMS, RING, FLIGHT, PATHS, K, D, PREKEYS, TICKETS, CLIENT_TICKETS>;

/// The sizes a driver runs with; each has a default and a hard ceiling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The most sessions at once (at most [`MAX_CONNECTIONS`]). The memory for the next capacity of [`CAPACITIES`](crate::CAPACITIES)
    /// at or above it is reserved when the engine starts; see the module docs for what that costs.
    pub connections: usize,
    /// The 16 KiB chunks one session may hold for its streams and datagrams (at least 8). The default of 512 is 8 MiB:
    /// the pool of every session is reserved at start, so raise it for a few busy sessions, not for thousands.
    pub pool_chunks: usize,
    /// The receive window of each stream in bytes, at most `(RING - 1) * 16 KiB`, which is the default 1,310,720 (1.25
    /// MiB): a stream moves at most one window per round trip, so on a 150 ms path one stream tops out at 8.7 MB/s.
    /// The pool is charged the window of a stream from its first byte, so a raised window needs a raised
    /// `pool_chunks` to keep as many streams busy at once.
    pub stream_window: u64,
    /// The most data a session keeps written and unacknowledged, over all its streams (default 1,310,720, 1.25 MiB);
    /// a path whose bandwidth times round trip is larger needs a larger value.
    pub send_window: u64,
    /// The most streams the peer may have open at once on a session (at most 64).
    pub streams: u16,
    /// The most streams the peer may open that the application has not accepted, per session.
    pub accept_streams: usize,
    /// The most sessions accepted but not yet taken by the application.
    pub accept_sessions: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            connections: 1024,
            pool_chunks: 512,
            stream_window: 1_310_720,
            send_window: 1_310_720,
            streams: 64,
            accept_streams: 64,
            accept_sessions: 64,
        }
    }
}

impl Limits {
    /// Check the limits against the ceilings.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) naming the limit that is out of range.
    pub fn check(&self) -> Result<()> {
        let ok = (1..=MAX_CONNECTIONS).contains(&self.connections)
            && (8..=65_536).contains(&self.pool_chunks)
            && (16 * 1024..=16 * 1024 * 1024).contains(&self.stream_window)
            && (16 * 1024..=1 << 30).contains(&self.send_window)
            && (1..=64).contains(&self.streams)
            && self.accept_streams >= 1
            && self.accept_sessions >= 1;
        if ok {
            Ok(())
        } else {
            Err(Error::config("a limit is out of range"))
        }
    }
}
