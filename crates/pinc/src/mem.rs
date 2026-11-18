//! The shape of the endpoint a driver runs, and the memory its connections use.
//!
//! The endpoint's tables are const-generic, so the driver builds one of a ladder of shapes: the smallest of
//! [`CAPACITIES`](crate::CAPACITIES) that holds [`Limits::connections`] sessions. Every shape has [`STREAMS`] stream slots per session
//! and [`RING`] chunk entries per stream half. What varies at run time is the pool of 16 KiB chunks each session may
//! use ([`Limits::pool_chunks`]). The endpoint owns its tables: they are allocated on the heap and piece by piece, and
//! freed when the endpoint is dropped; nothing is leaked. What the endpoints of one thread share is what they hold
//! only for a moment: the receive and transmit buffers of their drivers and the state machines of handshakes in
//! progress.
//!
//! # Memory
//!
//! Per session, every slot of the shape reserves a connection, a stream table of [`STREAMS`] slots (a slot is a few KiB
//! with a [`RING`] of 257 entries, and is written only when its stream is first used) and a pool of up to
//! [`Limits::pool_chunks`] chunks of 16 KiB. The stream table and the table of sent packets are reserved memory the
//! system commits only as it is used. Every pool takes its chunks from the endpoint's one chunk store
//! ([`Limits::memory_chunks`]), allocated when the engine starts and committed by the system as chunks are first used,
//! and gives each back to it as soon as the session returns it: so a quiet session holds no chunk, nothing is
//! allocated or freed for a stream or a session, and the endpoint's chunk memory stays at the most its sessions held at
//! once. A session that moved 64 KiB and went quiet holds about 96 KiB of the client's memory, and a client endpoint
//! with no session about 620 KiB (`tests/pinc_client_memory.rs` holds them to 112 and 704 KiB). The shape is rounded up to the next capacity of the ladder, which doubles at each step: ask for what you
//! need, not for a round number above it.
//!
//! Invariants: the memory of a session returns to its slot when the session ends; the slot table never grows.

use pinc_core::Endpoint;
use pinc_crypto::Software;

use crate::error::{Error, Result};

/// The most protocols (ALPNs) an endpoint serves for the application: those the builder lists and those registered.
pub const MAX_PROTOCOLS: usize = 8;
/// The most sessions an engine can hold: the top of [`CAPACITIES`](crate::CAPACITIES).
pub const MAX_CONNECTIONS: usize = 65_536;
/// The stream slots of a session, both directions of opening counted. Half are for the streams the peer opens, so a
/// session carries up to 100 of them at once each way. A slot is written when a stream first uses it, so a session
/// with few streams pays for few.
pub const STREAMS: usize = 200;
/// The chunk entries of one stream half.
pub const RING: usize = 257;
pub(crate) const FLIGHT: usize = pinc_transport::recovery::SENT_PACKETS;
pub(crate) const PATHS: usize = 4;
pub(crate) const PREKEYS: usize = 8;
pub(crate) const TICKETS: usize = 64;
pub(crate) const CLIENT_TICKETS: usize = 32;

/// The endpoint a driver runs, for a table of `K` sessions and `D` connection id entries (ten per session).
pub(crate) type Ep<'s, 'a, const K: usize, const D: usize> =
    Endpoint<'s, 'a, Software, crate::Body, STREAMS, RING, FLIGHT, PATHS, K, D, PREKEYS, TICKETS, CLIENT_TICKETS>;

/// The sizes a driver runs with; each has a default and a hard ceiling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The most sessions at once (at most [`MAX_CONNECTIONS`]). The memory for the next capacity of [`CAPACITIES`](crate::CAPACITIES)
    /// at or above it is reserved when the engine starts; see the module docs for what that costs.
    pub connections: usize,
    /// The 16 KiB chunks one session may hold for its streams and datagrams (8 to 65,535). The default of 1024 is 16 MiB,
    /// a ceiling: a busy session holds the chunks it came to use and a quiet one (no stream open) none, every chunk
    /// coming from the endpoint's store ([`memory_chunks`](Self::memory_chunks)). Streams that move data at once are
    /// charged their whole window, so a path whose bandwidth times round trip is above half the pool needs more.
    pub pool_chunks: usize,
    /// The slots of the endpoint's spill arena (0 to 65,536; default 128, 1 MiB): when a stream's ranges (received,
    /// lost or acknowledged) outgrow the few it keeps inline, under scattered loss, they move into one 8 KiB slot until
    /// they shrink to half of inline again. The arena is allocated once with the endpoint, commits a slot's memory the
    /// first time it is used, and is shared by every session, each holding at most half of it. With no slot free a
    /// received frame that needs one more range is refused and sent again by the peer, and a lost range is widened or
    /// sent again; 0 turns spilling off.
    pub spill_slots: usize,
    /// The 16 KiB chunks of the endpoint's store, every chunk its sessions may hold together, reserved when the engine
    /// starts as one allocation the system commits only as chunks are first used, and never given back before the
    /// engine stops: memory stays at its high-water mark. `None` (the default) is [`default_memory_chunks`] of the
    /// connections and the pool. Every slot of the endpoint (the rung of [`CAPACITIES`](crate::CAPACITIES) that holds
    /// the connections) keeps a floor of 8 chunks of it from the start, so it must hold that many for each and no
    /// session is ever refused; the rest is burst room the sessions that need more than their floor share in turn. A
    /// full store holds back new windows and writes as a full pool does.
    pub memory_chunks: Option<usize>,
    /// The receive window a stream starts with, in bytes (default 1,310,720, 1.25 MiB). It grows toward twice what the
    /// stream's own reader drains per round trip, up to half the pool and `(RING - 1) * 16 KiB` (4 MiB): a stream moves at
    /// most one window per round trip. The pool is charged the window of a stream from its first byte, so a raised
    /// window needs a raised `pool_chunks` to keep as many streams busy at once.
    pub stream_window: u64,
    /// The most data a session keeps written and unacknowledged, over all its streams (default 16 MiB): the smaller of
    /// this and 1.5 times the congestion window, which is what binds on any path under about 1 Gbit/s at 100 ms.
    pub send_window: u64,
    /// The most streams the peer may have open at once on a session (at most 100, half the slots of
    /// [`STREAMS`]). A peer that sends one request a stream has this many requests in flight on a session. A new
    /// stream needs room in the pool for its first 64 KiB beside the same for each stream already open, so with the
    /// default pool a hundred streams stay open and busy at once; what they send together beyond the pool is held
    /// back and sent again by the peer.
    pub streams: u16,
    /// The most streams the peer may open that the application has not accepted, per session.
    pub accept_streams: usize,
    /// The most sessions accepted but not yet taken by the application, per protocol (default 1,024, the default
    /// connection table, so a burst the table holds is taken whole). The endpoint starts no handshake that could not
    /// wait here: while the sessions in the fullest queue and those whose handshake is under way or not yet queued fill
    /// it, a first flight is refused before any work and the dialer sends it again, so a session that finished its
    /// handshake is never closed for want of room. A waiting session holds its slot of the table (see the module docs)
    /// and its entry in the queue; the table bounds them whatever this is. Two things follow from the endpoint not
    /// knowing a first flight's protocol before it opens it: the fullest queue holds back the dials of every protocol,
    /// and handshakes whose peer is not authenticated yet may hold at most half of the free places at a time, so that
    /// first flights that never finish cannot keep out a peer that resumes.
    pub accept_sessions: usize,
    /// The largest message [`Endpoint::publish`](crate::Endpoint::publish) takes, in bytes (at most 16 MiB). Larger data
    /// belongs behind a reference: publish a root or an id and fetch the bytes over a stream.
    pub topic_message: usize,
    /// The bytes of messages a hub endpoint keeps for each topic (at most 1 GiB; never less than four of the largest
    /// message). A subscriber whose path is slower than a burst is served from this log, and so is one that was away:
    /// a burst larger than the log loses its oldest messages for a subscriber that could not keep up. The memory is
    /// taken as a topic's log fills.
    pub topic_log: usize,
    /// The most topics the endpoint tracks at once.
    pub topics: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            connections: 1024,
            pool_chunks: 1024,
            spill_slots: pinc_transport::stream::spill::DEFAULT_SLOTS,
            memory_chunks: None,
            stream_window: 1_310_720,
            // vertexia: the transport's own default is the reference's 1,310,720 bytes, a figure sized for its test
            // links; at the facade a session of one stream or many would be held to 8.7 MiB/s on a 150 ms path
            // whatever its congestion window. This is a deliberate departure from the reference's constant at the
            // product surface only: the cap stays `min(send_window, max(192 KiB, 1.5 x cwnd))`, and below a congestion
            // window of 873,813 bytes it is the same. Upgrade path: none needed; a host can set the reference's value.
            send_window: 16 * 1024 * 1024,
            streams: 100,
            accept_streams: 100,
            accept_sessions: 1024,
            topic_message: 65_536,
            topic_log: 4 << 20,
            topics: 128,
        }
    }
}

/// The store a node of `connections` sessions of up to `pool_chunks` chunks gets by default: a floor for every slot of
/// the endpoint (the rung of [`CAPACITIES`](crate::CAPACITIES) that holds the connections), held from the start, and a
/// floor of burst room for each connection, shared by the sessions that need more than theirs. 16,384 chunks, 256 MiB,
/// for the default limits; the system commits only what sessions come to use at once.
pub const fn default_memory_chunks(connections: usize, pool_chunks: usize) -> usize {
    (rung(connections) + connections) * pinc_transport::stream::store::floor_chunks(pool_chunks)
}

impl Limits {
    /// The chunks of the endpoint's store these limits give.
    pub fn store_chunks(&self) -> usize {
        self.memory_chunks
            .unwrap_or_else(|| default_memory_chunks(self.connections, self.pool_chunks))
    }

    /// Check the limits against the ceilings.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) naming the limit that is out of range.
    pub fn check(&self) -> Result<()> {
        let ok = (1..=MAX_CONNECTIONS).contains(&self.connections)
            && (8..=65_535).contains(&self.pool_chunks)
            && self.spill_slots <= 65_536
            && (rung(self.connections) * pinc_transport::stream::store::floor_chunks(self.pool_chunks)
                ..=u32::MAX as usize)
                .contains(&self.store_chunks())
            && (16 * 1024..=16 * 1024 * 1024).contains(&self.stream_window)
            && (16 * 1024..=1 << 30).contains(&self.send_window)
            && (1..=STREAMS / 2).contains(&usize::from(self.streams))
            && self.accept_streams >= 1
            && self.accept_sessions >= 1
            && (1..=16 * 1024 * 1024).contains(&self.topic_message)
            && (1..=1 << 30).contains(&self.topic_log)
            && (1..=4096).contains(&self.topics);
        if ok {
            Ok(())
        } else {
            Err(Error::config("a limit is out of range"))
        }
    }
}

/// The capacity of the endpoint built for `connections` sessions: the smallest rung of [`CAPACITIES`] that holds them.
/// The store keeps a floor for every slot of it.
const fn rung(connections: usize) -> usize {
    let mut rest: &[usize] = &crate::CAPACITIES;
    while let [k, tail @ ..] = rest {
        if *k >= connections {
            return *k;
        }
        rest = tail;
    }
    connections
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_pool_of_more_chunks_than_a_stream_ring_can_name_is_refused() {
        let limits = |pool_chunks| Limits {
            pool_chunks,
            ..Limits::default()
        };
        assert!(limits(65_535).check().is_ok());
        assert!(limits(65_536).check().is_err());
    }

    #[test]
    fn a_topic_log_is_between_one_byte_and_one_gibibyte() {
        let limits = |topic_log| Limits {
            topic_log,
            ..Limits::default()
        };
        assert!(limits(16 << 20).check().is_ok());
        assert!(limits(1 << 30).check().is_ok());
        assert!(limits(0).check().is_err());
        assert!(limits((1 << 30) + 1).check().is_err());
    }
}
