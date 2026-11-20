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
//! The endpoint reserves room for every slot of its shape when it is built: the table of slots, one per session the
//! shape holds, and the tables that look sessions up. The system commits that room only as it is written. A slot's own
//! memory is made when the slot is first taken, and kept for the sessions that follow in it: a stream table of
//! [`STREAMS`] entries (an entry is a few KiB with a [`RING`] of 257 chunk entries, written when its stream is first
//! used), the table of sent packets, the event queue, and a pool of up to [`Limits::pool_chunks`] chunks of 16 KiB. The
//! pool makes a chunk when the session first needs it and keeps it while the session is busy; when the session's last
//! stream ends it frees its idle chunks, so a quiet session holds what it uses, on any allocator. A session that moved
//! 64 KiB and went quiet holds about 96 KiB of the client's memory, and a client endpoint with no session about 620
//! KiB (`tests/pinc_client_memory.rs` holds them to 112 and 704 KiB). The shape is rounded up to the next capacity of
//! the ladder, which doubles at each step: ask for what you need, not for a round number above it.
//!
//! The most the limits allow an endpoint to come to hold is the number of sessions of the shape, each with a full pool
//! and every table of its slot written, plus every topic's log full and every slot of the spill arena written.
//! [`Limits::check`] refuses limits whose most exceeds half the target's address space, which is as much as one
//! allocation can be; a 64-bit target accepts every limit in range, a 32-bit one needs fewer sessions or a smaller pool
//! ([`Limits::wasm`]). The measured memory of an
//! endpoint and of a session without `std` is in the crate's own docs, with the platform it was measured on.
//!
//! Invariants: the memory of a session returns to its slot when the session ends; the slot table never grows.

use pinc_core::{Endpoint, Slot};
use pinc_crypto::Software;
use pinc_transport::conn::Resources;
use pinc_transport::stream::pool::CHUNK_SIZE;

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

/// The bytes one slot of the shape reserves beside its pool's chunks: the slot, with its connection, and what its
/// stream table, table of sent packets and event queue reserve when every entry is written. Taken from the real types.
const SLOT_BYTES: usize = size_of::<Slot<'static, Software, crate::Body, STREAMS, RING, FLIGHT, PATHS>>()
    + Resources::<'static, crate::Body, STREAMS, RING, FLIGHT>::BYTES;

/// The bytes of one slot of the endpoint's spill arena.
const SPILL_SLOT: usize = size_of::<pinc_transport::stream::spill::SpillSlot>();

/// The sizes a driver runs with; each has a default and a hard ceiling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The most sessions at once (at most [`MAX_CONNECTIONS`]). The room for the next capacity of
    /// [`CAPACITIES`](crate::CAPACITIES) at or above it is reserved when the engine starts, and a slot's memory is made
    /// when a session first takes it; see the module docs for what that costs.
    pub connections: usize,
    /// The 16 KiB chunks one session may hold for its streams and datagrams (8 to 65,535). The default of 1024 is 16 MiB,
    /// a ceiling: the pool makes a chunk as a session needs it, a busy session holds the chunks it came to use and a
    /// quiet one (no stream open) only those still in use, so thousands of quiet sessions hold little whatever the
    /// ceiling. Streams that move data at once are charged
    /// their whole window, so a path whose bandwidth times round trip is above half the pool needs more.
    pub pool_chunks: usize,
    /// The slots of the endpoint's spill arena (0 to 65,536; default 128, 1 MiB): when a stream's ranges (received,
    /// lost or acknowledged) outgrow the few it keeps inline, under scattered loss, they move into one 8 KiB slot until
    /// they shrink to half of inline again. The arena is allocated once with the endpoint, commits a slot's memory the
    /// first time it is used, and is shared by every session, each holding at most half of it. With no slot free a
    /// received frame that needs one more range is refused and sent again by the peer, and a lost range is widened or
    /// sent again; 0 turns spilling off.
    pub spill_slots: usize,
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

impl Limits {
    /// What every session gets, on any target; a host's preset changes only how many sessions it holds.
    const BASE: Self = Self {
        connections: 1024,
        pool_chunks: 1024,
        spill_slots: pinc_transport::stream::spill::DEFAULT_SLOTS,
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
    };

    /// The limits for a host with a 32-bit address space, a browser first: every session gets what the default gives
    /// it, and only the number of sessions is lower, 64 (and as many waiting to be accepted). The default of 1024
    /// sessions cannot be addressed there and [`check`](Self::check) refuses it. The most these limits allow an
    /// endpoint to hold is about 1.7 GiB (1 GiB of pools, 512 MiB of topic logs and 64 slots of about 2.7 MiB), under
    /// the 2 GiB such a host can address; a host with less memory lowers `connections` and `pool_chunks` further.
    #[must_use]
    pub const fn wasm() -> Self {
        Self {
            connections: 64,
            accept_sessions: 64,
            ..Self::BASE
        }
    }

    /// Check the limits against the ceilings, and against what the target can address.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) naming a limit that is out of range, or saying the limits allow
    /// more memory than this target can address.
    pub fn check(&self) -> Result<()> {
        self.check_for(size_of::<usize>())
    }

    /// [`check`](Self::check) for a target whose pointers are `pointer_bytes` wide.
    fn check_for(&self, pointer_bytes: usize) -> Result<()> {
        let ok = (1..=MAX_CONNECTIONS).contains(&self.connections)
            && (8..=65_535).contains(&self.pool_chunks)
            && self.spill_slots <= 65_536
            && (16 * 1024..=16 * 1024 * 1024).contains(&self.stream_window)
            && (16 * 1024..=1 << 30).contains(&self.send_window)
            && (1..=STREAMS / 2).contains(&usize::from(self.streams))
            && self.accept_streams >= 1
            && self.accept_sessions >= 1
            && (1..=16 * 1024 * 1024).contains(&self.topic_message)
            && (1..=1 << 30).contains(&self.topic_log)
            && (1..=4096).contains(&self.topics);
        if !ok {
            return Err(Error::config("a limit is out of range"));
        }
        if !fits(self, u32::try_from(pointer_bytes).unwrap_or(u32::MAX)) {
            return Err(Error::config(
                "the limits allow more memory than this target can address: lower `connections` or `pool_chunks`, \
                 or start from `Limits::wasm()`",
            ));
        }
        Ok(())
    }
}

impl Default for Limits {
    fn default() -> Self {
        Self::BASE
    }
}

/// The most memory the limits allow the endpoint to come to hold, in bytes: every session of the shape with a full pool
/// and every table of its slot written, every topic's log full and every slot of the spill arena written. `None` if the
/// sum does not fit 128 bits.
fn worst_case(limits: &Limits) -> Option<u128> {
    let sessions = u128::try_from(crate::node::rung(limits.connections)?).ok()?;
    let pool = u128::try_from(limits.pool_chunks)
        .ok()?
        .checked_mul(CHUNK_SIZE as u128)?;
    let slot = pool.checked_add(SLOT_BYTES as u128)?;
    let logs = u128::try_from(limits.topics)
        .ok()?
        .checked_mul(u128::try_from(limits.topic_log).ok()?)?;
    let spill = u128::try_from(limits.spill_slots)
        .ok()?
        .checked_mul(SPILL_SLOT as u128)?;
    sessions.checked_mul(slot)?.checked_add(logs)?.checked_add(spill)
}

/// Whether the most memory the limits allow is at most half the address space of a target with `pointer_bytes`-wide
/// pointers, which is the most Rust lets one allocation be. Pure: the arithmetic is checked and in 128 bits, so a
/// 4-byte target is judged exactly on any host.
pub(crate) fn fits(limits: &Limits, pointer_bytes: u32) -> bool {
    let bits = pointer_bytes.saturating_mul(8).saturating_sub(1);
    let bound = 1u128.checked_shl(bits).map_or(u128::MAX, |b| b - 1);
    worst_case(limits).is_some_and(|w| w <= bound)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use alloc::string::ToString;

    use super::*;

    /// Half the address space of a 32-bit target, less one byte: the most one allocation can be there.
    const BOUND_4: u128 = (1 << 31) - 1;

    /// Every limit at its ceiling (the two that have none at a million).
    fn largest() -> Limits {
        Limits {
            connections: MAX_CONNECTIONS,
            pool_chunks: 65_535,
            spill_slots: 65_536,
            stream_window: 16 * 1024 * 1024,
            send_window: 1 << 30,
            streams: 100,
            accept_streams: 1 << 20,
            accept_sessions: 1 << 20,
            topic_message: 16 * 1024 * 1024,
            topic_log: 1 << 30,
            topics: 4096,
        }
    }

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

    #[test]
    fn with_8_byte_pointers_every_limit_set_in_range_fits() {
        assert!(fits(&largest(), 8));
        assert!(largest().check_for(8).is_ok());
        assert!(fits(&Limits::default(), 8));
    }

    #[test]
    fn the_default_limits_do_not_fit_4_byte_pointers_and_say_what_to_do() {
        assert!(!fits(&Limits::default(), 4));
        assert!(!fits(&largest(), 4));
        let e = Limits::default().check_for(4).unwrap_err();
        assert_eq!(e.kind(), crate::ErrorKind::Config);
        let said = e.to_string();
        assert!(said.contains("more memory than this target can address"), "{said}");
        assert!(said.contains("Limits::wasm()"), "{said}");
        // A limit out of range keeps its own sentence on any target.
        let bad = Limits {
            topics: 0,
            ..Limits::default()
        };
        assert_eq!(bad.check_for(4).unwrap_err().to_string(), "a limit is out of range");
        assert_eq!(bad.check().unwrap_err().to_string(), "a limit is out of range");
    }

    #[test]
    fn the_target_of_the_build_decides_check() {
        let wide = size_of::<usize>() == 8;
        assert_eq!(Limits::default().check().is_ok(), wide);
        assert_eq!(
            Limits::default().check().is_ok(),
            Limits::default().check_for(size_of::<usize>()).is_ok()
        );
    }

    #[test]
    fn the_wasm_limits_fit_both_widths_and_keep_what_a_session_gets() {
        let (w, d) = (Limits::wasm(), Limits::default());
        assert!(fits(&w, 4) && fits(&w, 8));
        assert!(w.check_for(4).is_ok() && w.check_for(8).is_ok() && w.check().is_ok());
        let sessions = Limits {
            connections: d.connections,
            accept_sessions: d.accept_sessions,
            ..w
        };
        assert_eq!(sessions, d);
        assert_eq!((w.connections, w.accept_sessions), (64, 64));
        let worst = worst_case(&w).unwrap();
        std::println!("wasm worst case: {worst} B, slot {SLOT_BYTES} B");
        assert!((1_700 << 20..1_800 << 20).contains(&worst), "{worst}");
    }

    #[test]
    fn sixty_four_is_the_largest_capacity_of_the_ladder_that_fits_4_byte_pointers() {
        let sessions = |connections| Limits {
            connections,
            ..Limits::wasm()
        };
        assert!(fits(&sessions(64), 4));
        assert!(!fits(&sessions(65), 4));
        assert!(!fits(&sessions(128), 4));
        assert!(fits(&sessions(128), 8));
    }

    #[test]
    fn the_bound_for_4_byte_pointers_is_exact() {
        let base = Limits {
            topics: 1,
            topic_log: 0,
            ..Limits::wasm()
        };
        let room = BOUND_4 - worst_case(&base).unwrap();
        let with = |log: u128| Limits {
            topic_log: usize::try_from(log).unwrap(),
            ..base
        };
        assert!(fits(&with(room), 4));
        assert!(!fits(&with(room + 1), 4));
        assert!(fits(&with(room + 1), 8));
    }

    #[test]
    fn the_rung_is_the_smallest_capacity_that_holds_the_sessions() {
        for (n, k) in [(1, 1), (2, 2), (3, 4), (65, 128), (1024, 1024), (65_536, 65_536)] {
            assert_eq!(crate::node::rung(n), Some(k), "{n}");
        }
        assert_eq!(crate::node::rung(65_537), None);
        assert!(!fits(
            &Limits {
                connections: 65_537,
                ..Limits::default()
            },
            8
        ));
    }

    #[test]
    fn a_pointer_width_of_nothing_fits_nothing() {
        assert!(!fits(&Limits::wasm(), 0));
    }

    /// The limits as the model's record: its field names are the model's, not the code's.
    fn jlimits(l: &Limits) -> alloc::string::String {
        alloc::format!(
            r#"{{"conn":{},"pool":{},"sw":{},"snd":{},"streams":{},"ast":{},"as":{},"tmsg":{},"tlog":{},"topics":{},"spill":{}}}"#,
            l.connections,
            l.pool_chunks,
            l.stream_window,
            l.send_window,
            l.streams,
            l.accept_streams,
            l.accept_sessions,
            l.topic_message,
            l.topic_log,
            l.topics,
            l.spill_slots
        )
    }

    /// A number as 15-bit limbs, lowest first (zero is none).
    fn limbs15(mut v: u128) -> alloc::string::String {
        let mut limbs = alloc::vec::Vec::new();
        while v > 0 {
            limbs.push(alloc::format!("{}", v & 0x7fff));
            v >>= 15;
        }
        alloc::format!("[{}]", limbs.join(","))
    }

    /// `worst_case`, `fits` and `check_for` written out again from their documentation, in plain 128-bit arithmetic.
    fn reference(l: &Limits, pb: u32) -> (Option<u128>, bool, &'static str) {
        let worst = (l.connections <= 65_536).then(|| {
            let rung = l.connections.next_power_of_two() as u128;
            rung * (l.pool_chunks as u128 * CHUNK_SIZE as u128 + SLOT_BYTES as u128)
                + l.topics as u128 * l.topic_log as u128
                + l.spill_slots as u128 * SPILL_SLOT as u128
        });
        let bits = (pb * 8).saturating_sub(1);
        let bound = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
        let fits = worst.is_some_and(|w| w <= bound);
        let in_range = (1..=65_536).contains(&l.connections)
            && (8..=65_535).contains(&l.pool_chunks)
            && (16 * 1024..=16 * 1024 * 1024).contains(&l.stream_window)
            && (16 * 1024..=1 << 30).contains(&l.send_window)
            && (1..=100).contains(&l.streams)
            && l.accept_streams >= 1
            && l.accept_sessions >= 1
            && (1..=16 * 1024 * 1024).contains(&l.topic_message)
            && (1..=1 << 30).contains(&l.topic_log)
            && (1..=4096).contains(&l.topics)
            && l.spill_slots <= 65_536;
        (
            worst,
            fits,
            if !in_range {
                "range"
            } else if !fits {
                "address"
            } else {
                "ok"
            },
        )
    }

    /// `worst_case`, `fits` and `check_for` of the cases of the operator's decision and of seeded limit sets, each
    /// checked against the plain reference and recorded for the trace check.
    #[test]
    fn trace_limits() {
        use core::fmt::Write as _;

        use crate::trace_util::{mix, write_trace};

        let base = Limits {
            topics: 1,
            topic_log: 0,
            ..Limits::wasm()
        };
        let room = BOUND_4 - worst_case(&base).unwrap();
        let with = |log: u128| Limits {
            topic_log: usize::try_from(log).unwrap(),
            ..base
        };
        let sessions = |connections| Limits {
            connections,
            ..Limits::wasm()
        };
        let mut cases: alloc::vec::Vec<(&str, Limits, u32)> = alloc::vec![
            ("default-4", Limits::default(), 4),
            ("default-8", Limits::default(), 8),
            ("largest-4", largest(), 4),
            ("largest-8", largest(), 8),
            ("wasm-4", Limits::wasm(), 4),
            ("wasm-8", Limits::wasm(), 8),
            ("wasm-64-4", sessions(64), 4),
            ("wasm-65-4", sessions(65), 4),
            ("wasm-128-4", sessions(128), 4),
            ("wasm-128-8", sessions(128), 8),
            ("room-4", with(room), 4),
            ("room1-4", with(room + 1), 4),
            ("room1-8", with(room + 1), 8),
            (
                "above-ladder-8",
                Limits {
                    connections: 65_537,
                    ..Limits::default()
                },
                8
            ),
            ("width-0", Limits::wasm(), 0),
        ];
        let mut seed = 3u64;
        let mut pick = |hi: u64| usize::try_from(mix(&mut seed) % hi).unwrap();
        for _ in 0..60 {
            let l = Limits {
                connections: pick(70_000),
                pool_chunks: pick(70_000),
                stream_window: 16 * 1024 + u64::try_from(pick(1 << 24)).unwrap(),
                send_window: 16 * 1024 + u64::try_from(pick(1 << 30)).unwrap(),
                streams: u16::try_from(pick(102)).unwrap(),
                accept_streams: pick(3),
                accept_sessions: pick(3),
                topic_message: 1 + pick(1 << 24),
                topic_log: pick(1 << 30),
                topics: pick(4100),
                spill_slots: pick(70_000),
            };
            let pb = u32::try_from(pick(10)).unwrap();
            cases.push(("", l, pb));
        }
        let mut out = alloc::string::String::new();
        for (name, l, pb) in &cases {
            let (worst, fits_ref, check_ref) = reference(l, *pb);
            assert_eq!(worst_case(l), worst, "{name}");
            assert_eq!(fits(l, *pb), fits_ref, "{name}");
            let check = match l.check_for(*pb as usize) {
                Ok(()) => "ok",
                Err(e) if e.to_string() == "a limit is out of range" => "range",
                Err(_) => "address",
            };
            assert_eq!(check, check_ref, "{name}");
            writeln!(
                out,
                r#"{{"name":"{name}","l":{},"pb":{pb},"slot":{SLOT_BYTES},"chunk":{CHUNK_SIZE},"sslot":{SPILL_SLOT},"wok":{},"worst":{},"fits":{},"check":"{check}"}}"#,
                jlimits(l),
                worst.is_some(),
                limbs15(worst.unwrap_or(0)),
                fits_ref
            )
            .unwrap();
        }
        assert!(
            cases.iter().any(|(_, l, pb)| l.check_for(*pb as usize).is_ok()),
            "no case passes"
        );
        assert!(cases.iter().any(|(_, l, pb)| !fits(l, *pb)), "no case is refused");
        write_trace("limits.ndjson", &out);
    }
}
