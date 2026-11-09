//! The node's trace: every decision of its host-side duties, in order, together with the records of the layers it
//! composes, as one stream with a version.
//!
//! A [`TraceItem`] is a plain value: the node's time and a [`Body`]. The node's own decisions ([`NodeTrace`]) have a
//! stable ndjson form with named fields ([`TraceItem::write_ndjson`], version [`TRACE_VERSION`]); the records of the
//! membership and broadcast machines and of the endpoint are carried as they are, typed, in the order they were
//! produced, so a proof replays one interleaved run.
//!
//! Invariants: the queue holds at most [`QUEUE_CAP`] items and counts what it drops, delivering the count as
//! [`NodeTrace::Lost`] before the next item; a node built without tracing queues nothing.

use alloc::collections::VecDeque;
use alloc::string::String;
use core::fmt;

use vinc_membership::NodeId;

use crate::config::Nanos;

/// The version of the record format; it changes when a field is renamed, removed or re-typed.
pub const TRACE_VERSION: u32 = 1;
/// The most items queued between two polls.
pub const QUEUE_CAP: usize = 8192;

/// The first four bytes of a node id as a number, enough to tell the nodes of one run apart.
pub fn tag(id: &NodeId) -> u64 {
    let [a, b, c, d, ..] = *id;
    u64::from(u32::from_be_bytes([a, b, c, d]))
}

/// A decision of the node's own duties.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeTrace {
    /// The node started as a hub (1) or a member (0).
    Started {
        /// 1 for a hub.
        hub: u64,
    },
    /// A hub stream session with this peer came up.
    SessionUp {
        /// The peer's tag.
        peer: u64,
        /// 1 if the peer dialed.
        incoming: u64,
    },
    /// A hub stream session with this peer ended with this close code.
    SessionDown {
        /// The peer's tag.
        peer: u64,
        /// The close code, 0 if the session ended without one.
        code: u64,
    },
    /// A dial of this peer started.
    Dial {
        /// The peer's tag.
        peer: u64,
    },
    /// A dial failed or its session ended early; the next dial waits.
    Backoff {
        /// The peer's tag.
        peer: u64,
        /// How long, in milliseconds.
        wait_ms: u64,
        /// 1 if the peer's access check refused us.
        denied: u64,
    },
    /// A second session of this peer was closed because the peer already has one.
    DuplicateClosed {
        /// The peer's tag.
        peer: u64,
    },
    /// A hub adopted another live session of this member after its newer one closed.
    Adopted {
        /// The member's tag.
        peer: u64,
    },
    /// A session without our write stream got a fresh stream.
    StreamRepaired {
        /// The peer's tag.
        peer: u64,
    },
    /// The watchdog closed a hub session that kept timing out and received nothing.
    Watchdog {
        /// The hub's tag.
        peer: u64,
    },
    /// A stream broke the framing and was reset.
    StreamReset {
        /// The peer's tag.
        peer: u64,
    },
    /// A member's relay carrier to this hub opened (1) or closed (0).
    Carrier {
        /// The member's tag.
        member: u64,
        /// 1 for open.
        open: u64,
    },
    /// A peer was revoked and every session with it closed.
    Revoked {
        /// The peer's tag.
        peer: u64,
        /// How many sessions were closed.
        sessions: u64,
    },
    /// The node left the group.
    Left,
    /// This many items were dropped because the queue was full.
    Lost {
        /// How many.
        count: u64,
    },
}

impl NodeTrace {
    const fn name(&self) -> &'static str {
        match self {
            Self::Started { .. } => "started",
            Self::SessionUp { .. } => "session_up",
            Self::SessionDown { .. } => "session_down",
            Self::Dial { .. } => "dial",
            Self::Backoff { .. } => "backoff",
            Self::DuplicateClosed { .. } => "duplicate_closed",
            Self::Adopted { .. } => "adopted",
            Self::StreamRepaired { .. } => "stream_repaired",
            Self::Watchdog { .. } => "watchdog",
            Self::StreamReset { .. } => "stream_reset",
            Self::Carrier { .. } => "carrier",
            Self::Revoked { .. } => "revoked",
            Self::Left => "left",
            Self::Lost { .. } => "lost",
        }
    }

    fn fields(&self) -> ([(&'static str, u64); 3], usize) {
        let z = ("", 0);
        match *self {
            Self::Started { hub } => ([("hub", hub), z, z], 1),
            Self::SessionUp { peer, incoming } => ([("peer", peer), ("incoming", incoming), z], 2),
            Self::SessionDown { peer, code } => ([("peer", peer), ("code", code), z], 2),
            Self::Dial { peer }
            | Self::DuplicateClosed { peer }
            | Self::Adopted { peer }
            | Self::StreamRepaired { peer }
            | Self::Watchdog { peer }
            | Self::StreamReset { peer } => ([("peer", peer), z, z], 1),
            Self::Backoff { peer, wait_ms, denied } => ([("peer", peer), ("wait_ms", wait_ms), ("denied", denied)], 3),
            Self::Carrier { member, open } => ([("member", member), ("open", open), z], 2),
            Self::Revoked { peer, sessions } => ([("peer", peer), ("sessions", sessions), z], 2),
            Self::Left => ([z, z, z], 0),
            Self::Lost { count } => ([("count", count), z, z], 1),
        }
    }
}

/// What a trace item holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Body {
    /// A decision of the node's duties.
    Node(NodeTrace),
    /// A record of the membership machine.
    Membership(vinc_membership::Trace),
    /// A record of the broadcast machine.
    Broadcast(vinc_broadcast::Trace),
    /// A record of the endpoint.
    Core(vinc_core::TraceRecord),
}

/// One trace record with the time of the call that produced it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TraceItem {
    /// The node's time in nanoseconds.
    pub t: Nanos,
    /// The record.
    pub body: Body,
}

impl TraceItem {
    /// Write the item as one line of ndjson: `{"v":..,"t":..,"layer":"..","ev":"..",<fields>}`. The records of the
    /// layers below are written with their `Debug` text in `rec`, which is for reading, not for proofs: proofs take the
    /// typed [`Body`].
    ///
    /// # Errors
    /// The writer's error.
    pub fn write_ndjson(&self, out: &mut impl fmt::Write) -> fmt::Result {
        write!(out, "{{\"v\":{TRACE_VERSION},\"t\":{}", self.t)?;
        match &self.body {
            Body::Node(n) => {
                write!(out, ",\"layer\":\"node\",\"ev\":\"{}\"", n.name())?;
                let (fields, k) = n.fields();
                for (name, value) in fields.iter().take(k) {
                    write!(out, ",\"{name}\":{value}")?;
                }
            }
            Body::Membership(m) => write!(out, ",\"layer\":\"membership\",\"rec\":\"{m:?}\"")?,
            Body::Broadcast(b) => write!(out, ",\"layer\":\"broadcast\",\"rec\":\"{b:?}\"")?,
            Body::Core(c) => {
                let mut line = String::new();
                c.write_ndjson(&mut line)?;
                write!(out, ",\"layer\":\"core\",\"rec\":{}", line.trim_end())?;
            }
        }
        out.write_str("}\n")
    }
}

/// The bounded queue of items.
#[derive(Debug)]
pub(crate) struct TraceQueue {
    on: bool,
    q: VecDeque<TraceItem>,
    lost: u64,
}

impl TraceQueue {
    pub(crate) fn new(on: bool) -> Self {
        Self {
            on,
            q: VecDeque::new(),
            lost: 0,
        }
    }

    pub(crate) const fn on(&self) -> bool {
        self.on
    }

    pub(crate) fn push(&mut self, t: Nanos, body: Body) {
        if !self.on {
            return;
        }
        if self.q.len() >= QUEUE_CAP {
            self.lost = self.lost.saturating_add(1);
        } else {
            self.q.push_back(TraceItem { t, body });
        }
    }

    pub(crate) fn pop(&mut self, now: Nanos) -> Option<TraceItem> {
        if self.lost > 0 && self.q.len() < QUEUE_CAP {
            let count = core::mem::take(&mut self.lost);
            self.q.push_front(TraceItem {
                t: now,
                body: Body::Node(NodeTrace::Lost { count }),
            });
        }
        self.q.pop_front()
    }
}
