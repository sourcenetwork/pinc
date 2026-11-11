//! What an operator reads from a running relay: counters and a bounded queue of events.
//!
//! Nothing here carries packet content or key material. A node id is a public identifier and may appear.

use alloc::collections::VecDeque;

use vinc_connect::mailbox;
use vinc_connect::relay::{Reject, Stats as MachineStats};
use vinc_crypto::NodeId;

use crate::carrier::CarrierKind;

/// Why the relay refused an input, as a counter index. One per reason of the state machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum Reason {
    /// The sender is not an authenticated peer relay, or a tunnelled packet came from no authenticated member.
    Unauthenticated,
    /// A frame that this sender may not send.
    UnexpectedFrame,
    /// An alias that names no node.
    UnknownAlias,
    /// A frame for a carrier session that is no longer the node's current one.
    StaleSession,
    /// The node used up its byte limit for the window.
    Quota,
    /// The session table is full.
    SessionsFull,
    /// The destination has no record, or it is not here.
    NoRoute,
    /// The home relay of the destination has no session with this relay.
    NoPeerSession,
    /// The packet cannot be tunnelled.
    NoTunnel,
    /// The record store is full of live records.
    StoreFull,
    /// A record that is malformed or whose signature does not verify.
    BadRecord,
    /// A record older than the stored one.
    StaleRecord,
    /// A node tried to publish a record that is not its own.
    WrongOwner,
    /// A sleep notice that was refused.
    BadSleep,
    /// A datagram that does not decode.
    BadDatagram,
    /// A frame that does not encode.
    BadFrame,
    /// The mailbox refused the packet.
    MailboxRefused,
}

impl Reason {
    /// How many reasons there are.
    pub const COUNT: usize = 17;

    pub(crate) const fn of(r: Reject) -> Self {
        match r {
            Reject::Unauthenticated => Self::Unauthenticated,
            Reject::UnexpectedFrame => Self::UnexpectedFrame,
            Reject::UnknownAlias => Self::UnknownAlias,
            Reject::StaleSession => Self::StaleSession,
            Reject::Quota => Self::Quota,
            Reject::SessionsFull => Self::SessionsFull,
            Reject::NoRoute => Self::NoRoute,
            Reject::NoPeerSession => Self::NoPeerSession,
            Reject::NoTunnel => Self::NoTunnel,
            Reject::StoreFull => Self::StoreFull,
            Reject::BadRecord(_) => Self::BadRecord,
            Reject::StaleRecord => Self::StaleRecord,
            Reject::WrongOwner => Self::WrongOwner,
            Reject::BadSleep(_) => Self::BadSleep,
            Reject::BadDatagram(_) => Self::BadDatagram,
            Reject::BadFrame(_) => Self::BadFrame,
            Reject::MailboxRefused => Self::MailboxRefused,
        }
    }
}

/// Why a carrier ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Closed {
    /// The peer closed the stream or the stream failed.
    Peer,
    /// The handshake or a record failed, or the peer broke the framing.
    Protocol,
    /// The handshake did not finish in time.
    HandshakeTimeout,
    /// The peer sent nothing for the idle limit.
    Idle,
    /// The carrier did not drain its queue within the backlog limit.
    Slow,
    /// The session reached the time limit of the quota.
    SessionTime,
    /// The same node opened a newer carrier.
    Replaced,
    /// A carrier that asked for the peer relay protocol came from a node that is not a listed peer.
    Untrusted,
    /// The relay has as many carriers as its limit allows.
    Full,
    /// The relay stopped.
    Shutdown,
}

/// Something that happened, for an operator to log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Event {
    /// A node's carrier is up.
    CarrierUp {
        /// The node.
        node: NodeId,
        /// How its bytes travel.
        kind: CarrierKind,
    },
    /// A carrier ended; `node` is `None` if it never finished its handshake.
    CarrierDown {
        /// The node, if it was authenticated.
        node: Option<NodeId>,
        /// Why.
        why: Closed,
    },
    /// An input was refused.
    Refused {
        /// Why.
        reason: Reason,
        /// The node it came from, if known.
        node: Option<NodeId>,
    },
    /// A record was stored.
    RecordStored {
        /// The publisher.
        node: NodeId,
        /// Its sequence number.
        seq: u64,
    },
    /// A member asleep should be woken: forward this to the push service of the deployment.
    Wake {
        /// The member.
        node: NodeId,
    },
    /// The store failed to keep or load a record.
    StoreFailed,
}

/// The counters of a relay. Every field counts since the relay was built.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Stats {
    /// Authenticated member carriers up now.
    pub carriers: usize,
    /// Times the run loop woke.
    pub wakes: u64,
    /// Streams the run loop looked at, summed over its passes (the cost of a wake grows with the streams).
    pub stream_polls: u64,
    /// Peer relays with a carrier up now.
    pub peers_up: usize,
    /// Dials of a peer relay that failed to open the stream.
    pub peer_dial_failures: u64,
    /// Carriers that finished their handshake.
    pub carriers_opened: u64,
    /// Carriers that ended, by any cause.
    pub carriers_closed: u64,
    /// Carriers whose handshake or records failed.
    pub protocol_failures: u64,
    /// Carriers closed for not draining their queue.
    pub slow_closed: u64,
    /// Carriers closed for silence or for not finishing their handshake.
    pub timed_out: u64,
    /// Carriers refused because the relay already holds as many as its limit allows.
    pub refused_carriers_full: u64,
    /// Streams refused as accepted because too many carriers were still in their handshake.
    pub refused_handshakes_full: u64,
    /// Failed accepts.
    pub accept_errors: u64,
    /// Datagrams received.
    pub datagrams_in: u64,
    /// Datagrams sent.
    pub datagrams_out: u64,
    /// Datagrams that could not be sent: the queue was full or the socket failed.
    pub datagrams_dropped: u64,
    /// Packets for the relay's own endpoint, or from it, that had nowhere to go (no hub is configured).
    pub hub_dropped: u64,
    /// Members with a UDP session to the relay's hub now.
    pub hub_sessions: usize,
    /// Records stored now.
    pub records: usize,
    /// Records the store failed to keep.
    pub store_errors: u64,
    /// Events dropped because nobody read them.
    pub events_dropped: u64,
    /// Inputs refused, by [`Reason`] (index with `reason as usize`).
    pub refused: [u64; Reason::COUNT],
    /// What the state machine counted: packets delivered, records stored, lookups, address queries.
    pub machine: MachineStats,
    /// What the mailbox counted.
    pub mailbox: mailbox::Stats,
    /// Sleeping members whose packets the mailbox holds now.
    pub mailbox_members: usize,
}

impl Stats {
    /// How many inputs were refused for `reason`.
    pub fn refused(&self, reason: Reason) -> u64 {
        self.refused.get(reason as usize).copied().unwrap_or(0)
    }
}

/// The counters the host loop keeps itself; [`Stats`] adds the state machine's.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Counters {
    pub(crate) peer_dial_failures: u64,
    pub(crate) wakes: u64,
    pub(crate) stream_polls: u64,
    pub(crate) carriers_opened: u64,
    pub(crate) carriers_closed: u64,
    pub(crate) protocol_failures: u64,
    pub(crate) slow_closed: u64,
    pub(crate) timed_out: u64,
    pub(crate) refused_carriers_full: u64,
    pub(crate) refused_handshakes_full: u64,
    pub(crate) accept_errors: u64,
    pub(crate) datagrams_in: u64,
    pub(crate) datagrams_out: u64,
    pub(crate) datagrams_dropped: u64,
    pub(crate) hub_dropped: u64,
    pub(crate) store_errors: u64,
    pub(crate) events_dropped: u64,
    pub(crate) refused: [u64; Reason::COUNT],
}

/// A bounded queue of events; the oldest are dropped and counted.
#[derive(Debug)]
pub(crate) struct Events {
    queue: VecDeque<Event>,
    cap: usize,
}

impl Events {
    pub(crate) fn new(cap: usize) -> Self {
        Self {
            queue: VecDeque::with_capacity(cap),
            cap,
        }
    }

    /// Queue `e`; returns whether an older event was dropped to make room.
    pub(crate) fn push(&mut self, e: Event) -> bool {
        let dropped = self.queue.len() >= self.cap && self.queue.pop_front().is_some();
        self.queue.push_back(e);
        dropped
    }

    pub(crate) fn pop(&mut self) -> Option<Event> {
        self.queue.pop_front()
    }
}
