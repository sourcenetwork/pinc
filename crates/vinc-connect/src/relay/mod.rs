//! The relay side: carrier sessions, forwarding, records, lookup, address discovery, hub tunnel, sleep notices and
//! the mailbox, as one SANS-IO state machine.
//!
//! A [`Relay`] is driven by the host. The host owns the sockets and the protected carriers
//! ([`crate::carrier::ProtectedCarrier`]); it reports what happened (a carrier opened, a frame arrived, a datagram
//! arrived, time passed) and the relay answers through the [`Sink`] the host passes to the call: every effect
//! ([`Effect`]) is something for the host to do, and every state transition is also reported as a [`Trace`] event, in
//! order, so a run can be replayed and checked against the formal models.
//!
//! Invariants:
//! - **Authenticated peers only.** A carrier session exists only for a node the carrier handshake authenticated, and
//!   forwarded packets and replicated records are accepted only from a node id in the set of authenticated peer
//!   relays ([`Relay::add_peer`]); anything else is [`Reject::Unauthenticated`].
//! - **Signed records only.** A record is stored only after its signature and key binding verified, a publisher may
//!   publish only its own record, and a stored record is exactly the published one (a replica is the same bytes).
//! - **The relay never reads relayed content.** Packets pass as opaque bytes; only their length is looked at.
//! - **Bounded.** Every table has a compile-time capacity; per-node byte and time limits ([`Quota`]) bound what one
//!   node can relay; the mailbox bounds bytes and age per member and counts every drop.
//! - **No loops.** A packet that arrived from a peer relay is never forwarded to another relay.
//! - Nothing allocates, reads a clock or a random source, or panics.

pub mod clients;
pub mod datagram;
pub mod discovery;
pub mod records;
pub mod route;
pub mod sleep;
pub mod table;

use core::net::SocketAddr;

use vinc_crypto::NodeId;

use crate::carrier::frame::{Frame, FrameError};
use crate::mailbox::{self, Mailbox};
use crate::record::RecordError;
use datagram::{Datagram, DatagramError};
use records::RecordStore;
use sleep::SleepError;
use table::{Cache, Table};

pub use clients::{NodeState, SessionId};

/// The numbers the relay rules use, in nanoseconds unless stated.
pub mod rule {
    /// A record is republished every 1800 s.
    pub const RECORD_REPUBLISH_NS: u64 = 1_800_000_000_000;
    /// A stored record not refreshed within three republish periods is dropped.
    pub const RECORD_TTL_NS: u64 = 3 * RECORD_REPUBLISH_NS;
    /// Replies to a forwarded node go back through the forwarding relay for 30 s.
    pub const FWD_BACK_NS: u64 = 30_000_000_000;
    /// A member carrier silent for this long also gets a copy of each packet over its UDP session.
    pub const TUNNEL_STALE_NS: u64 = 15_000_000_000;
    /// A member's UDP session carries tunnel packets if it was heard within this time.
    pub const HUB_TUNNEL_FRESH_NS: u64 = 20_000_000_000;
    /// A sleep notice this close before a carrier close marks the close as a suspension.
    pub const SLEEP_WIN_NS: u64 = 10_000_000_000;
    /// A node that lost its carrier stays known as gone this long.
    pub const GONE_TTL_NS: u64 = 600_000_000_000;
    /// A woken-up member that still has held messages is signalled again after this long.
    pub const WAKE_REARM_NS: u64 = 30_000_000_000;
    /// The relay pings every client carrier this often.
    pub const CLIENT_PING_NS: u64 = 600_000_000_000;
    /// The relay sweeps its tables at most this often.
    pub const SWEEP_NS: u64 = 1_000_000_000;
    /// The most authenticated peer relays.
    pub const MAX_PEERS: usize = 32;
}

/// The per-node limits of CMP-CON-03, as configuration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Quota {
    /// Bytes of packets a node may send through this relay per [`Quota::window_ns`].
    pub bytes: u64,
    /// The length of one byte-limit window.
    pub window_ns: u64,
    /// The longest a carrier session may stay open; the relay closes it after that (the node redials).
    pub session_ns: u64,
}

impl Quota {
    /// 32 MiB per minute, and sessions of 24 hours.
    pub const DEFAULT: Self = Self {
        bytes: 32 << 20,
        window_ns: 60_000_000_000,
        session_ns: 86_400_000_000_000,
    };
}

impl Default for Quota {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// How a relay is configured.
#[derive(Debug, Clone, Copy)]
pub struct Config {
    /// This relay's node id.
    pub me: NodeId,
    /// The limits applied to every carrier session.
    pub quota: Quota,
    /// How long the mailbox holds a message.
    pub mailbox_max_age_ns: u64,
    /// Keys every table's hash; choose it at random once per process.
    pub seed: u64,
}

impl Config {
    /// A configuration with the default quota and a one-day mailbox age.
    pub const fn new(me: NodeId, seed: u64) -> Self {
        Self {
            me,
            quota: Quota::DEFAULT,
            mailbox_max_age_ns: 86_400_000_000_000,
            seed,
        }
    }
}

/// Where a UDP control datagram goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UdpTarget {
    /// Back to the address that sent the request.
    Reply(SocketAddr),
    /// Down the validated UDP session with this member.
    Member(NodeId),
}

/// Why the relay asks the host to close a carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CloseReason {
    /// The session reached the time limit of the quota.
    SessionTime,
    /// The same node opened a newer carrier.
    Replaced,
}

/// Something for the host to do.
#[derive(Debug, Clone, Copy)]
pub enum Effect<'a> {
    /// Write a frame on a member's carrier.
    Carrier {
        /// The member.
        to: NodeId,
        /// The frame.
        frame: Frame<'a>,
    },
    /// Write a frame on the authenticated session with a peer relay.
    PeerRelay {
        /// The peer relay.
        to: NodeId,
        /// The frame.
        frame: Frame<'a>,
    },
    /// Send a UDP datagram.
    Udp {
        /// Where.
        to: UdpTarget,
        /// What.
        datagram: Datagram<'a>,
    },
    /// A packet for the relay's own endpoint.
    Local {
        /// The node it came from.
        from: NodeId,
        /// The packet.
        packet: &'a [u8],
    },
    /// Close a carrier.
    Close {
        /// The member.
        node: NodeId,
        /// The session to close.
        session: SessionId,
        /// Why.
        reason: CloseReason,
    },
    /// Forward a wake-up to the push service for this member.
    Wake {
        /// The member to wake.
        node: NodeId,
    },
    /// A state transition, for tracing.
    Trace(Trace),
}

/// Where the host receives effects.
pub trait Sink {
    /// Take one effect.
    fn emit(&mut self, effect: Effect<'_>);

    /// Whether the host can send a datagram to member `node` over its session's validated direct route now. The relay
    /// asks when it routes, so a packet it tunnels is one the host can send and, if not, takes the next rule. A sink
    /// that stands for no sessions of its own (a test collector) says yes.
    fn tunnel_ready(&self, _node: &NodeId) -> bool {
        true
    }
}

/// How a packet was routed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Route {
    /// To the relay's own endpoint.
    Local,
    /// To a member's open carrier.
    Carrier,
    /// Down a member's UDP session.
    Tunnel,
    /// To another relay.
    Peer,
    /// Into the mailbox of a sleeping member.
    Mailbox,
}

/// Where a stored record came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecordOrigin {
    /// The node published it on its carrier.
    Publish,
    /// A peer relay replicated it.
    Replica,
    /// This relay's own record.
    Own,
}

/// Why the relay refused an input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reject {
    /// The sender is not an authenticated peer relay, or a tunnelled packet came from no authenticated member.
    Unauthenticated,
    /// A frame that this sender may not send.
    UnexpectedFrame,
    /// An alias that names no node.
    UnknownAlias,
    /// The carrier session is not the node's current one.
    StaleSession,
    /// The node used up its byte limit for this window.
    Quota,
    /// The session table is full.
    SessionsFull,
    /// No route: the destination has no record, or its home relay is this one but it is not here.
    NoRoute,
    /// The home relay of the destination has no authenticated session with this relay.
    NoPeerSession,
    /// The packet cannot be tunnelled (too large for a datagram, or no fresh UDP session ready to send on). A held
    /// message that hit it stays held.
    NoTunnel,
    /// The record store is full of live records.
    StoreFull,
    /// A record that is malformed or whose signature does not verify.
    BadRecord(RecordError),
    /// A record older than the stored one.
    StaleRecord,
    /// A node tried to publish a record that is not its own.
    WrongOwner,
    /// A sleep notice that was refused.
    BadSleep(SleepError),
    /// A datagram that does not decode.
    BadDatagram(DatagramError),
    /// A frame that does not encode.
    BadFrame(FrameError),
    /// The mailbox refused the packet.
    MailboxRefused,
}

/// A state transition of the relay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trace {
    /// A member's carrier session opened.
    CarrierOpened {
        /// The member.
        node: NodeId,
        /// The session.
        session: SessionId,
    },
    /// A member's carrier session ended; `asleep` says a sleep notice came just before.
    CarrierClosed {
        /// The member.
        node: NodeId,
        /// Whether the close is a suspension.
        asleep: bool,
    },
    /// A session reached its time limit.
    SessionExpired {
        /// The member.
        node: NodeId,
    },
    /// A node's frame was dropped for the byte limit.
    QuotaExceeded {
        /// The member.
        node: NodeId,
    },
    /// A packet was routed.
    Routed {
        /// The source.
        src: NodeId,
        /// The destination.
        dst: NodeId,
        /// How.
        route: Route,
        /// The packet length.
        bytes: usize,
    },
    /// A reply route was learnt: replies to `node` go through relay `via`.
    FwdBackLearned {
        /// The forwarded node.
        node: NodeId,
        /// The relay that forwarded its packets.
        via: NodeId,
    },
    /// An input was refused.
    Rejected {
        /// Why.
        reason: Reject,
        /// The node it came from, when known.
        node: Option<NodeId>,
    },
    /// A record was stored.
    RecordStored {
        /// The publisher.
        node: NodeId,
        /// Its sequence number.
        seq: u64,
        /// Where it came from.
        origin: RecordOrigin,
    },
    /// This relay's own record was sent to its peers again.
    Republished {
        /// How many peers.
        peers: usize,
    },
    /// A lookup was answered.
    LookupServed {
        /// The node looked up.
        peer: NodeId,
        /// Whether a record was found.
        found: bool,
    },
    /// An address discovery query was answered.
    QadAnswered,
    /// A sleep notice was accepted.
    SleepAccepted {
        /// The sleeping node.
        node: NodeId,
    },
    /// A carrier keepalive probe arrived (evidence of life for the sessions riding this carrier).
    Pulse {
        /// The member.
        node: NodeId,
    },
    /// A packet went into the mailbox.
    MailboxStored {
        /// The sleeping member.
        node: NodeId,
        /// The message's sequence number.
        seq: u64,
        /// How many older messages the quota pushed out.
        dropped: u32,
    },
    /// A held packet was handed to the returning member.
    MailboxDelivered {
        /// The member.
        node: NodeId,
        /// The message's sequence number.
        seq: u64,
    },
    /// A wake-up was requested for a member.
    WakeRequested {
        /// The member.
        node: NodeId,
    },
}

/// Counters of what the relay did.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    /// Packets delivered to a member carrier.
    pub carrier: u64,
    /// Packets tunnelled down a UDP session.
    pub tunnel: u64,
    /// Packets forwarded to a peer relay.
    pub peer: u64,
    /// Packets for the relay's own endpoint.
    pub local: u64,
    /// Packets put into the mailbox.
    pub mailboxed: u64,
    /// Inputs refused.
    pub rejected: u64,
    /// Frames dropped for the byte limit.
    pub quota_drops: u64,
    /// Records stored (published or replicated).
    pub records: u64,
    /// Lookups answered.
    pub lookups: u64,
    /// Address discovery queries answered.
    pub qad: u64,
}

#[derive(Debug)]
pub(crate) struct FwdBack {
    pub(crate) relay: NodeId,
    pub(crate) at: u64,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Sleeper {
    pub(crate) at: u64,
    pub(crate) woke: u64,
}

/// A relay with room for `C` member sessions, `R` stored records and a mailbox of `MN` members of `MB` bytes each.
#[derive(Debug)]
pub struct Relay<const C: usize, const R: usize, const MN: usize, const MB: usize> {
    pub(crate) cfg: Config,
    pub(crate) clients: Table<clients::Client, C>,
    pub(crate) gone: Table<u64, C>,
    pub(crate) sleeping: Table<Sleeper, C>,
    pub(crate) udp: Table<u64, C>,
    // vertexia: direct-mapped, so a collision forgets the older reply route (it is a 30 s hint); an ordered table
    // would keep the newest entries instead
    pub(crate) fwd_back: Cache<FwdBack, C>,
    pub(crate) peers: [Option<NodeId>; rule::MAX_PEERS],
    pub(crate) records: RecordStore<R>,
    pub(crate) mailbox: Mailbox<MN, MB>,
    pub(crate) next_session: u64,
    pub(crate) next_publish: u64,
    pub(crate) last_sweep: u64,
    pub(crate) next_ping: u64,
    pub(crate) stats: Stats,
}

impl<const C: usize, const R: usize, const MN: usize, const MB: usize> Relay<C, R, MN, MB> {
    /// A relay with no sessions, records or peers.
    pub fn new(cfg: Config) -> Self {
        Self {
            cfg,
            clients: Table::new(cfg.seed),
            gone: Table::new(cfg.seed),
            sleeping: Table::new(cfg.seed),
            udp: Table::new(cfg.seed),
            fwd_back: Cache::new(cfg.seed),
            peers: [None; rule::MAX_PEERS],
            records: RecordStore::new(cfg.seed),
            mailbox: Mailbox::new(cfg.mailbox_max_age_ns, cfg.seed),
            next_session: 0,
            next_publish: 0,
            last_sweep: 0,
            next_ping: 0,
            stats: Stats::default(),
        }
    }

    /// This relay's node id.
    pub const fn me(&self) -> &NodeId {
        &self.cfg.me
    }

    /// The counters.
    pub const fn stats(&self) -> Stats {
        self.stats
    }

    /// The mailbox counters.
    pub const fn mailbox_stats(&self) -> mailbox::Stats {
        self.mailbox.stats()
    }

    /// Messages and bytes the mailbox holds for `node`.
    pub fn mailbox_pending(&self, node: &NodeId) -> (usize, usize) {
        self.mailbox.pending(node)
    }

    /// Members with packets held in the mailbox.
    pub const fn mailbox_members(&self) -> usize {
        self.mailbox.members()
    }

    /// The `index`th packet held for `node`, oldest first: its body goes into `buf`; the header and the time it
    /// arrived come back. A host keeps these across a restart and gives them back with [`Relay::restore_held`].
    pub fn held_packet(
        &self,
        node: &NodeId,
        index: usize,
        buf: &mut [u8; crate::carrier::frame::MAX_PACKET_LEN],
    ) -> Option<(mailbox::Delivered, u64)> {
        self.mailbox.peek(node, index, buf)
    }

    /// Put back a packet for `node` that arrived at `at` and was kept across a restart. Restore a member's packets
    /// oldest first; one older than the mailbox's maximum age is refused.
    ///
    /// # Errors
    /// [`Reject::MailboxRefused`] if the packet is expired, empty, too long, or no member slot is free.
    pub fn restore_held(
        &mut self,
        now: u64,
        at: u64,
        node: &NodeId,
        src: &NodeId,
        flag: u8,
        body: &[u8],
    ) -> Result<(), Reject> {
        if now.saturating_sub(at) >= self.cfg.mailbox_max_age_ns {
            return Err(Reject::MailboxRefused);
        }
        match self.mailbox.restore(now, at, node, src, flag, body) {
            mailbox::Push::Stored { .. } => Ok(()),
            mailbox::Push::TooLarge | mailbox::Push::NoSlot => Err(Reject::MailboxRefused),
        }
    }

    /// The time the stored record of `node` was received or last restored, if one is stored (it ends
    /// [`rule::RECORD_TTL_NS`] later unless refreshed).
    pub fn record_received(&self, node: &NodeId) -> Option<u64> {
        self.records.get(node).map(|s| s.received)
    }

    /// How many records are stored.
    pub const fn record_count(&self) -> usize {
        self.records.len()
    }

    /// Record `relay` as an authenticated peer relay: call it when a protected carrier handshake to or from this
    /// node id completed and the node is one this relay's operator trusts as a relay. Returns false if the set is
    /// full.
    pub fn add_peer(&mut self, relay: NodeId) -> bool {
        if self.is_peer(&relay) {
            return true;
        }
        self.peers.iter_mut().find(|p| p.is_none()).is_some_and(|slot| {
            *slot = Some(relay);
            true
        })
    }

    /// Forget a peer relay (its session ended).
    pub fn remove_peer(&mut self, relay: &NodeId) {
        for slot in &mut self.peers {
            if slot.as_ref() == Some(relay) {
                *slot = None;
            }
        }
    }

    /// Whether `node` is an authenticated peer relay.
    pub fn is_peer(&self, node: &NodeId) -> bool {
        self.peers.iter().flatten().any(|p| p == node)
    }

    pub(crate) fn reject<S: Sink>(&mut self, sink: &mut S, reason: Reject, node: Option<NodeId>) -> Reject {
        self.stats.rejected += 1;
        sink.emit(Effect::Trace(Trace::Rejected { reason, node }));
        reason
    }
}
