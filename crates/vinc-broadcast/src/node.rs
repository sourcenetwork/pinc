//! The topic machine: its state, its configuration and the tables every other module works on.
//!
//! One [`Topics`] runs on every node. A hub also keeps the topic logs and the subscriber tables. The machine reads
//! no clock and owns no socket: the host reports frames, timers and carrier events and answers through the
//! [`Host`] trait; the machine answers with frames, [`Event`]s and [`Trace`] records.
//!
//! Invariants: every table is bounded; a full table refuses the new entry instead of evicting; iteration over a
//! table that a step also mutates is avoided or done through disjoint fields; every collection is ordered, so two
//! runs with the same inputs take the same steps; the steady path (a message published, pushed, delivered) allocates
//! nothing once the topic's tables exist.

use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::vec::Vec;
use vinc_crypto::{IdentityAlg, Keypair};
use vinc_membership::{Nanos, NodeId};
use vinc_wire::hlc::Hlc;

use crate::consts::{
    DEFAULT_LOG_BYTES, DEFAULT_MAX_BODY, DEFAULT_MAX_SUBSCRIBERS, DEFAULT_MAX_TOPICS, GAP_EVERY, HAVE_MAX, MAX_TOPIC,
    QUEUE_CAP, SEEN_CAP,
};
use crate::event::Trace;
use crate::floors::{Gather, SentFloors};
use crate::log::HubLog;
use crate::table::Seen;

/// The size limits of a node. The defaults suit small messages; raise `max_body` (and `log_bytes` with it) for a
/// stack that broadcasts larger payloads. Data larger than any sensible limit belongs behind a reference: broadcast a
/// root or CID and fetch the bytes with `vinc-values`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The largest message body, in bytes.
    pub max_body: usize,
    /// The bytes of message data (heads and bodies) one topic log holds on a hub.
    pub log_bytes: usize,
    /// The most topics the node tracks.
    pub max_topics: usize,
    /// The most subscribers the node learns or announces per topic.
    pub max_subscribers: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_body: DEFAULT_MAX_BODY,
            log_bytes: DEFAULT_LOG_BYTES,
            max_topics: DEFAULT_MAX_TOPICS,
            max_subscribers: DEFAULT_MAX_SUBSCRIBERS,
        }
    }
}

impl Limits {
    /// The most bytes one frame can take: prefix, type, topic, head and body.
    pub(crate) const fn max_frame(&self) -> usize {
        4 + 2 + MAX_TOPIC + crate::wire::MAX_HEAD + self.max_body
    }

    fn valid(&self) -> bool {
        // A logged message is its head and body, and the whole of it must fit the ring.
        self.max_topics > 0
            && self.max_subscribers > 0
            && u16::try_from(self.max_subscribers).is_ok()
            && u32::try_from(self.max_body).is_ok()
            && self.max_body.saturating_add(crate::wire::MAX_HEAD) <= self.log_bytes
    }
}

/// How a node is set up.
#[derive(Debug, Clone, Copy)]
pub struct Config<'a> {
    /// This node.
    pub me: NodeId,
    /// This node is a hub.
    pub is_hub: bool,
    /// The hubs, in the order the host prefers on a tie. A hub's own id may be listed or left out.
    pub hubs: &'a [NodeId],
    /// The incarnation word of this life of the node (the membership incarnation). It must differ across restarts:
    /// message ids derive from it.
    pub incarnation: u64,
    /// Queue trace records for [`Topics::poll_trace`].
    pub trace: bool,
    /// The size limits.
    pub limits: Limits,
}

/// Why a node could not start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StartError {
    /// More hubs than the node supports.
    TooManyHubs,
    /// The key does not belong to this node id.
    KeyMismatch,
    /// The limits are unusable: a body (with its head) larger than the log ring, or a zero table.
    InvalidLimits,
}

impl core::fmt::Display for StartError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::TooManyHubs => "more hubs than the node supports",
            Self::KeyMismatch => "the signing key is not the key of this node id",
            Self::InvalidLimits => {
                "the limits are unusable: the log must hold a full message and no table may be empty"
            }
        })
    }
}

impl core::error::Error for StartError {}

/// Why a publish, a subscription or an answer was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Refused {
    /// The topic is longer than 255 bytes.
    TopicTooLong,
    /// The body is larger than the configured limit.
    BodyTooLarge {
        /// The configured limit, in bytes.
        limit: usize,
    },
    /// The node tracks as many topics as it can.
    TopicsFull,
    /// The signature could not be produced.
    Sign,
}

impl core::fmt::Display for Refused {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Self::BodyTooLarge { limit } = self {
            return write!(
                f,
                "the message body is larger than the configured limit of {limit} bytes; send large data by reference"
            );
        }
        f.write_str(match self {
            Self::BodyTooLarge { .. } => "",
            Self::TopicTooLong => "the topic is longer than 255 bytes",

            Self::TopicsFull => "the node tracks as many topics as it can",
            Self::Sign => "the message could not be signed",
        })
    }
}

impl core::error::Error for Refused {}

/// The state of one topic.
#[derive(Debug)]
pub(crate) struct Topic {
    /// This node subscribes to the topic.
    pub(crate) sub: bool,
    /// Hub: subscribed members; the flag is false while a member's subscriptions are held.
    pub(crate) subs: BTreeMap<NodeId, bool>,
    /// Hub: the subscribers the other hubs reported.
    pub(crate) rsubs: BTreeMap<NodeId, Vec<NodeId>>,
    /// Hub: members that published to the topic, told the subscribers.
    pub(crate) pubs: BTreeSet<NodeId>,
    /// Member: the subscribers a hub reported, for the member-to-member fallback.
    pub(crate) peers: Vec<NodeId>,
    /// Hub: the message log.
    pub(crate) log: Option<HubLog>,
    pub(crate) seen: Seen,
    /// Ids a gap repair asked for and has not received.
    pub(crate) requested: BTreeSet<[u8; 8]>,
}

impl Topic {
    fn new() -> Self {
        Self {
            sub: false,
            subs: BTreeMap::new(),
            rsubs: BTreeMap::new(),
            pubs: BTreeSet::new(),
            peers: Vec::new(),
            log: None,
            seen: Seen::with_capacity(SEEN_CAP),
            requested: BTreeSet::new(),
        }
    }
}

/// A publish waiting for a hub to acknowledge it.
#[derive(Debug)]
pub(crate) struct Pending {
    pub(crate) mid: [u8; 8],
    /// `topic | head | body`.
    pub(crate) data: Vec<u8>,
    pub(crate) tlen: usize,
    pub(crate) hlen: usize,
    pub(crate) t0: Nanos,
    pub(crate) next_try: Nanos,
    pub(crate) idx: usize,
    /// Subscribers the fallback already sent it to.
    pub(crate) served: Vec<NodeId>,
}

/// A message set aside until a decision arrives: `topic_len | topic | body`.
#[derive(Debug)]
pub(crate) struct Held {
    pub(crate) mid: [u8; 8],
    pub(crate) origin: NodeId,
    pub(crate) ts: Hlc,
    pub(crate) data: Vec<u8>,
}

/// The topic machine. See the module docs.
// The `topics` table is the machine's namesake state.
#[allow(clippy::struct_field_names)]
#[derive(Debug)]
pub struct Topics {
    pub(crate) me: NodeId,
    pub(crate) is_hub: bool,
    pub(crate) hubs: Vec<NodeId>,
    pub(crate) limits: Limits,
    pub(crate) key: alloc::boxed::Box<Keypair>,
    pub(crate) alg: IdentityAlg,
    pub(crate) pk: Vec<u8>,
    pub(crate) inc: u64,
    pub(crate) seq: u64,
    pub(crate) born: Nanos,
    pub(crate) born_wall: u64,
    pub(crate) hlc: Hlc,
    pub(crate) primary: Option<NodeId>,
    pub(crate) topics: BTreeMap<Vec<u8>, Topic>,
    pub(crate) pending: Vec<Pending>,
    pub(crate) acp: BTreeMap<NodeId, (bool, Nanos)>,
    pub(crate) checks: Vec<(u32, NodeId)>,
    pub(crate) next_check: u32,
    pub(crate) held: Vec<Held>,
    pub(crate) revoked: BTreeSet<NodeId>,
    pub(crate) sent: SentFloors,
    pub(crate) gather: Gather,
    pub(crate) last_rx_wall: u64,
    /// The wall clock up to which every periodic check since the start reached back to the one before; starts at the
    /// start of the node.
    pub(crate) last_gap_wall: u64,
    pub(crate) next_ae: Nanos,
    pub(crate) next_gap: Nanos,
    pub(crate) scratch: Vec<u8>,
    pub(crate) ids: Vec<u8>,
    pub(crate) nodes: Vec<NodeId>,
    pub(crate) spare: Vec<Vec<u8>>,
    pub(crate) tq: TraceQueue,
}

/// The bounded queue of trace records.
#[derive(Debug)]
pub(crate) struct TraceQueue {
    on: bool,
    q: VecDeque<Trace>,
    lost: u32,
}

impl TraceQueue {
    /// Queue the record `t` builds, if tracing is on; a full queue counts the loss instead.
    pub(crate) fn push(&mut self, t: impl FnOnce() -> Trace) {
        if !self.on {
            return;
        }
        if self.q.len() >= QUEUE_CAP {
            self.lost = self.lost.saturating_add(1);
        } else {
            self.q.push_back(t());
        }
    }
}

impl Topics {
    /// Start a node at `now` (monotonic) with the wall clock `wall_ms`. `key` is the node's signing key.
    ///
    /// # Errors
    /// [`StartError`] for too many hubs or a key that is not the node's.
    pub fn start(cfg: &Config<'_>, key: Keypair, now: Nanos, wall_ms: u64) -> Result<Self, StartError> {
        let mut hubs: Vec<NodeId> = Vec::with_capacity(cfg.hubs.len());
        for h in cfg.hubs {
            if *h != cfg.me && !hubs.contains(h) {
                hubs.push(*h);
            }
        }
        if hubs.len() > vinc_membership::consts::MAX_HUBS {
            return Err(StartError::TooManyHubs);
        }
        if !cfg.limits.valid() {
            return Err(StartError::InvalidLimits);
        }
        let alg = key.alg();
        if key.node_id().bytes != cfg.me {
            return Err(StartError::KeyMismatch);
        }
        let mut pk = alloc::vec![0u8; alg.public_key_len()];
        key.public_key(&mut pk).map_err(|_| StartError::KeyMismatch)?;
        Ok(Self {
            me: cfg.me,
            is_hub: cfg.is_hub,
            hubs,
            limits: cfg.limits,
            key: alloc::boxed::Box::new(key),
            alg,
            pk,
            inc: cfg.incarnation,
            seq: 0,
            born: now,
            born_wall: wall_ms,
            hlc: Hlc::new(wall_ms, 0),
            primary: cfg.is_hub.then_some(cfg.me),
            topics: BTreeMap::new(),
            pending: Vec::new(),
            acp: BTreeMap::new(),
            checks: Vec::new(),
            next_check: 1,
            held: Vec::new(),
            revoked: BTreeSet::new(),
            sent: SentFloors::default(),
            gather: Gather::new(cfg.is_hub),
            last_rx_wall: 0,
            last_gap_wall: wall_ms,
            next_ae: now,
            next_gap: now.saturating_add(GAP_EVERY),
            scratch: Vec::with_capacity(cfg.limits.max_frame()),
            ids: Vec::with_capacity(8 * HAVE_MAX),
            nodes: Vec::with_capacity(cfg.limits.max_subscribers),
            spare: Vec::new(),
            tq: TraceQueue {
                on: cfg.trace,
                q: if cfg.trace {
                    VecDeque::with_capacity(QUEUE_CAP)
                } else {
                    VecDeque::new()
                },
                lost: 0,
            },
        })
    }

    /// Whether this node is a hub.
    pub const fn is_hub(&self) -> bool {
        self.is_hub
    }

    /// The hub this node subscribes through.
    pub const fn primary(&self) -> Option<&NodeId> {
        self.primary.as_ref()
    }

    /// How many topics the node tracks.
    pub fn topic_count(&self) -> usize {
        self.topics.len()
    }

    /// Whether this node subscribes to `topic`.
    pub fn is_subscribed(&self, topic: &[u8]) -> bool {
        self.topics.get(topic).is_some_and(|t| t.sub)
    }

    /// How many messages a hub logs for `topic`.
    pub fn log_len(&self, topic: &[u8]) -> usize {
        self.topics
            .get(topic)
            .and_then(|t| t.log.as_ref())
            .map_or(0, HubLog::len)
    }

    /// How many publishes still wait for an acknowledgement.
    pub fn pending_len(&self) -> usize {
        self.pending.len()
    }

    /// Whether a hub holds subscriptions for `member` that are live (`Some(true)`), held (`Some(false)`) or absent.
    pub fn sub_state(&self, topic: &[u8], member: &NodeId) -> Option<bool> {
        self.topics.get(topic).and_then(|t| t.subs.get(member)).copied()
    }

    /// The subscribers a node knows for `topic`, for the member-to-member fallback.
    pub fn known_subscribers(&self, topic: &[u8]) -> &[NodeId] {
        self.topics.get(topic).map_or(&[], |t| t.peers.as_slice())
    }

    /// The next trace record.
    pub fn poll_trace(&mut self) -> Option<Trace> {
        if self.tq.lost > 0 && self.tq.q.len() < QUEUE_CAP {
            let count = core::mem::take(&mut self.tq.lost);
            self.tq.q.push_back(Trace::Lost { count });
        }
        self.tq.q.pop_front()
    }

    pub(crate) fn trace(&mut self, t: impl FnOnce() -> Trace) {
        self.tq.push(t);
    }

    pub(crate) fn is_boot(&self, id: &NodeId) -> bool {
        self.hubs.contains(id)
    }

    pub(crate) fn any_hub_up<H: crate::host::Host>(&self, h: &H) -> bool {
        self.hubs.iter().any(|x| h.hub_up(x))
    }

    /// The state of `topic`, created if the table has room.
    pub(crate) fn topic(&mut self, topic: &[u8]) -> Option<&mut Topic> {
        if !self.topics.contains_key(topic) {
            if self.topics.len() >= self.limits.max_topics {
                return None;
            }
            self.topics.insert(topic.to_vec(), Topic::new());
        }
        self.topics.get_mut(topic)
    }

    /// Make sure `topic` has state; false if the table is full.
    pub(crate) fn ensure_topic(&mut self, topic: &[u8]) -> bool {
        self.topic(topic).is_some()
    }

    /// Lay `topic_len | topic | body` into `out`; false for a topic over 255 bytes.
    pub(crate) fn pack(out: &mut Vec<u8>, topic: &[u8], body: &[u8]) -> bool {
        let Ok(tl) = u8::try_from(topic.len()) else {
            return false;
        };
        out.clear();
        out.push(tl);
        out.extend_from_slice(topic);
        out.extend_from_slice(body);
        true
    }

    /// Split what [`Topics::pack`] laid out.
    pub(crate) fn unpack(data: &[u8]) -> Option<(&[u8], &[u8])> {
        let (&tl, rest) = data.split_first()?;
        rest.split_at_checked(usize::from(tl))
    }

    /// A cleared buffer from the pool, or a new one.
    pub(crate) fn take_buf(&mut self) -> Vec<u8> {
        self.spare.pop().unwrap_or_default()
    }

    /// Return a buffer to the pool.
    pub(crate) fn give_buf(&mut self, mut b: Vec<u8>) {
        b.clear();
        if self.spare.len() < crate::consts::PENDING_MAX {
            self.spare.push(b);
        }
    }

    /// Advance the clock for a message from `remote`, unless it claims a time too far ahead of ours.
    pub(crate) fn observe(&mut self, remote: Hlc, wall_ms: u64) {
        if remote.wall <= wall_ms.saturating_add(crate::consts::HLC_DRIFT_MS) {
            self.hlc = self.hlc.observe(remote, wall_ms);
        }
    }

    /// Stop trusting `peer`: forget its subscriptions and refuse its messages.
    pub fn revoke(&mut self, peer: &NodeId) {
        if self.revoked.len() < crate::consts::TABLE_MAX {
            self.revoked.insert(*peer);
        }
        for t in self.topics.values_mut() {
            t.subs.remove(peer);
            t.pubs.remove(peer);
        }
    }
}
