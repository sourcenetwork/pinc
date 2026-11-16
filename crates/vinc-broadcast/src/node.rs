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

use crate::behind::Behind;
use crate::consts::{
    DEFAULT_LOG_BYTES, DEFAULT_MAX_BODY, DEFAULT_MAX_SUBSCRIBERS, DEFAULT_MAX_TOPICS, DEFAULT_REACH_BYTES, GAP_EVERY,
    HAVE_MAX, MAX_TOPIC, QUEUE_CAP, SEEN_CAP,
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
    /// The bytes a hub's adjacency table holds (see [`Topics::set_adjacent`]). Each record is charged
    /// [`REACH_RECORD_BASE`](crate::consts::REACH_RECORD_BASE), 32 bytes per peer it names and its signature; a
    /// tombstone the base alone. [`ReachStats::bytes`](crate::ReachStats::bytes) is the charge now. A record that
    /// does not fit is refused: a new node's, and the table closes (while it is closed every node without a record
    /// counts as alone; it opens again once every node it refused has a record, was revoked or was released); or a
    /// newer record of a node it holds one of, which then keeps a tombstone and is alone until a record of it fits.
    /// The refused nodes it remembers are bounded by the records the bytes could hold. It must hold at least one
    /// record's fixed share.
    pub reach_bytes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_body: DEFAULT_MAX_BODY,
            log_bytes: DEFAULT_LOG_BYTES,
            max_topics: DEFAULT_MAX_TOPICS,
            max_subscribers: DEFAULT_MAX_SUBSCRIBERS,
            reach_bytes: DEFAULT_REACH_BYTES,
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
            && self.reach_bytes >= crate::consts::REACH_RECORD_BASE
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
    /// As many publishes as the node tracks are still waiting for a hub to acknowledge them, or, on a hub, the topic's
    /// log cannot take the message without evicting one its subscribers are still owed.
    Backlog,
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
            Self::Backlog => "as many publishes as the node tracks are waiting for a hub; publish again later",
        })
    }
}

impl core::error::Error for Refused {}

/// The state of one topic.
#[derive(Debug)]
#[allow(clippy::struct_excessive_bools, reason = "independent facts about one topic")]
pub(crate) struct Topic {
    /// This node subscribes to the topic.
    pub(crate) sub: bool,
    /// Member: a hub's subscriber set listed this node since it last subscribed.
    pub(crate) confirmed: bool,
    /// Hub: subscribed members; the flag is false while a member's subscriptions are held.
    pub(crate) subs: BTreeMap<NodeId, bool>,
    /// Hub: the subscribers the other hubs reported.
    pub(crate) rsubs: BTreeMap<NodeId, Vec<NodeId>>,
    /// Hub: members that published to the topic, told the subscribers.
    pub(crate) pubs: BTreeSet<NodeId>,
    /// Member: the subscribers a hub reported, for the member-to-member fallback.
    pub(crate) peers: Vec<NodeId>,
    /// Member: the hub whose whole list `peers` was built from; only its deltas apply.
    pub(crate) peers_from: Option<NodeId>,
    /// Member: the version of `peers` (the hub's incarnation and list number); `None` while it waits for a whole list.
    pub(crate) peers_ver: Option<(u64, u32)>,
    /// Member: `peers` was cut to this member's `max_subscribers`, so it lacks ids the hub's list has past the cut.
    pub(crate) peers_cut: bool,
    /// Member: join hints, nodes taken as subscribers beside the hub's list; at most `max_subscribers`, none of them
    /// in `peers`. A hint leaves when a hub's list names it and when the topic is left.
    pub(crate) hints: Vec<NodeId>,
    /// Hub: the list last told the recipients (see `subs`).
    pub(crate) told: Vec<NodeId>,
    /// Hub: the number of `told`, raised by one at every change; with the incarnation it is the list's version.
    pub(crate) told_seq: u32,
    /// Hub: recipients that may not hold `told`, owed the whole list.
    pub(crate) stale: BTreeSet<NodeId>,
    /// Hub: the message log.
    pub(crate) log: Option<HubLog>,
    /// Hub: the subscribers whose stream had no room, each with its place in the log (see [`Behind`]). Such a
    /// subscriber is pushed nothing new: it is served from that place, in order.
    pub(crate) behind: BTreeMap<NodeId, Behind>,
    /// Hub: the span in which it stopped serving subscribers it still owed something, because their sessions ended
    /// (its wall clock): from when the earliest message it owed one of them was logged, to when it last forgot such
    /// a place. A subscription that asks for the topic from inside the span is not offered that message, and is
    /// told (`gap.rs`). One span for the topic, however many subscribers: it only ever widens.
    pub(crate) forgot: Option<(u64, u64)>,
    pub(crate) seen: Seen,
    /// Ids a gap repair asked for and has not received.
    pub(crate) requested: BTreeSet<[u8; 8]>,
    /// Member: a message of the topic found no room to wait for an access answer and was left unseen; the hub is
    /// asked for the topic again once there is room (`msg.rs`).
    pub(crate) refused: bool,
}

impl Topic {
    fn new() -> Self {
        Self {
            sub: false,
            confirmed: false,
            subs: BTreeMap::new(),
            rsubs: BTreeMap::new(),
            pubs: BTreeSet::new(),
            peers: Vec::new(),
            peers_from: None,
            peers_ver: None,
            peers_cut: false,
            hints: Vec::new(),
            told: Vec::new(),
            told_seq: 0,
            stale: BTreeSet::new(),
            log: None,
            behind: BTreeMap::new(),
            forgot: None,
            seen: Seen::with_capacity(SEEN_CAP),
            requested: BTreeSet::new(),
            refused: false,
        }
    }

    /// The hub owed a subscriber something of this topic logged at `from_ms` or later (0: something the log no
    /// longer holds, or a notice) and can no longer send it: its session ended at `wall_ms`.
    pub(crate) fn note_forgot(&mut self, from_ms: u64, wall_ms: u64) {
        self.forgot = Some(
            self.forgot
                .map_or((from_ms, wall_ms), |(f, a)| (f.min(from_ms), a.max(wall_ms))),
        );
    }

    /// Whether a subscription asking for the topic from `since_ms` is not offered something the hub owed a
    /// subscriber whose session ended: it asks from after that message was logged, and from before the hub forgot.
    pub(crate) fn forgot_since(&self, since_ms: u64) -> bool {
        self.forgot.is_some_and(|(from, at)| from < since_ms && since_ms <= at)
    }

    /// Forget `peer`'s place in the log because its session ended at `wall_ms`. What it was owed from there is no
    /// longer sent, so the span is kept; a place that owed nothing leaves none.
    pub(crate) fn forget_place(&mut self, peer: &NodeId, wall_ms: u64) {
        let Some(b) = self.behind.remove(peer) else { return };
        let from = match self.log.as_ref() {
            Some(log) if !b.lost && b.next >= log.base() => log.wall_at(b.next),
            _ => Some(0),
        };
        if let Some(from) = from {
            self.note_forgot(from, wall_ms);
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
    /// The hub's stream had no room for it, so nothing was sent yet: it goes out when the stream has room again
    /// ([`Topics::peer_writable`]), or at its next retry.
    pub(crate) unsent: bool,
}

/// A message set aside until a decision arrives: `topic_len | topic | body`.
#[derive(Debug)]
pub(crate) struct Held {
    pub(crate) mid: [u8; 8],
    pub(crate) origin: NodeId,
    pub(crate) hop: NodeId,
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
    /// How many of `pending` are [`Pending::unsent`]. While it is not zero a new publish waits behind them.
    pub(crate) unsent: usize,
    /// Hub: a publish of its own found no room in a log; the latest instant at which the application is told to
    /// publish again (a subscriber that stalls can be let go by then). It is told sooner when a subscriber moves on.
    pub(crate) room_at: Option<Nanos>,
    pub(crate) acp: BTreeMap<NodeId, (bool, Nanos)>,
    pub(crate) checks: Vec<(u32, NodeId)>,
    pub(crate) next_check: u32,
    pub(crate) held: Vec<Held>,
    pub(crate) revoked: BTreeSet<NodeId>,
    pub(crate) sent: SentFloors,
    /// Hub: the subscribers that are behind in some topic (see [`Topic::behind`]).
    pub(crate) lagging: BTreeSet<NodeId>,
    /// Hub: every recipient whose stream refused a subscriber list, so that it may be stale in some topic (a superset
    /// of the `stale` sets; see `subs`). At most the recipients of every topic.
    pub(crate) owed: BTreeSet<NodeId>,
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
    /// The adjacency records and the components they make (see `reach.rs`).
    pub(crate) reach: crate::reach::Reach,
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
    pub fn start(
        cfg: &Config<'_>,
        key: alloc::boxed::Box<Keypair>,
        now: Nanos,
        wall_ms: u64,
    ) -> Result<Self, StartError> {
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
        let mut unscoped = hubs.clone();
        if cfg.is_hub {
            unscoped.push(cfg.me);
        }
        Ok(Self {
            me: cfg.me,
            is_hub: cfg.is_hub,
            hubs,
            limits: cfg.limits,
            key,
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
            unsent: 0,
            room_at: None,
            acp: BTreeMap::new(),
            checks: Vec::new(),
            next_check: 1,
            held: Vec::new(),
            revoked: BTreeSet::new(),
            sent: SentFloors::default(),
            lagging: BTreeSet::new(),
            owed: BTreeSet::new(),
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
            reach: crate::reach::Reach::new(unscoped, cfg.limits.reach_bytes),
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

    /// How many of them wait for room in a hub's stream and were not sent yet.
    pub const fn unsent_len(&self) -> usize {
        self.unsent
    }

    /// Take the pending publish at `i` out of the table.
    pub(crate) fn take_pending(&mut self, i: usize) -> Pending {
        let p = self.pending.remove(i);
        self.unsent -= usize::from(p.unsent);
        p
    }

    /// Whether a hub holds subscriptions for `member` that are live (`Some(true)`), held (`Some(false)`) or absent.
    pub fn sub_state(&self, topic: &[u8], member: &NodeId) -> Option<bool> {
        self.topics.get(topic).and_then(|t| t.subs.get(member)).copied()
    }

    /// The subscribers a hub reported for `topic`, for the member-to-member fallback: that hub's list at the version
    /// this node holds, cut to this node's limit. Join hints are beside it ([`Topics::hinted_subscribers`]).
    pub fn known_subscribers(&self, topic: &[u8]) -> &[NodeId] {
        self.topics.get(topic).map_or(&[], |t| t.peers.as_slice())
    }

    /// The join hints taken for `topic` that no hub's list names (yet), which the fallback sends to as well as to
    /// [`Topics::known_subscribers`]; no node is in both.
    pub fn hinted_subscribers(&self, topic: &[u8]) -> &[NodeId] {
        self.topics.get(topic).map_or(&[], |t| t.hints.as_slice())
    }

    /// Take `member` as a subscriber of `topic` that this node may send to straight when no hub is reachable (a join
    /// hint). It is kept beside the hub's list, which a hint never enters: that list is the hub's at its version, which
    /// later changes are applied to. A hub's list that names the node covers it, and the hint is dropped. Hints are
    /// bounded by `max_subscribers`: when they are full a new one is refused (false), the kept ones stay. False also
    /// if the topic table is full.
    pub fn hint(&mut self, topic: &[u8], member: &NodeId) -> bool {
        if *member == self.me || !self.ensure_topic(topic) {
            return false;
        }
        let max = self.limits.max_subscribers;
        let Some(st) = self.topics.get_mut(topic) else {
            return false;
        };
        if st.peers.contains(member) || st.hints.contains(member) {
            return true;
        }
        if st.hints.len() >= max {
            return false;
        }
        st.hints.push(*member);
        true
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

    /// Trust `peer` again; whether it was revoked.
    pub fn unrevoke(&mut self, peer: &NodeId) -> bool {
        self.revoked.remove(peer)
    }

    /// Stop trusting `peer`: forget its subscriptions and refuse its messages.
    pub fn revoke(&mut self, peer: &NodeId) {
        if self.revoked.len() < crate::consts::TABLE_MAX {
            self.revoked.insert(*peer);
        }
        for t in self.topics.values_mut() {
            t.subs.remove(peer);
            t.behind.remove(peer);
            t.pubs.remove(peer);
        }
        self.lagging.remove(peer);
        self.reach.forget(peer);
    }
}
