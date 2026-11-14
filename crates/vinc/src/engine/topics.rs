//! Topics on the core: joining and leaving, publishing, the neighbours of a topic and the events about them.
//!
//! The node runs broadcast through hubs; the core turns its messages into [`Event`]s, derives the neighbours of a topic
//! (the members the node knows for it that this endpoint has a session with) and tells when they change, and keeps the
//! deadlines of the futures that wait for one.
//!
//! Invariants: the event queue holds at most [`EVENTS`] events and counts what it drops; the topics joined are
//! bounded by the node's topic limit; a neighbour is reported up once and down once per change of the set.

use std::collections::BTreeMap;

use vinc_core::Role;
use vinc_crypto::NodeId;
use vinc_keystore::KeyStore;
use vinc_node::{HUB_ALPN, NodeEvent};

use super::{Admit, Core, Direction, GKey, Try, Wait};
use crate::addr::NodeAddr;
use crate::error::{Error, ErrorKind, Result};
use crate::event::{Event, MessageId};

/// The most events queued for the host.
const EVENTS: usize = 1024;
/// The most join hints one call takes.
const HINTS: usize = 16;
/// How often the neighbours are looked at while a topic is joined or a future waits for one, in nanoseconds.
const LOOK: u64 = 500_000_000;
/// With connected topics, the least time between two records naming this endpoint's peers, in nanoseconds.
pub(super) const ADJ_GAP: u64 = 250_000_000;

impl<S: KeyStore, A: Admit> Core<S, A> {
    /// One event of the node: the endpoint's go to the sessions, the others become events for the host.
    pub(super) fn on_node_event(&mut self, now: u64, ev: NodeEvent) {
        match ev {
            NodeEvent::Endpoint(e) => {
                self.tap(&e);
                self.on_event(now, e);
            }
            NodeEvent::Message {
                topic,
                origin,
                hop,
                body,
                ..
            } => {
                let (origin, hop) = (self.node.full_id(&origin), self.node.full_id(&hop));
                self.push_event(Event::Message {
                    topic,
                    origin,
                    hop,
                    direct: origin == hop,
                    payload: body,
                });
            }
            NodeEvent::BroadcastAcpCheck { id, origin, .. } => {
                let origin = self.node.full_id(&origin);
                let allow = self.admit.admit(&origin, HUB_ALPN, Direction::Gossip);
                self.node.broadcast_acp_answer(now, id, allow);
                self.dirty = true;
            }
            NodeEvent::ReachRefused { origin } => {
                let node = self.node.full_id(&origin);
                self.push_event(Event::ReachRefused { node });
            }
            NodeEvent::Subscribed { hub, topic } => {
                if self.topics.contains_key(&topic) {
                    let hub = self.node.full_id(&hub);
                    self.push_event(Event::Joined { topic, hub });
                }
            }
            NodeEvent::ReachClosed => self.push_event(Event::ReachClosed),
            NodeEvent::ReachOpened => self.push_event(Event::ReachOpened),
            NodeEvent::Member(_) => self.neighbors_dirty = true,
            NodeEvent::Connect(n) => self.on_notice(&n),
            NodeEvent::Lost { count } => {
                self.lost = self.lost.saturating_add(count);
                // An event of a session may be among them: the neighbours are worked out from the sessions again.
                self.neighbors_dirty = true;
            }
            NodeEvent::PublishAcked { .. } | NodeEvent::PublishGaveUp { .. } | NodeEvent::PublishRoom => {
                self.wake_g(GKey::Publish);
            }
            _ => {}
        }
    }

    fn push_event(&mut self, e: Event) {
        if self.events.len() >= EVENTS {
            self.lost = self.lost.saturating_add(1);
        } else {
            self.events.push_back(e);
        }
        self.wake_g(GKey::Events);
    }

    /// The next event, or `None` once the endpoint stopped and the queue is empty, else a wait.
    pub(crate) fn poll_event(&mut self) -> Try<Option<Event>> {
        if self.lost > 0 {
            let count = std::mem::take(&mut self.lost);
            return Try::Done(Some(Event::Lost { count }));
        }
        match self.events.pop_front() {
            Some(e) => Try::Done(Some(e)),
            None if self.stopped.is_some() => Try::Done(None),
            None => Try::Wait(Wait::G(GKey::Events)),
        }
    }

    /// Join `topic`, and dial the peers of `hints` as its neighbours. Whether the topic was new.
    pub(crate) fn join(&mut self, now: u64, topic: &[u8], hints: &[NodeAddr]) -> Result<bool> {
        self.running()?;
        self.node.subscribe(now, topic).map_err(refused)?;
        let new = !self.topics.contains_key(topic);
        if new {
            self.topics.insert(topic.to_vec(), Vec::new());
        }
        for hint in hints.iter().take(HINTS) {
            self.hint(now, topic, hint);
        }
        self.neighbors_dirty = true;
        self.dirty = true;
        Ok(new)
    }

    fn hint(&mut self, now: u64, topic: &[u8], hint: &NodeAddr) {
        for a in &hint.direct {
            self.add_address(hint.node, *a);
        }
        if !self.node.hint_subscriber(topic, &hint.node.bytes) || self.hub_sessions.values().any(|p| *p == hint.node) {
            return;
        }
        let mut addrs = hint.direct.clone();
        addrs.extend(self.book.get(&hint.node).into_iter().flatten().copied());
        // A refused dial is retried by the node when it sends to the peer.
        let _ = self.node.dial(now, hint.node, HUB_ALPN, Role::Other, &addrs);
    }

    /// Leave `topic`; whether it was joined.
    pub(crate) fn leave(&mut self, now: u64, topic: &[u8]) -> bool {
        let was = self.topics.remove(topic).is_some();
        if was {
            self.node.unsubscribe(now, topic);
            self.dirty = true;
        }
        was
    }

    /// Publish `body` to `topic`, or a wait while the node has no room for it: as a member, while it tracks as many
    /// publishes as it can (room returns when a hub acknowledges one or one is given up); as a hub, while the topic's
    /// log is full of messages subscribers are still owed (the node says when to publish again).
    pub(crate) fn publish(&mut self, now: u64, topic: &[u8], body: &[u8]) -> Try<Result<MessageId>> {
        if let Err(e) = self.running() {
            return Try::Done(Err(e));
        }
        match self.node.publish(now, topic, body) {
            Ok(mid) => {
                self.dirty = true;
                Try::Done(Ok(mid))
            }
            Err(vinc_broadcast::Refused::Backlog) => Try::Wait(Wait::G(GKey::Publish)),
            Err(e) => Try::Done(Err(refused(e))),
        }
    }

    /// The members of `topic` this endpoint has a session with.
    pub(crate) fn neighbors(&self, topic: &[u8]) -> Vec<NodeId> {
        let present = self.present();
        let mut v: Vec<NodeId> = self
            .node
            .broadcast()
            .known_subscribers(topic)
            .iter()
            .filter_map(|b| present.get(b).copied())
            .filter(|p| !self.admit.is_revoked(p))
            .collect();
        v.sort_by_key(|n| n.bytes);
        v
    }

    /// Every peer with a session, by its short id.
    fn present(&self) -> BTreeMap<[u8; 32], NodeId> {
        self.sessions
            .values()
            .map(|s| s.info.node)
            .chain(self.hub_sessions.values().copied())
            .map(|n| (n.bytes, n))
            .collect()
    }

    /// Done when `topic` has a neighbour, timed out at `deadline`, else a wait.
    pub(crate) fn neighbor_wait(&mut self, topic: &[u8], deadline: u64, now: u64) -> Try<Result<()>> {
        if let Err(e) = self.running() {
            return Try::Done(Err(e));
        }
        if !self.neighbors(topic).is_empty() {
            return Try::Done(Ok(()));
        }
        if now >= deadline {
            return Try::Done(Err(Error::new(
                ErrorKind::TimedOut,
                "no member joined the topic in time",
            )));
        }
        self.deadlines.insert(deadline);
        Try::Wait(Wait::G(GKey::Topic))
    }

    /// Whether a future waits for a neighbour.
    fn waiting_for_neighbor(&self) -> bool {
        self.gwaits.iter().any(|(k, _)| *k == GKey::Topic)
    }

    /// When the neighbours are next looked at, if they need to be.
    pub(super) fn look_deadline(&self) -> Option<u64> {
        (!self.topics.is_empty() || self.waiting_for_neighbor()).then_some(self.look_at)
    }

    /// Look at the neighbours of the joined topics when something changed or the interval passed, report the changes
    /// and wake the futures that wait for a neighbour; fire the deadlines that passed.
    pub(super) fn look(&mut self, now: u64) {
        let mut woke = false;
        while let Some(d) = self.deadlines.first().copied().filter(|d| *d <= now) {
            self.deadlines.remove(&d);
            woke = true;
        }
        if now >= self.look_at {
            self.look_at = now.saturating_add(LOOK);
            self.neighbors_dirty = true;
        }
        if self.neighbors_dirty && (!self.topics.is_empty() || self.waiting_for_neighbor()) {
            self.neighbors_dirty = false;
            woke = true;
            let mut changes = Vec::new();
            let topics: Vec<Vec<u8>> = self.topics.keys().cloned().collect();
            for topic in topics {
                let current = self.neighbors(&topic);
                let Some(last) = self.topics.get_mut(&topic) else {
                    continue;
                };
                for p in current.iter().filter(|p| !last.contains(p)) {
                    changes.push(Event::NeighborUp {
                        topic: topic.clone(),
                        peer: *p,
                    });
                }
                for p in last.iter().filter(|p| !current.contains(p)) {
                    changes.push(Event::NeighborDown {
                        topic: topic.clone(),
                        peer: *p,
                    });
                }
                *last = current;
            }
            for e in changes {
                self.push_event(e);
            }
        }
        if woke {
            self.expire_dials(now);
            self.wake_g(GKey::Topic);
            self.wake_g(GKey::Lookup);
        }
    }

    /// A session of the hub protocol came up with `peer`.
    pub(super) fn hub_session_up(&mut self, session: vinc_core::SessionId, peer: NodeId) {
        if self.hub_sessions.len() < self.limits.connections {
            self.hub_sessions.insert(session, peer);
            self.neighbors_dirty = true;
        }
    }

    /// A session ended; true if it was one of the hub protocol.
    pub(super) fn hub_session_down(&mut self, session: vinc_core::SessionId) -> bool {
        let was = self.hub_sessions.remove(&session).is_some();
        self.neighbors_dirty |= was;
        was
    }

    /// When the peers are next named to the hubs: while sessions came up or ended since they last were.
    pub(super) fn adjacent_deadline(&self) -> Option<u64> {
        self.adjacent.as_ref().and(self.adjacent_due)
    }

    /// A session came up or ended: the peers are named once the turn's events are handled, no sooner than the gap.
    pub(super) fn adjacent_changed(&mut self) {
        self.adjacent_due.get_or_insert(self.adjacent_next);
    }

    /// With connected topics, name the peers of the application's sessions to the hubs when the set changed, so the
    /// hubs hand this endpoint topic messages only from its connected component. Called once the events of a turn
    /// are handled, and at most once every [`ADJ_GAP`]: a burst of sessions is one signed record, not one per session.
    /// Hub-protocol sessions are not counted: every member holds one with its hubs. When the hubs are not told every
    /// peer, [`Event::AdjacencyShort`] says so.
    pub(super) fn report_adjacent(&mut self, now: u64) {
        if self.adjacent_due.is_none_or(|at| now < at) {
            return;
        }
        self.adjacent_due = None;
        let Some(last) = self.adjacent.as_ref() else { return };
        let mut set: Vec<[u8; 32]> = self.sessions.values().map(|s| s.info.node.bytes).collect();
        set.sort_unstable();
        set.dedup();
        if set == *last {
            return;
        }
        self.adjacent_next = now.saturating_add(ADJ_GAP);
        let sessions = u32::try_from(set.len()).unwrap_or(u32::MAX);
        match self.node.set_adjacent(now, &set) {
            Ok(named) => {
                if named < set.len() {
                    let named = Some(u32::try_from(named).unwrap_or(u32::MAX));
                    self.push_event(Event::AdjacencyShort { sessions, named });
                }
                self.adjacent = Some(set);
                self.dirty = true;
            }
            // The set stays unnamed, so the next change of sessions tries again.
            Err(_) => self.push_event(Event::AdjacencyShort { sessions, named: None }),
        }
    }
}

/// The error for a refusal of the broadcast layer.
fn refused(r: vinc_broadcast::Refused) -> Error {
    match r {
        vinc_broadcast::Refused::TopicTooLong => Error::config("the topic name is longer than 255 bytes"),
        vinc_broadcast::Refused::BodyTooLarge { .. } => Error::new(
            ErrorKind::TooLarge,
            "the message is larger than the topic message limit",
        ),
        vinc_broadcast::Refused::TopicsFull => {
            Error::new(ErrorKind::Busy, "the endpoint tracks as many topics as it can")
        }
        vinc_broadcast::Refused::Sign => Error::config("the message could not be signed"),
        vinc_broadcast::Refused::Backlog => Error::new(
            ErrorKind::Busy,
            "as many publishes as the endpoint tracks are waiting for a hub",
        ),
    }
}
