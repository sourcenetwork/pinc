//! The node's broadcast calls: publish, subscribe, scope, and the counters the broadcast layer keeps.
//!
//! Each call opens the node's step, hands the broadcast layer a host over the node's I/O, and settles the deadlines
//! the layer moved; none holds state of its own.

use vinc_broadcast::{ReachStats, Refused, RejectStats};
use vinc_crypto::Provider;
use vinc_membership::NodeId;

use super::{Due, Node};
use crate::apps::{Apps, ServeSource};
use crate::config::{Nanos, Store};
use crate::ep::Ep;

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// Publish `body` to `topic`; returns the message id.
    ///
    /// # Errors
    /// [`Refused`] for a long topic, a body over the configured limit, a full topic table or a signing failure.
    pub fn publish(&mut self, now: Nanos, topic: &[u8], body: &[u8]) -> Result<[u8; 8], Refused> {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        let r = t.publish(&mut h, now, topic, body);
        self.settle(now);
        r
    }

    /// Subscribe to `topic`.
    ///
    /// # Errors
    /// [`Refused`] for a long topic or a full topic table.
    pub fn subscribe(&mut self, now: Nanos, topic: &[u8]) -> Result<(), Refused> {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        let r = t.subscribe(&mut h, now, topic);
        self.settle(now);
        r
    }

    /// Unsubscribe from `topic`.
    pub fn unsubscribe(&mut self, now: Nanos, topic: &[u8]) {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        t.unsubscribe(&mut h, topic);
        self.settle(now);
    }

    /// Take `member` as a subscriber of `topic` to send to straight when no hub is reachable.
    pub fn hint_subscriber(&mut self, topic: &[u8], member: &NodeId) -> bool {
        self.deadline.set(Due::Stale);
        self.topics.hint(topic, member)
    }

    /// Name the peers this node holds sessions with: from then on the hubs hand it topic messages only from its
    /// connected component (see [`Topics::set_adjacent`](vinc_broadcast::Topics::set_adjacent)). Returns how many
    /// peers the record names.
    ///
    /// # Errors
    /// [`Refused::Sign`] if the record cannot be signed.
    pub fn set_adjacent(&mut self, now: Nanos, peers: &[NodeId]) -> Result<usize, Refused> {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        let r = t.set_adjacent(&mut h, now, peers);
        self.settle(now);
        r
    }

    /// On a hub: what its adjacency table holds, what it refused and whether it is closed
    /// ([`NodeEvent::ReachClosed`](crate::NodeEvent::ReachClosed)); on a member: how many adjacency records it signed. See
    /// [`Topics::reach_stats`](vinc_broadcast::Topics::reach_stats).
    pub fn reach_stats(&self) -> ReachStats {
        self.topics.reach_stats()
    }

    /// The access-control layer answered a broadcast check ([`NodeEvent::BroadcastAcpCheck`](crate::NodeEvent::BroadcastAcpCheck)).
    pub fn broadcast_acp_answer(&mut self, now: Nanos, id: u32, allow: bool) {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        t.acp_answer(&mut h, now, id, allow);
        self.settle(now);
    }

    /// What the broadcast layer turned away, by reason, and how many long walks its id tables made; counted whether or
    /// not tracing is on. See [`Topics::reject_stats`](vinc_broadcast::Topics::reject_stats).
    pub fn reject_stats(&self) -> RejectStats {
        self.topics.reject_stats()
    }
}
