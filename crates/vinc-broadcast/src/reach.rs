//! Delivery scoped to the publisher's connected component: who a hub may hand a message to.
//!
//! A gossip mesh reaches the peers of the publisher, the peers of those peers and so on, and never a node with no path
//! to it. A hub reaches every subscriber, so two groups that share a hub and hold no session between them would hear
//! each other. A member that wants a mesh's reach names the peers it holds sessions with
//! ([`Topics::set_adjacent`]); that is its adjacency record (ADJ), signed by the member and sent to every hub that is
//! up, on every change, when its primary hub's session comes up and every [`REFRESH`].
//!
//! A hub keeps the newest record of each member (by incarnation, then sequence number), mirrors every record a member
//! sends it to the other hubs, and keeps an edge only when both ends list each other. Each component of those edges
//! is labelled by its least id. A message is handed to a subscriber only when the origin and the subscriber are in
//! one class (below), or when either is a hub. The push, the replay, the HAVE offers, the GET answers and the
//! catch-up of a subscriber that is behind all ask [`Topics::may_reach`], so a gap repair answers from the graph as it
//! is now.
//!
//! The class of a node at a hub:
//! - a node with a record: its component;
//! - a node whose record was not heard for [`RECORD_TTL`]: alone. The record stays as a tombstone that names no peer,
//!   until the node is heard again;
//! - a node that never sent a record: unscoped. Unscoped nodes hear each other and no scoped node, as before;
//! - the table holds at most [`Limits::reach_bytes`](crate::Limits::reach_bytes): each record is charged a fixed
//!   share, its peers and its signature. A new node's record that does not fit is refused and the table closes: while it is closed every node without a record is alone, the refused
//!   ones and the unscoped ones alike (failing closed: an unscoped member then hears only hubs through this hub). The
//!   hub reports each refusal ([`Event::ReachRefused`]) and the closing ([`Event::ReachClosed`]). The table opens
//!   again ([`Event::ReachOpened`], checked every [`REFRESH`]) once no refused node waits: each one
//!   got a record (a refused member sends its record again every [`REFRESH`]), was revoked, or was released for
//!   good with nothing of it left in the logs. A hub that refused more nodes than the bytes hold records of no peers
//!   cannot tell, and its table stays closed until it restarts;
//! - a newer record of a node the table holds one of that does not fit is refused too: the node keeps a tombstone,
//!   alone, and the hub reports the refusal; its next record that fits takes its place. The table does not close for
//!   it, since that node has a record;
//! - a node membership released for good ([`Topics::release`]) keeps its tombstone until no log here holds a message
//!   of it; then the tombstone is dropped, since the node is neither an origin nor a subscriber here any more;
//! - a revoked node's record is forgotten: nothing of it is delivered.
//!
//! Hubs are not scoped: a hub's own application hears every message, a hub's own publish reaches every subscriber,
//! and [`Topics::set_adjacent`] on a hub does nothing. Hubs log and mirror every message.
//!
//! The record is signed so that a hub mirrors only what the member said: another hub cannot widen the reach of a
//! member it does not serve. A hub checks the signature before its table changes at all. Members still verify every
//! message, so a hub that ignores the scope leaks no more than a hub did before.
//!
//! A session that comes up joins two components one hub round trip after the later of its two ends names it; one that
//! ends splits them one hub round trip after the first end drops it, and within [`REFRESH`] more when that frame is
//! lost. The components are worked out again before the first check after a record changed an edge, at most once per
//! check however many records arrived between.
//!
//! Invariants: an edge is in the graph only while both ends' newest records list each other; the labels are a
//! function of the records alone, so every hub with the same records hands the same message to the same subscribers;
//! a node that sent a record is never unscoped again at that hub while any log there holds a message of it.
//!
//! Ordering: a member's record reaches its primary hub before its subscriptions and its publishes, since all three
//! ride the same stream and the record goes first when the stream comes up. Modelled in
//! `proofs/tla/BroadcastReach.tla`; the component invariant is `proofs/lean/Vinc/BroadcastReach.lean`.

mod record;
mod table;

use alloc::vec::Vec;
use vinc_crypto::IdentityAlg;
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_membership::{Nanos, NodeId};

use crate::consts::{ADJ_MAX, REFRESH};
use crate::host::{Event, Host, Lane};
use crate::log::HubLog;
use crate::node::{Refused, Topics};
use crate::wire::{self, Head, ty};
pub(crate) use table::Reach;
pub use table::ReachStats;

/// This node's own record, once the host named its peers.
#[derive(Debug)]
pub(crate) struct Mine {
    seq: u64,
    peers: Vec<NodeId>,
    /// The whole ADJ frame, to send again.
    frame: Vec<u8>,
    next: Nanos,
}

/// Whether a message of `origin` may be handed to `to` (see the module docs). Free over the fields it reads, so a
/// caller may hold a topic mutably meanwhile.
pub(crate) fn reaches(reach: &Reach, origin: &NodeId, to: &NodeId) -> bool {
    reach.from(origin).to(to)
}

/// Whether the message logged under `mid` may be offered to `to` in a HAVE: [`reaches`] for its origin. Reads no head
/// while no node is scoped.
pub(crate) fn offers(reach: &Reach, log: &HubLog, mid: u64, to: &NodeId) -> bool {
    reach.open()
        || reach.is_hub(to)
        || log
            .get(mid)
            .and_then(|l| Head::parse(l).ok())
            .is_some_and(|(head, _)| reaches(reach, head.origin, to))
}

impl Topics {
    /// [`reaches`] for this node.
    pub(crate) fn may_reach(&self, origin: &NodeId, to: &NodeId) -> bool {
        reaches(&self.reach, origin, to)
    }

    /// Name the peers this node holds sessions with, so the hubs reach it only from its connected component. The
    /// first call makes the node scoped for the rest of its life; an empty list scopes it to itself. The record goes
    /// to every hub that is up at once when the set changed, so a caller names its peers once a batch of session
    /// changes is handled, not once per change. A record names at most [`ADJ_MAX`] peers: of more, the least
    /// [`ADJ_MAX`] ids. That narrows the reach and can lose an edge both ends hold: two nodes with more than
    /// [`ADJ_MAX`] peers each may name different subsets, and an edge only one of them names is not kept, so the
    /// component may split there. Returns how many peers the record names. On a hub it does nothing and returns 0:
    /// hubs are not scoped.
    ///
    /// # Errors
    /// [`Refused::Sign`] if the record cannot be signed; the last record stays.
    pub fn set_adjacent<H: Host>(&mut self, h: &mut H, now: Nanos, peers: &[NodeId]) -> Result<usize, Refused> {
        if self.is_hub {
            return Ok(0);
        }
        let mut set: Vec<NodeId> = peers.iter().filter(|p| **p != self.me).copied().collect();
        set.sort_unstable();
        set.dedup();
        set.truncate(ADJ_MAX);
        if self.reach.mine.as_ref().is_some_and(|m| m.peers == set) {
            return Ok(set.len());
        }
        let named = set.len();
        let seq = self.reach.mine.as_ref().map_or(1, |m| m.seq + 1);
        let frame = self.adj_frame(seq, &set).ok_or(Refused::Sign)?;
        self.reach.signed = self.reach.signed.saturating_add(1);
        self.reach.mine = Some(Mine {
            seq,
            peers: set,
            frame,
            next: now.saturating_add(REFRESH),
        });
        self.send_adj(h, None);
        Ok(named)
    }

    /// The peers this node named with [`Topics::set_adjacent`], or `None` while it is not scoped.
    pub fn adjacent(&self) -> Option<&[NodeId]> {
        self.reach.mine.as_ref().map(|m| m.peers.as_slice())
    }

    /// On a hub: what its adjacency table holds, what it refused and whether it is closed; on a member: how many records
    /// it signed.
    pub fn reach_stats(&self) -> ReachStats {
        self.reach.stats()
    }

    /// On a hub: whether `a` and `b` are in one class (one component, or both unscoped).
    pub fn same_component(&self, a: &NodeId, b: &NodeId) -> bool {
        self.reach.class(a) == self.reach.class(b)
    }

    fn adj_frame(&self, seq: u64, peers: &[NodeId]) -> Option<Vec<u8>> {
        let count = u16::try_from(peers.len()).ok()?;
        let mut rest = Vec::with_capacity(32 + 1 + self.pk.len() + 18 + 32 * peers.len() + MAX_SIGNATURE_LEN);
        rest.extend_from_slice(&self.me);
        rest.push(self.alg.tag());
        if self.alg != IdentityAlg::Ed25519 {
            rest.extend_from_slice(&self.pk);
        }
        rest.extend_from_slice(&self.inc.to_be_bytes());
        rest.extend_from_slice(&seq.to_be_bytes());
        rest.extend_from_slice(&count.to_be_bytes());
        rest.extend_from_slice(peers.as_flattened());
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let n = self.key.sign(&record::digest(&rest), &mut sig).ok()?;
        rest.extend_from_slice(sig.get(..n)?);
        let mut frame = Vec::with_capacity(6 + rest.len());
        wire::build(&mut frame, ty::ADJ, &[], &[&rest]).ok()?;
        Some(frame)
    }

    /// Send this node's record: to `only`, or to every hub that is up.
    pub(crate) fn send_adj<H: Host>(&self, h: &mut H, only: Option<&NodeId>) {
        let Some(m) = self.reach.mine.as_ref() else { return };
        for hub in self.hubs.iter().filter(|x| only.is_none_or(|o| o == *x)) {
            if only.is_some() || h.hub_up(hub) {
                h.send(hub, Lane::Main, &m.frame);
            }
        }
    }

    /// The refresh, the expiry of the records and the drop of released members' tombstones, on the timer.
    pub(crate) fn reach_timer<H: Host>(&mut self, h: &mut H, now: Nanos) {
        if let Some(m) = self.reach.mine.as_mut()
            && now >= m.next
        {
            m.next = now.saturating_add(REFRESH);
            self.send_adj(h, None);
        }
        if self.reach.expire(now) {
            if self.reach.any_gone() {
                let topics = &self.topics;
                self.reach
                    .drop_gone(|id| topics.values().filter_map(|st| st.log.as_ref()).any(|l| l.holds(id)));
            }
            if self.reach.reopen() {
                h.event(Event::ReachOpened);
            }
        }
    }

    /// When the reach timers next need a call.
    pub(crate) fn reach_deadline(&self) -> Option<Nanos> {
        let mine = self.reach.mine.as_ref().map(|m| m.next);
        match (mine, self.reach.sweep_at) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }

    /// An ADJ frame. A hub takes a member's own record, or one another hub mirrored, and mirrors a member's to the
    /// other hubs; a member ignores it.
    pub(crate) fn on_adj<H: Host>(&mut self, h: &mut H, now: Nanos, from: &NodeId, rest: &[u8]) {
        if !self.is_hub {
            return;
        }
        let Some(v) = record::parse(rest) else { return };
        let mirrored = self.is_boot(from);
        if (!mirrored && v.origin != from) || self.revoked.contains(v.origin) || *v.origin == self.me {
            return;
        }
        let (closed, refused) = (self.reach.is_closed(), self.reach.refused());
        let took = self.reach.take(now, &v, !mirrored);
        if self.reach.refused() != refused {
            h.event(Event::ReachRefused { origin: v.origin });
            if !closed && self.reach.is_closed() {
                h.event(Event::ReachClosed);
            }
        }
        if took.is_none() || mirrored {
            return;
        }
        let mut frame = Vec::with_capacity(6 + rest.len());
        if wire::build(&mut frame, ty::ADJ, &[], &[rest]).is_ok() {
            for hub in &self.hubs {
                h.send(hub, Lane::Main, &frame);
            }
        }
    }
}
