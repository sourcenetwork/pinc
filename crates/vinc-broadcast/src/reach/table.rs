//! A hub's table of adjacency records and the components they make.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::cmp::Ordering;
use vinc_membership::{Nanos, NodeId};

use super::Mine;
use super::record::{View, verify};
use crate::consts::{RECORD_TTL, REFRESH};

/// A record a hub keeps. An expired one, a tombstone, keeps its id, incarnation and sequence number and names no peer.
#[derive(Debug)]
struct Rec {
    inc: u64,
    seq: u64,
    /// The frame's rest as it arrived, to compare with a refresh; empty once expired.
    rest: Vec<u8>,
    /// The peers it names, sorted, parsed when it was taken; empty once expired.
    peers: Vec<NodeId>,
    heard: Nanos,
    /// Membership released the member for good ([`Topics::release`](crate::Topics::release)).
    gone: bool,
}

impl Rec {
    const fn live(&self) -> bool {
        !self.rest.is_empty()
    }
}

/// What a hub's adjacency table holds and what it refused ([`Topics::reach_stats`](crate::Topics::reach_stats)).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReachStats {
    /// Records kept, expired ones included; at most [`Limits::max_reach`](crate::Limits::max_reach).
    pub records: usize,
    /// Records kept that name their peers (not expired).
    pub live: usize,
    /// Bytes the kept records hold: the frames as they arrived and the parsed peers.
    pub bytes: usize,
    /// Records refused because the table was full.
    pub refused: u64,
    /// Expired records of members released for good, dropped once no log here held a message of theirs.
    pub dropped: u64,
    /// How many times the components were worked out.
    pub rebuilds: u64,
    /// A record was refused for want of room: from then on every node without a record counts as alone.
    pub closed: bool,
}

/// The adjacency state of a node: its own record, and on a hub every member's and the components.
#[derive(Debug)]
pub(crate) struct Reach {
    pub(crate) mine: Option<Mine>,
    recs: BTreeMap<NodeId, Rec>,
    /// The least id of the component of every node with a record, worked out from `recs` before it is read.
    label: RefCell<BTreeMap<NodeId, NodeId>>,
    /// `recs` changed an edge or a node since `label` was worked out.
    dirty: Cell<bool>,
    rebuilds: Cell<u64>,
    /// The hubs and, on a hub, this node: never scoped.
    hubs: Vec<NodeId>,
    max: usize,
    closed: bool,
    refused: u64,
    dropped: u64,
    /// Hub: when the records are next looked at for expiry, while any is live or released.
    pub(crate) sweep_at: Option<Nanos>,
}

/// The root of `i` in the union-find forest `p`, halving the path on the way.
fn root(p: &mut [usize], mut i: usize) -> usize {
    while let Some(&up) = p.get(i).filter(|up| **up != i) {
        let grand = p.get(up).copied().unwrap_or(up);
        if let Some(slot) = p.get_mut(i) {
            *slot = grand;
        }
        i = up;
    }
    i
}

/// Who a message of one origin may be handed to: the origin's class, looked up once for all subscribers.
pub(crate) struct Scope<'a> {
    reach: &'a Reach,
    /// The origin reaches every node: no node is scoped, or the origin is a hub.
    everyone: bool,
    /// The origin's class, when it does not.
    class: Option<NodeId>,
}

impl Scope<'_> {
    /// Whether the message may be handed to `to`: a hub, or a node of the origin's class.
    pub(crate) fn to(&self, to: &NodeId) -> bool {
        self.everyone || self.reach.hubs.contains(to) || self.reach.class(to) == self.class
    }
}

impl Reach {
    /// A table of at most `max` records; `hubs` are never scoped.
    pub(crate) fn new(hubs: Vec<NodeId>, max: usize) -> Self {
        Self {
            mine: None,
            recs: BTreeMap::new(),
            label: RefCell::new(BTreeMap::new()),
            dirty: Cell::new(false),
            rebuilds: Cell::new(0),
            hubs,
            max,
            closed: false,
            refused: 0,
            dropped: 0,
            sweep_at: None,
        }
    }

    /// No node is scoped here: every check passes without a lookup.
    pub(crate) fn open(&self) -> bool {
        self.recs.is_empty() && !self.closed
    }

    pub(crate) fn is_hub(&self, n: &NodeId) -> bool {
        self.hubs.contains(n)
    }

    /// The class of `n`: its component's label, itself for a node with no record once the table refused one (it
    /// may be that node, so it is alone), and `None` for a node that never named its peers.
    pub(crate) fn class(&self, n: &NodeId) -> Option<NodeId> {
        if self.dirty.get() {
            self.rebuild();
        }
        self.label
            .borrow()
            .get(n)
            .copied()
            .or_else(|| self.closed.then_some(*n))
    }

    /// The scope of a message of `origin`.
    pub(crate) fn from(&self, origin: &NodeId) -> Scope<'_> {
        let everyone = self.open() || self.is_hub(origin);
        Scope {
            reach: self,
            everyone,
            class: if everyone { None } else { self.class(origin) },
        }
    }

    /// The labels from the records: union by least index over the edges both ends report.
    // vertexia: a full rebuild, O(records + edges · log records), at most once per check after the records changed
    // their edges or nodes (a refresh that names the same peers changes nothing); an incremental union for joins if
    // tables of thousands churn between every check.
    fn rebuild(&self) {
        let ids: Vec<&NodeId> = self.recs.keys().collect();
        let mut parent: Vec<usize> = (0..ids.len()).collect();
        for (i, (id, rec)) in self.recs.iter().enumerate() {
            for p in &rec.peers {
                let Ok(j) = ids.binary_search(&p) else { continue };
                let mutual = self.recs.get(p).is_some_and(|r| r.peers.binary_search(id).is_ok());
                if j > i && mutual {
                    let (a, b) = (root(&mut parent, i), root(&mut parent, j));
                    let (lo, hi) = (a.min(b), a.max(b));
                    if let Some(slot) = parent.get_mut(hi) {
                        *slot = lo;
                    }
                }
            }
        }
        let mut label = self.label.borrow_mut();
        label.clear();
        for i in 0..ids.len() {
            let r = root(&mut parent, i);
            if let (Some(id), Some(l)) = (ids.get(i), ids.get(r)) {
                label.insert(**id, **l);
            }
        }
        self.dirty.set(false);
        self.rebuilds.set(self.rebuilds.get().saturating_add(1));
    }

    /// Take a record that parsed, `direct` from its member or mirrored by a hub; whether it is new. Nothing changes
    /// unless the signature verifies. A live record takes only a newer one, or the same bytes again (heard again, not
    /// new); a tombstone takes the same or a newer one, and an older one only from its member itself (its incarnation
    /// went back), never from a hub's mirror. A new node with the table full is refused, and the table closes.
    pub(crate) fn take(&mut self, now: Nanos, v: &View<'_>, rest: &[u8], direct: bool) -> Option<bool> {
        if !verify(v) {
            return None;
        }
        if let Some(r) = self.recs.get_mut(v.origin) {
            match (v.inc, v.seq).cmp(&(r.inc, r.seq)) {
                Ordering::Less if r.live() || !direct => return None,
                Ordering::Equal if r.live() => {
                    if r.rest != rest {
                        return None;
                    }
                    r.heard = now;
                    return Some(false);
                }
                _ => {}
            }
        } else if self.recs.len() >= self.max {
            self.refused = self.refused.saturating_add(1);
            self.closed = true;
            return None;
        }
        let peers = v.peers.to_vec();
        let moved = self.recs.get(v.origin).is_none_or(|r| r.peers != peers);
        self.sweep_at.get_or_insert(now.saturating_add(REFRESH));
        self.recs.insert(
            *v.origin,
            Rec {
                inc: v.inc,
                seq: v.seq,
                rest: rest.to_vec(),
                peers,
                heard: now,
                gone: false,
            },
        );
        if moved {
            self.dirty.set(true);
        }
        Some(true)
    }

    /// Every [`REFRESH`], expire the records not heard for [`RECORD_TTL`]: a record expires between [`RECORD_TTL`] and
    /// [`RECORD_TTL`] + [`REFRESH`] after it was last heard. A tombstone keeps its node alone in its component until
    /// it is heard again; forgetting it would make it a node that never named its peers, and two such nodes would
    /// hear each other.
    pub(crate) fn expire(&mut self, now: Nanos) -> bool {
        if self.sweep_at.is_none_or(|t| now < t) {
            return false;
        }
        for r in self.recs.values_mut() {
            if r.live() && now.saturating_sub(r.heard) > RECORD_TTL {
                r.rest = Vec::new();
                if !r.peers.is_empty() {
                    r.peers = Vec::new();
                    self.dirty.set(true);
                }
            }
        }
        let busy = self.recs.values().any(|r| r.live() || r.gone);
        self.sweep_at = busy.then_some(now.saturating_add(REFRESH));
        true
    }

    /// Whether a tombstone of a released member waits for the logs to drop its messages.
    pub(crate) fn any_gone(&self) -> bool {
        self.recs.values().any(|r| r.gone && !r.live())
    }

    /// Drop the tombstones of released members that no log here holds a message of (`logged` says which do): such a
    /// node is neither an origin nor a subscriber here any more, so it needs no class.
    pub(crate) fn drop_gone(&mut self, logged: impl Fn(&NodeId) -> bool) {
        let before = self.recs.len();
        self.recs.retain(|id, r| r.live() || !r.gone || logged(id));
        let n = before - self.recs.len();
        if n > 0 {
            self.dropped = self.dropped.saturating_add(u64::try_from(n).unwrap_or(u64::MAX));
            self.dirty.set(true);
        }
    }

    /// Membership released `n` for good: its tombstone may go once the logs are clear of it.
    pub(crate) fn leave(&mut self, n: &NodeId) {
        if let Some(r) = self.recs.get_mut(n) {
            r.gone = true;
        }
    }

    /// Forget `n`'s record (it was revoked: nothing of it is delivered or logged any more).
    pub(crate) fn forget(&mut self, n: &NodeId) {
        if self.recs.remove(n).is_some() {
            self.dirty.set(true);
        }
    }

    pub(crate) fn stats(&self) -> ReachStats {
        ReachStats {
            records: self.recs.len(),
            live: self.recs.values().filter(|r| r.live()).count(),
            bytes: self.recs.values().map(|r| r.rest.len() + 32 * r.peers.len()).sum(),
            refused: self.refused,
            dropped: self.dropped,
            rebuilds: self.rebuilds.get(),
            closed: self.closed,
        }
    }
}
