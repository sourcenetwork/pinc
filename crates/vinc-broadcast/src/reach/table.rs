//! A hub's table of adjacency records and the components they make.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use vinc_membership::{Nanos, NodeId};

use super::Mine;
use super::record::{View, verify};
use crate::consts::{RECORD_TTL, REFRESH};

/// A record a hub keeps: the parsed peers and the signature, not the frame. An expired one, a tombstone, keeps its id,
/// incarnation and sequence number and names no peer.
#[derive(Debug)]
struct Rec {
    inc: u64,
    seq: u64,
    /// The peers it names, sorted, parsed when it was taken; empty once expired.
    peers: Vec<NodeId>,
    /// Its signature, to recognise a refresh by its bytes; empty once expired.
    sig: Vec<u8>,
    heard: Nanos,
    /// Membership released the member for good ([`Topics::release`](crate::Topics::release)).
    gone: bool,
}

impl Rec {
    const fn live(&self) -> bool {
        !self.sig.is_empty()
    }
}

/// What a hub's adjacency table holds and what it refused ([`Topics::reach_stats`](crate::Topics::reach_stats)).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ReachStats {
    /// Records kept, expired ones included; at most [`Limits::max_reach`](crate::Limits::max_reach).
    pub records: usize,
    /// Records kept that name their peers (not expired).
    pub live: usize,
    /// Bytes the kept records hold: their peers and their signatures.
    pub bytes: usize,
    /// Records refused because the table was full.
    pub refused: u64,
    /// Nodes refused that hold no record yet and may still be heard here: the table stays closed while any is.
    pub waiting: usize,
    /// More nodes were refused than the table holds records: it stays closed until the hub restarts.
    pub stuck: bool,
    /// How many times a closed table opened again.
    pub reopened: u64,
    /// On a member: how many adjacency records it signed.
    pub signed: u64,
    /// How many record signatures were checked: a refresh with the same bytes is not checked again.
    pub verified: u64,
    /// Expired records of members released for good, dropped once no log here held a message of theirs.
    pub dropped: u64,
    /// How many times the components were worked out.
    pub rebuilds: u64,
    /// A record was refused for want of room: while it stays so, every node without a record counts as alone. It
    /// opens again once no refused node waits ([`waiting`](Self::waiting) is 0), unless it is
    /// [`stuck`](Self::stuck).
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
    /// Refused nodes with no record, and whether membership released each for good. At most `max`.
    waiting: BTreeMap<NodeId, bool>,
    stuck: bool,
    reopened: u64,
    pub(crate) signed: u64,
    verified: u64,
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
            waiting: BTreeMap::new(),
            stuck: false,
            reopened: 0,
            signed: 0,
            verified: 0,
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

    /// Take a record that parsed, `direct` from its member or mirrored by a hub; whether it is new. A live record
    /// takes only a newer one, or the same one again (heard again, not new), recognised by its bytes before any
    /// signature check; a tombstone takes the same or a newer one, and an older one only from its member itself (its
    /// incarnation went back), never from a hub's mirror. Nothing else changes unless the signature verifies. A new
    /// node with the table full is refused: the table closes and the node waits (see [`Reach::reopen`]).
    pub(crate) fn take(&mut self, now: Nanos, v: &View<'_>, direct: bool) -> Option<bool> {
        // A refresh: the same incarnation, sequence, peers and signature. The key fields are not compared, so a copy
        // with another key passes here too; all it does is what the true record's bytes, which anyone can replay, do.
        if let Some(r) = self.recs.get_mut(v.origin)
            && r.live()
            && (v.inc, v.seq) == (r.inc, r.seq)
        {
            if r.peers != v.peers || r.sig != v.sig {
                return None;
            }
            r.heard = now;
            return Some(false);
        }
        self.verified = self.verified.saturating_add(1);
        if !verify(v) {
            return None;
        }
        if let Some(r) = self.recs.get(v.origin) {
            if (v.inc, v.seq) < (r.inc, r.seq) && (r.live() || !direct) {
                return None;
            }
        } else if self.recs.len() >= self.max {
            self.refused = self.refused.saturating_add(1);
            self.closed = true;
            if self.waiting.len() < self.max {
                self.waiting.entry(*v.origin).or_insert(false);
            } else if !self.waiting.contains_key(v.origin) {
                self.stuck = true;
            }
            self.sweep_at.get_or_insert(now.saturating_add(REFRESH));
            return None;
        }
        self.waiting.remove(v.origin);
        let peers = v.peers.to_vec();
        let moved = self.recs.get(v.origin).is_none_or(|r| r.peers != peers);
        self.sweep_at.get_or_insert(now.saturating_add(REFRESH));
        self.recs.insert(
            *v.origin,
            Rec {
                inc: v.inc,
                seq: v.seq,
                peers,
                sig: v.sig.to_vec(),
                heard: now,
                gone: false,
            },
        );
        if moved {
            self.dirty.set(true);
        }
        Some(true)
    }

    /// Open a closed table again when no refused node waits for a record: every node refused since
    /// it closed has a record now, was revoked, or was released for good with nothing of it left in the logs. Then no
    /// node that asked to be scoped is without a record, and counting the nodes without one as unscoped again lets
    /// no scoped node's message out of its component. A table that refused more nodes than it could remember stays
    /// closed until the hub restarts. Whether it opened.
    pub(crate) fn reopen(&mut self) -> bool {
        if !self.closed || self.stuck || !self.waiting.is_empty() {
            return false;
        }
        self.closed = false;
        self.reopened = self.reopened.saturating_add(1);
        true
    }

    pub(crate) const fn is_closed(&self) -> bool {
        self.closed
    }

    pub(crate) const fn refused(&self) -> u64 {
        self.refused
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
                r.sig = Vec::new();
                if !r.peers.is_empty() {
                    r.peers = Vec::new();
                    self.dirty.set(true);
                }
            }
        }
        let busy = self.closed || self.recs.values().any(|r| r.live() || r.gone);
        self.sweep_at = busy.then_some(now.saturating_add(REFRESH));
        true
    }

    /// Whether a tombstone of a released member, or a refused node released, waits for the logs to drop its messages.
    pub(crate) fn any_gone(&self) -> bool {
        self.recs.values().any(|r| r.gone && !r.live()) || self.waiting.values().any(|gone| *gone)
    }

    /// Drop the tombstones of released members that no log here holds a message of (`logged` says which do): such a
    /// node is neither an origin nor a subscriber here any more, so it needs no class.
    pub(crate) fn drop_gone(&mut self, logged: impl Fn(&NodeId) -> bool) {
        self.waiting.retain(|id, gone| !*gone || logged(id));
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
        if let Some(gone) = self.waiting.get_mut(n) {
            *gone = true;
        }
    }

    /// Forget `n`'s record (it was revoked: nothing of it is delivered or logged any more).
    pub(crate) fn forget(&mut self, n: &NodeId) {
        self.waiting.remove(n);
        if self.recs.remove(n).is_some() {
            self.dirty.set(true);
        }
    }

    pub(crate) fn stats(&self) -> ReachStats {
        ReachStats {
            records: self.recs.len(),
            live: self.recs.values().filter(|r| r.live()).count(),
            bytes: self.recs.values().map(|r| r.sig.len() + 32 * r.peers.len()).sum(),
            refused: self.refused,
            waiting: self.waiting.len(),
            stuck: self.stuck,
            reopened: self.reopened,
            signed: self.signed,
            verified: self.verified,
            dropped: self.dropped,
            rebuilds: self.rebuilds.get(),
            closed: self.closed,
        }
    }
}
