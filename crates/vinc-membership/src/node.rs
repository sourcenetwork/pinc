//! The membership node: one state machine that is a member, and also a hub when configured as one.
//!
//! A hub keeps the lease roster (`hub.rs`); every node keeps the member view (`view.rs`); the timers (`timers.rs`)
//! and the frame dispatch (`input.rs`) drive both. This file holds the state, the queues and the session events.
//!
//! Invariants: every table is bounded by [`MAX_TABLE`] or [`MAX_HUBS`] and a full table refuses new entries instead
//! of evicting; iteration over a table that a step also mutates uses a key cursor, so a steady-state step
//! allocates nothing; every collection is ordered, so two runs with the same inputs take the same steps.

use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::vec::Vec;
use core::ops::Bound;

use crate::codec::{Alive, Entry, Frame, NodeId, Path, Record};
use crate::consts::{HUB_STALE, MAX_HUBS, MAX_TABLE, QUEUE_CAP};
use crate::event::{Event, QuietCause, Trace};
use crate::incarnation::{AddressTag, Incarnation, IncarnationError};
use crate::session::{CloseReason, Host, LEAVE_CODE, Nanos, Route};

/// How a node is set up.
#[derive(Debug, Clone, Copy)]
pub struct Config<'a> {
    /// This node.
    pub me: NodeId,
    /// This node is a hub (a bootstrap node that also relays).
    pub is_hub: bool,
    /// The hubs, in the order the host prefers on a tie. A hub's own id may be listed or left out.
    pub hubs: &'a [NodeId],
    /// Queue trace records for [`Membership::poll_trace`].
    pub trace: bool,
}

/// Why a node could not start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StartError {
    /// More than [`MAX_HUBS`] hubs.
    TooManyHubs,
    /// A member with no hub has nothing to attach to.
    NoHubs,
    /// The incarnation could not be issued.
    Incarnation(IncarnationError),
}

impl From<IncarnationError> for StartError {
    fn from(e: IncarnationError) -> Self {
        Self::Incarnation(e)
    }
}

impl core::fmt::Display for StartError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::TooManyHubs => f.write_str("more hubs than the node supports"),
            Self::NoHubs => f.write_str("a member needs at least one hub"),
            Self::Incarnation(e) => e.fmt(f),
        }
    }
}

impl core::error::Error for StartError {}

/// A table is full; the entry was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TableFull;

impl core::fmt::Display for TableFull {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("the revocation table is full")
    }
}

impl core::error::Error for TableFull {}

/// A hub's lease on one member.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Lease {
    pub(crate) rec: Record,
    pub(crate) renewed: Nanos,
}

/// One member in one hub's copy of the roster.
#[derive(Debug, Clone, Copy)]
pub(crate) struct CopyEntry {
    pub(crate) rec: Record,
    /// The snapshot round that last listed it.
    pub(crate) round: u32,
    /// When a complete snapshot first omitted it; it counts for one lease from then.
    pub(crate) absent_since: Option<Nanos>,
}

/// This node's copy of one hub's roster.
#[derive(Debug, Default)]
pub(crate) struct HubCopy {
    pub(crate) entries: BTreeMap<NodeId, CopyEntry>,
    pub(crate) round: u32,
    /// A multi-frame snapshot is in progress.
    pub(crate) open: bool,
}

/// One member of the view.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ViewEntry {
    pub(crate) rec: Record,
    pub(crate) suspected: bool,
}

/// A carrier drop a hub is confirming.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Susp {
    pub(crate) since: Nanos,
    pub(crate) probe_a: Nanos,
    pub(crate) probe_b: Option<(Nanos, Path)>,
    pub(crate) wait: Nanos,
}

/// The first key of `m` strictly after `after` (or the first key when `after` is `None`).
pub(crate) fn next_key<V>(m: &BTreeMap<NodeId, V>, after: Option<&NodeId>) -> Option<NodeId> {
    let lo: Bound<&NodeId> = after.map_or(Bound::Unbounded, Bound::Excluded);
    m.range::<NodeId, _>((lo, Bound::Unbounded)).next().map(|(k, _)| *k)
}

/// As [`next_key`], for a set.
pub(crate) fn next_in(s: &BTreeSet<NodeId>, after: Option<&NodeId>) -> Option<NodeId> {
    let lo: Bound<&NodeId> = after.map_or(Bound::Unbounded, Bound::Excluded);
    s.range::<NodeId, _>((lo, Bound::Unbounded)).next().copied()
}

/// The membership node. See the crate docs for the driving contract.
// The flags are independent facts of one machine (hub or member, leaving, tracing, seal state).
#[allow(clippy::struct_excessive_bools)]
#[derive(Debug)]
pub struct Membership {
    pub(crate) me: NodeId,
    pub(crate) is_hub: bool,
    pub(crate) boot: Vec<NodeId>,
    pub(crate) born: Nanos,
    pub(crate) leaving: bool,
    pub(crate) inc: Incarnation,
    pub(crate) tag: AddressTag,
    pub(crate) ver: u16,
    pub(crate) th: [u8; 8],
    pub(crate) sent: Option<(u16, [u8; 8])>,
    pub(crate) seal_failed: bool,
    pub(crate) max_frame: usize,

    pub(crate) up: BTreeMap<NodeId, Nanos>,
    pub(crate) heard: BTreeMap<NodeId, Nanos>,
    pub(crate) revoked: BTreeSet<NodeId>,

    // The member view.
    pub(crate) hv: BTreeMap<NodeId, HubCopy>,
    pub(crate) members: BTreeMap<NodeId, ViewEntry>,
    pub(crate) epoch: u64,
    pub(crate) hrtt: BTreeMap<NodeId, Nanos>,
    pub(crate) hsent: BTreeMap<NodeId, Nanos>,
    pub(crate) hello_at: BTreeMap<NodeId, Nanos>,
    pub(crate) primary: Option<NodeId>,
    pub(crate) home_ok: Option<NodeId>,
    pub(crate) home_seen: bool,
    pub(crate) recheck: BTreeSet<NodeId>,
    pub(crate) quiet_until: Nanos,
    pub(crate) regrace: bool,
    pub(crate) gone_ver: BTreeMap<NodeId, (u16, [u8; 8])>,
    pub(crate) left: BTreeSet<NodeId>,
    pub(crate) next_renew: Nanos,
    pub(crate) next_tick: Option<Nanos>,
    pub(crate) next_slow: Nanos,

    // The hub roster.
    pub(crate) own: Record,
    pub(crate) roster: BTreeMap<NodeId, Lease>,
    pub(crate) attached: BTreeSet<NodeId>,
    pub(crate) homed: BTreeSet<NodeId>,
    pub(crate) susp: BTreeMap<NodeId, Susp>,
    pub(crate) downed: BTreeMap<NodeId, (Lease, Nanos)>,
    pub(crate) next_conf: Option<Nanos>,

    events: VecDeque<Event>,
    lost_events: u32,
    tracing: bool,
    traces: VecDeque<Trace>,
    lost_traces: u32,
}

impl Membership {
    /// Start a node at `now` (monotonic) with the wall clock `wall_ms`. `floor` is any incarnation epoch the host
    /// remembers by other means (0 for none).
    ///
    /// # Errors
    /// [`StartError`] for a bad hub list or an incarnation that cannot be issued.
    pub fn start<H: Host>(
        cfg: &Config<'_>,
        host: &mut H,
        now: Nanos,
        wall_ms: u64,
        floor: u64,
    ) -> Result<Self, StartError> {
        let mut boot: Vec<NodeId> = Vec::with_capacity(cfg.hubs.len() + 1);
        for h in cfg.hubs {
            if !boot.contains(h) {
                boot.push(*h);
            }
        }
        if cfg.is_hub && !boot.contains(&cfg.me) {
            boot.push(cfg.me);
        }
        if boot.len() > MAX_HUBS {
            return Err(StartError::TooManyHubs);
        }
        if !cfg.is_hub && boot.is_empty() {
            return Err(StartError::NoHubs);
        }
        let inc = Incarnation::start(host, wall_ms, floor)?;
        let mut tag = AddressTag::default();
        let th = tag.tag(now, host);
        let ver = host.version();
        let mut hv = BTreeMap::new();
        if cfg.is_hub {
            hv.insert(cfg.me, HubCopy::default());
        }
        let mut m = Self {
            me: cfg.me,
            is_hub: cfg.is_hub,
            boot,
            born: now,
            leaving: false,
            inc,
            tag,
            ver,
            th,
            sent: None,
            seal_failed: false,
            max_frame: crate::codec::MAX_BODY,
            up: BTreeMap::new(),
            heard: BTreeMap::new(),
            revoked: BTreeSet::new(),
            hv,
            members: BTreeMap::new(),
            epoch: 0,
            hrtt: BTreeMap::new(),
            hsent: BTreeMap::new(),
            hello_at: BTreeMap::new(),
            primary: cfg.is_hub.then_some(cfg.me),
            home_ok: None,
            home_seen: false,
            recheck: BTreeSet::new(),
            quiet_until: 0,
            regrace: false,
            gone_ver: BTreeMap::new(),
            left: BTreeSet::new(),
            next_renew: now,
            next_tick: None,
            next_slow: now,
            own: Record {
                inc: inc.word(),
                ver,
                thash: th,
            },
            roster: BTreeMap::new(),
            attached: BTreeSet::new(),
            homed: BTreeSet::new(),
            susp: BTreeMap::new(),
            downed: BTreeMap::new(),
            next_conf: None,
            events: VecDeque::new(),
            lost_events: 0,
            tracing: cfg.trace,
            traces: VecDeque::new(),
            lost_traces: 0,
        };
        m.trace(Trace::Started { inc: inc.word() });
        Ok(m)
    }

    // ---------------------------------------------------------------- outputs

    /// The next event, oldest first.
    pub fn poll_event(&mut self) -> Option<Event> {
        if self.lost_events > 0 {
            let count = core::mem::take(&mut self.lost_events);
            return Some(Event::Lost { count });
        }
        self.events.pop_front()
    }

    /// The next trace record, oldest first. Empty unless tracing was configured.
    pub fn poll_trace(&mut self) -> Option<Trace> {
        if self.lost_traces > 0 {
            let count = core::mem::take(&mut self.lost_traces);
            return Some(Trace::Lost { count });
        }
        self.traces.pop_front()
    }

    pub(crate) fn emit(&mut self, e: Event) {
        if self.events.len() >= QUEUE_CAP {
            self.lost_events = self.lost_events.saturating_add(1);
        } else {
            self.events.push_back(e);
        }
    }

    pub(crate) fn trace(&mut self, t: Trace) {
        if !self.tracing {
            return;
        }
        if self.traces.len() >= QUEUE_CAP {
            self.lost_traces = self.lost_traces.saturating_add(1);
        } else {
            self.traces.push_back(t);
        }
    }

    // ---------------------------------------------------------------- state

    /// This node.
    pub const fn id(&self) -> &NodeId {
        &self.me
    }

    /// The members of the view, in id order, with their records. The node itself is not listed.
    pub fn members(&self) -> impl Iterator<Item = (&NodeId, &Record)> {
        self.members.iter().map(|(m, e)| (m, &e.rec))
    }

    /// How many members the view lists.
    pub fn member_count(&self) -> usize {
        self.members.len()
    }

    /// The view epoch; it only increases.
    pub const fn view_epoch(&self) -> u64 {
        self.epoch
    }

    /// The hub this node follows, if any is chosen.
    pub const fn primary(&self) -> Option<&NodeId> {
        self.primary.as_ref()
    }

    /// The incarnation word this node announces.
    pub fn incarnation(&self) -> u64 {
        self.inc.word()
    }

    /// Whether the incarnation could not be sealed at some point; the node keeps running on its current word.
    pub const fn seal_failed(&self) -> bool {
        self.seal_failed
    }

    /// The hubs, in preference order.
    pub fn hubs(&self) -> impl Iterator<Item = &NodeId> {
        let me = self.me;
        self.boot.iter().filter(move |h| **h != me)
    }

    /// Whether hub `x` is alive at `now`: this node itself, or a session that received a frame recently.
    pub fn hub_is_up(&self, now: Nanos, x: &NodeId) -> bool {
        self.hub_up(now, x)
    }

    /// Whether the view lists `member`.
    pub fn in_view(&self, member: &NodeId) -> bool {
        self.members.contains_key(member)
    }

    /// Raise (or lower) the largest frame body the node reads from a hub stream, for a broadcast layer configured
    /// for messages larger than the default [`MAX_BODY`](crate::codec::MAX_BODY). The limit never goes below the
    /// default.
    pub fn set_max_frame(&mut self, max_body: usize) {
        self.max_frame = max_body.max(crate::codec::MAX_BODY);
    }

    /// The largest frame body the node reads from a hub stream.
    pub const fn max_frame(&self) -> usize {
        self.max_frame
    }

    /// The members a hub holds a lease for.
    pub fn roster_len(&self) -> usize {
        self.roster.len()
    }

    /// Whether a hub holds a lease for `member`, and when it was last renewed.
    pub fn lease_of(&self, member: &NodeId) -> Option<Nanos> {
        self.roster.get(member).map(|l| l.renewed)
    }

    // ---------------------------------------------------------------- sending

    pub(crate) fn tx<H: Host>(&mut self, h: &mut H, peer: &NodeId, route: Route, f: &Frame<'_>) -> bool {
        self.tx_buf(h, peer, route, f, &mut [0u8; 160])
    }

    /// As [`Membership::tx`], encoding into `buf` for frames larger than the small default.
    pub(crate) fn tx_buf<H: Host>(
        &mut self,
        h: &mut H,
        peer: &NodeId,
        route: Route,
        f: &Frame<'_>,
        buf: &mut [u8],
    ) -> bool {
        if self.revoked.contains(peer) || *peer == self.me {
            return false;
        }
        let Ok(bytes) = f.encode(buf) else {
            return false;
        };
        self.trace(Trace::FrameOut {
            peer: *peer,
            ty: f.ty(),
        });
        h.send(peer, route, bytes)
    }

    pub(crate) fn delta_to<H: Host>(&mut self, h: &mut H, peer: &NodeId, m: &NodeId, rec: Record, alive: Alive) {
        let f = Frame::Delta(Entry { member: m, rec, alive });
        self.tx(h, peer, Route::Session, &f);
    }

    /// Whether `hub` is a hub this node knows.
    pub(crate) fn is_boot(&self, id: &NodeId) -> bool {
        self.boot.contains(id)
    }

    /// Whether hub `x` is alive: this node itself, or a session that received a frame within [`HUB_STALE`].
    pub(crate) fn hub_up(&self, now: Nanos, x: &NodeId) -> bool {
        *x == self.me
            || (self.up.contains_key(x) && self.heard.get(x).is_some_and(|t| now.saturating_sub(*t) < HUB_STALE))
    }

    /// Open a quiet window: removals found now are re-checked after it, not believed.
    pub(crate) fn begin_quiet(&mut self, now: Nanos, cause: QuietCause) {
        self.quiet_until = now.saturating_add(crate::consts::QUIET);
        self.regrace = false;
        self.trace(Trace::Quiet { cause });
    }

    // ---------------------------------------------------------------- session events

    /// A hub stream to `peer` is up. `incoming` is true when `peer` dialed this node.
    ///
    /// A node that dialed a hub (and a hub, whichever side dialed) sends a HELLO asking for a snapshot at once, so a
    /// redial always brings a fresh view.
    /// A hub that accepts a new session forgets the old attachment, so the first HELLO on it is a new attachment.
    pub fn session_up<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId, incoming: bool) {
        if *peer == self.me {
            return;
        }
        if self.revoked.contains(peer) {
            h.close(peer, CloseReason::Revoked);
            return;
        }
        let silent = self
            .heard
            .get(peer)
            .is_some_and(|t| now.saturating_sub(*t) > h.give_up(peer));
        if !self.is_hub && self.is_boot(peer) && silent {
            self.begin_quiet(now, QuietCause::Heal);
        }
        if self.up.len() >= MAX_TABLE && !self.up.contains_key(peer) {
            h.close(peer, CloseReason::Stale);
            return;
        }
        self.up.insert(*peer, now);
        if incoming {
            self.attached.remove(peer);
        }
        // Hubs attach to each other in both directions, whoever dialed.
        if self.is_boot(peer) && (!incoming || self.is_hub) {
            if !self.is_hub && self.primary.as_ref() == Some(peer) {
                h.resubscribe(peer);
            }
            self.hello_to(h, now, peer, true);
        }
    }

    /// The session with `peer` ended with `code`. A graceful leave ([`LEAVE_CODE`]) seen by a hub is reported.
    pub fn session_down<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId, code: u64) {
        if self.up.remove(peer).is_none() {
            return;
        }
        if self.is_hub && code == LEAVE_CODE && !self.is_boot(peer) {
            self.trace(Trace::LeaveSeen { member: *peer });
            self.hub_down(h, now, peer, crate::hub::Cause::Left);
        }
        self.drop_peer(h, now, peer);
    }

    pub(crate) fn drop_peer<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId) {
        self.up.remove(peer);
        self.attached.remove(peer);
        self.homed.remove(peer);
        self.hello_at.remove(peer);
        self.hsent.remove(peer);
        if !self.is_hub && self.home_ok.as_ref() == Some(peer) {
            // The home session is gone, so its copy can go stale: until the home snapshot returns, additions from
            // every fresh hub are believed and removals are held.
            self.home_ok = None;
        }
        if !self.downed.contains_key(peer) {
            h.release(peer);
        }
        if self.is_boot(peer) && self.primary.as_ref() == Some(peer) {
            self.reselect(h, now);
        }
    }

    /// This node leaves the group: close every session with the leave code, and stop renewing.
    pub fn leave<H: Host>(&mut self, h: &mut H) {
        self.leaving = true;
        let mut cur = None;
        while let Some(p) = next_key(&self.up, cur.as_ref()) {
            cur = Some(p);
            h.close(&p, CloseReason::Leave);
        }
    }

    /// The access-control layer revoked `member`: drop it from the view and the roster, forget its subscriptions and
    /// close every session with it. Effective within this call.
    ///
    /// # Errors
    /// [`TableFull`] if the revocation table is full; the revocation is not recorded and must be retried or the
    /// node restarted with a larger bound.
    pub fn revoke<H: Host>(&mut self, h: &mut H, now: Nanos, member: &NodeId) -> Result<(), TableFull> {
        if !self.revoked.contains(member) && self.revoked.len() >= MAX_TABLE {
            return Err(TableFull);
        }
        self.revoked.insert(*member);
        let mut cur = None;
        while let Some(k) = next_key(&self.hv, cur.as_ref()) {
            cur = Some(k);
            if let Some(c) = self.hv.get_mut(&k) {
                c.entries.remove(member);
            }
        }
        self.recheck.remove(member);
        self.left.remove(member);
        self.susp.remove(member);
        self.downed.remove(member);
        self.attached.remove(member);
        self.homed.remove(member);
        if let Some(e) = self.members.remove(member) {
            self.trace(Trace::Removed {
                member: *member,
                why: crate::event::Removal::Revoked,
            });
            self.gone_ver.remove(member);
            if self.is_hub {
                self.home_delta(h, now, member, e.rec, Alive::Down);
            }
            self.bump();
        }
        if let Some(l) = self.roster.remove(member) {
            self.push_delta(h, now, member, l.rec, Alive::Down);
        }
        h.release(member);
        if self.up.contains_key(member) {
            h.close(member, CloseReason::Revoked);
        }
        self.emit(Event::MemberRevoked { member: *member });
        Ok(())
    }

    /// The address of this node changed (a handover).
    pub fn address_changed(&mut self, now: Nanos) {
        self.tag.moved(now);
    }
}
