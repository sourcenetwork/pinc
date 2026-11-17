//! The subscriber tables of a hub: held, restored and forgotten subscriptions, and the replication of the
//! subscriber list to the members, which the member-to-member fallback needs.
//!
//! Membership tells the hub what happened to a member: [`Topics::hold`] when it is confirmed down (its subscriptions
//! are kept for the lease and nothing is pushed to it), [`Topics::restore`] when it returns within the lease (the
//! subscriptions are live again and the member is told, one RESTORED per topic), [`Topics::release`] when it is gone
//! for good.
//!
//! Whenever the list of a topic changes, the hub tells its recipients (the live subscribers and the recent publishers)
//! what changed: a SUBS delta of the nodes added and removed. Every list has a version, the hub's incarnation and a
//! number raised at each change; a delta names the version it makes, and applies only to the one before it. A member
//! that is sent a delta whose base is not the version it holds (it missed one: a reset, a relay drop, a hub restart)
//! applies nothing, waits, and asks the hub for the whole list (ASK). Every SUB carries the version the member holds
//! of that hub's list, and the hub answers one that is not its current version with the whole list. The hub also
//! sends the whole list, without being asked, to a recipient that it knows may lack it (a new publisher, a restored
//! member, one whose stream refused a frame: `stale`), on the next change or when its stream has room. The other hubs
//! are sent the hub's local set whole, when it changes.
//!
//! A whole list goes as ordered pieces of at most [`SUBS_PIECE`] ids, all at one version, so no list is bigger than the
//! smallest valid frame whatever `max_subscribers` is. The hub keeps each stale recipient's place (the next piece) and
//! goes on from it when the stream has room; a change to the list sends every recipient back to the first piece, and a
//! fresh SUB, which does not change the list, leaves a recipient where it is (a member sends one every 20 s, and a slow
//! stream needs longer than that for a long list). A receiver gathers the pieces of each hub apart and acts only on a
//! whole list: a piece that does not follow the ones before it (a lost piece) breaks the gathering, is traced
//! ([`SubsDrop::Gap`]) and makes a member ask the hub once. Deltas keep the bytes a change costs a recipient
//! independent of the number of subscribers: the whole list on every change made the join of `n` subscribers cost `n`
//! lists of up to `max_subscribers` nodes on every session. A change of more than [`SUBS_PIECE`] ids is sent as the
//! whole list. A SUBS frame that changes nothing is traced with why ([`Trace::SubsDropped`]).
//!
//! Invariants: a list holds at most `max_subscribers` nodes in id order, so two hubs with the same tables send the
//! same bytes; `told` is the list built from the tables after every change, and `(incarnation, told_seq)` its
//! version; a member's list is always the list its hub had at the version the member holds: a delta is applied only
//! on its own base, and only from the hub of the member's list (a change from the primary makes it the hub of the
//! list, and the member asks it for the whole list), a join hint never enters it, and a member whose limit cut the
//! list asks for the whole list on a change that removes (the id past the cut is not in the change); a member's list
//! changes only when a gathering completes, never on a piece; `stale` holds only recipients, and `Topics::owed` holds
//! every recipient stale in some topic, so a stream's room is a lookup, not a walk of the topics; a held member
//! receives no push; a restore tells the member exactly the topics it had; a release of a member that was behind in
//! a topic leaves the span of what it was owed in that topic.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;
use vinc_membership::NodeId;

use crate::consts::{SUBS_PIECE, TABLE_MAX};
use crate::event::{SubsDrop, Trace, topic_tag};
use crate::host::{Event, Host, Lane};
use crate::node::{Topic, Topics};
use crate::wire::{self, ty};

/// How many recent publishers a hub tells the subscriber list of one topic.
const PUBS_MAX: usize = 256;

/// A SUBS frame that carries a piece of the whole list (`version | first | total | count | ids`): the ids of ranks
/// `first` to `first + count - 1` of a list of `total` ids. The receiver replaces its own list when the pieces of one
/// version make the whole list.
pub(crate) const FULL: u8 = 0;
/// A SUBS frame that carries a change (`version | count | added ids | count | removed ids`) from the version before
/// `version`: the receiver applies it only on that base.
pub(crate) const DELTA: u8 = 1;
/// A SUBS frame from a member: send me the whole list.
pub(crate) const ASK: u8 = 2;

/// A list's version: the hub's incarnation and the number of the change.
pub(crate) type Ver = (u64, u32);

/// The 12 bytes of a version.
pub(crate) fn ver_bytes((inc, seq): Ver) -> [u8; 12] {
    let mut b = [0u8; 12];
    let (i, s) = b.split_at_mut(8);
    i.copy_from_slice(&inc.to_be_bytes());
    s.copy_from_slice(&seq.to_be_bytes());
    b
}

/// A version from its 12 bytes, and the bytes after them.
pub(crate) fn read_ver(b: &[u8]) -> Option<(Ver, &[u8])> {
    let (inc, rest) = b.split_first_chunk::<8>()?;
    let (seq, rest) = rest.split_first_chunk::<4>()?;
    Some(((u64::from_be_bytes(*inc), u32::from_be_bytes(*seq)), rest))
}

/// Lay the list of `st` in `nodes`: the live local subscribers and the other hubs' reports (or only the local ones),
/// in id order, cut at `max`.
fn build_list(nodes: &mut Vec<NodeId>, st: &Topic, local_only: bool, max: usize) {
    nodes.clear();
    let live = st.subs.iter().filter(|(_, l)| **l).map(|(p, _)| p);
    let remote = st.rsubs.values().flatten().filter(|_| !local_only);
    for n in live.chain(remote) {
        if let Err(pos) = nodes.binary_search(n)
            && nodes.len() < max
        {
            nodes.insert(pos, *n);
        }
    }
}

fn count(n: usize) -> [u8; 2] {
    u16::try_from(n).unwrap_or(u16::MAX).to_be_bytes()
}

/// The pieces a list of `n` ids goes in: an empty list is one piece, so a node that knew subscribers learns they are
/// gone.
fn pieces(n: usize) -> usize {
    n.div_ceil(SUBS_PIECE).max(1)
}

/// The piece of `list` at version `ver` that starts at rank `first`, in `scratch`.
fn piece_frame(scratch: &mut Vec<u8>, topic: &[u8], ver: Ver, list: &[NodeId], first: usize) -> bool {
    let rest = list.get(first..).unwrap_or_default();
    let ids = rest.get(..SUBS_PIECE).unwrap_or(rest);
    wire::build(
        scratch,
        ty::SUBS,
        topic,
        &[
            &[FULL],
            &ver_bytes(ver),
            &count(first),
            &count(list.len()),
            &count(ids.len()),
            ids.as_flattened(),
        ],
    )
    .is_ok()
}

/// What one receiver holds of the list a hub is sending it in pieces.
#[derive(Debug)]
pub(crate) struct Part {
    ver: Ver,
    total: u16,
    /// The ids counted so far, kept or not.
    got: u16,
    /// The first `max` of them.
    ids: Vec<NodeId>,
    /// A piece did not follow the ones before it: nothing more is taken until a first piece restarts it.
    broken: bool,
}

/// What a piece did to the gathering of its sender.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Gathered {
    /// The list is whole: the gathered ids, or the ids of the piece itself when it alone is the list (`None`).
    Whole(Option<Vec<NodeId>>),
    /// More pieces are due; nothing changed.
    Partial,
    /// The piece does not follow the ones before it; `ask` when this breaks the gathering (once per gathering).
    Gap { ask: bool },
}

/// Take the piece of ranks `first..first + ids.len()` of a list of `total` ids at `ver` from `from`, keeping at most
/// `max` ids. A first piece starts the gathering of `from` again; any other joins it only when it follows the ones
/// before it at the same version and total.
pub(crate) fn gather(
    parts: &mut BTreeMap<NodeId, Part>,
    from: &NodeId,
    ver: Ver,
    first: u16,
    total: u16,
    ids: &[NodeId],
    max: usize,
) -> Gathered {
    let n = u16::try_from(ids.len()).unwrap_or(u16::MAX);
    if first == 0 {
        if n == total {
            parts.remove(from);
            return Gathered::Whole(None);
        }
        parts.insert(
            *from,
            Part {
                ver,
                total,
                got: n,
                ids: ids.iter().take(max).copied().collect(),
                broken: false,
            },
        );
        return Gathered::Partial;
    }
    // A piece that does not follow starts a broken gathering of its own version, and asks; the rest of that version
    // ask nothing more.
    let broken = Part {
        ver,
        total,
        got: 0,
        ids: Vec::new(),
        broken: true,
    };
    let Some(p) = parts.get_mut(from) else {
        parts.insert(*from, broken);
        return Gathered::Gap { ask: true };
    };
    let same = p.ver == ver && p.total == total;
    if p.broken && same {
        return Gathered::Gap { ask: false };
    }
    if !same || p.got != first {
        *p = broken;
        return Gathered::Gap { ask: true };
    }
    let room = max.saturating_sub(p.ids.len());
    p.ids.extend(ids.iter().take(room).copied());
    p.got = p.got.saturating_add(n);
    if p.got < p.total {
        return Gathered::Partial;
    }
    Gathered::Whole(parts.remove(from).map(|p| p.ids))
}

/// What turns the sorted list `old` into the sorted list `new`: the nodes only `new` has, and those only `old` has.
pub(crate) fn delta(old: &[NodeId], new: &[NodeId]) -> (Vec<NodeId>, Vec<NodeId>) {
    let only = |a: &[NodeId], b: &[NodeId]| a.iter().filter(|n| b.binary_search(n).is_err()).copied().collect();
    (only(new, old), only(old, new))
}

/// Apply a change to the sorted list `list`: remove `rem`, insert `add` in order, keep at most `max`; true when the
/// cut dropped an id. For sorted lists without duplicates and at most `max` long, `apply(old, delta(old, new))` is
/// `new`.
pub(crate) fn apply(list: &mut Vec<NodeId>, add: &[NodeId], rem: &[NodeId], max: usize) -> bool {
    list.retain(|n| !rem.contains(n));
    for n in add {
        if let Err(pos) = list.binary_search(n) {
            list.insert(pos, *n);
        }
    }
    let cut = list.len() > max;
    list.truncate(max);
    cut
}

/// Whether the hub tells `p` the list of `st`: a live subscriber, or a recent publisher that holds no subscription (a
/// held subscriber is told nothing, whatever else it did).
fn is_recipient(st: &Topic, p: &NodeId) -> bool {
    st.subs.get(p).copied().unwrap_or_else(|| st.pubs.contains(p))
}

/// Bring the recipients of `topic` to the current list: a delta to those that are not stale (the whole list when the
/// change names more than [`SUBS_PIECE`] ids), then the whole list to the stale ones. A recipient whose stream refuses
/// its frame is stale until one takes the whole list. A change sends every recipient back to the first piece. `inc` is
/// the hub's incarnation, the first half of every version it sends.
#[allow(
    clippy::too_many_arguments,
    reason = "the disjoint fields of `Topics` the iteration over its topics leaves free"
)]
fn tell_members<H: Host>(
    h: &mut H,
    scratch: &mut Vec<u8>,
    nodes: &mut Vec<NodeId>,
    owed: &mut BTreeSet<NodeId>,
    topic: &[u8],
    st: &mut Topic,
    max: usize,
    inc: u64,
) {
    build_list(nodes, st, false, max);
    if *nodes != st.told {
        let (add, rem) = delta(&st.told, nodes);
        // vertexia: wraps after 2^32 changes in one life of the hub; a member a whole cycle behind would take a delta.
        st.told_seq = st.told_seq.wrapping_add(1);
        let parts: [&[u8]; 6] = [
            &[DELTA],
            &ver_bytes((inc, st.told_seq)),
            &count(add.len()),
            add.as_flattened(),
            &count(rem.len()),
            rem.as_flattened(),
        ];
        let built = add.len() + rem.len() <= SUBS_PIECE && wire::build(scratch, ty::SUBS, topic, &parts).is_ok();
        let subs = st.subs.keys();
        let others = st.pubs.iter().filter(|p| !st.subs.contains_key(*p));
        let mut refused = Vec::new();
        for p in subs
            .chain(others)
            .filter(|p| is_recipient(st, p) && !st.stale.contains_key(*p))
        {
            if !built || !h.send(p, Lane::Reply, scratch) {
                refused.push(*p);
            }
        }
        // The pieces sent so far were of the list before this change.
        // vertexia: a change restarts a list in flight; holding the change for recipients mid-list if a stream
        // slower than the churn must still converge
        st.stale.values_mut().for_each(|place| *place = 0);
        st.stale.extend(refused.into_iter().map(|p| (p, 0)));
        st.told.clone_from(nodes);
    }
    flush_stale(h, scratch, owed, topic, st, None, inc);
}

/// Send the next pieces of the whole list to the stale recipients of `st`, or only to `only`; a recipient whose stream
/// took the last piece is no longer stale, and one whose stream refused a piece keeps its place. A stale entry that is
/// no longer a recipient is dropped: it is sent nothing, and the whole list again if it comes back. Every recipient
/// still stale afterwards is in `owed`, so its stream's room brings it the rest of the list.
fn flush_stale<H: Host>(
    h: &mut H,
    scratch: &mut Vec<u8>,
    owed: &mut BTreeSet<NodeId>,
    topic: &[u8],
    st: &mut Topic,
    only: Option<&NodeId>,
    inc: u64,
) {
    let gone: Vec<NodeId> = st.stale.keys().filter(|p| !is_recipient(st, p)).copied().collect();
    for p in &gone {
        st.stale.remove(p);
    }
    let ver = (inc, st.told_seq);
    let n = u16::try_from(pieces(st.told.len())).unwrap_or(u16::MAX);
    if let Some(p) = only {
        let mut at = st.stale.get(p).copied().filter(|at| *at < n).unwrap_or(0);
        while st.stale.contains_key(p) {
            let sent = piece_frame(scratch, topic, ver, &st.told, usize::from(at) * SUBS_PIECE)
                && h.send(p, Lane::Reply, scratch);
            if !sent {
                st.stale.insert(*p, at);
                break;
            }
            at += 1;
            if at >= n {
                st.stale.remove(p);
            }
        }
    } else {
        // Each piece is built once and sent to every recipient at that place; the next one goes to the lowest
        // place above it, the recipients that took this piece among them.
        let mut at = st.stale.values().copied().min();
        while let Some(place) = at.filter(|at| *at < n) {
            if piece_frame(scratch, topic, ver, &st.told, usize::from(place) * SUBS_PIECE) {
                for (p, slot) in st.stale.iter_mut().filter(|(_, slot)| **slot == place) {
                    if h.send(p, Lane::Reply, scratch) {
                        *slot = place + 1;
                    }
                }
            }
            at = st.stale.values().copied().filter(|at| *at > place).min();
        }
        st.stale.retain(|_, at| *at < n);
    }
    owed.extend(st.stale.keys().copied());
}

/// Tell the recipients of `topic` what changed, and, when the local set changed, the other hubs the local set, in
/// pieces. A hub whose stream refuses a piece is sent no more of this set and none is kept for it: it takes the next
/// set whole.
#[allow(
    clippy::too_many_arguments,
    reason = "the disjoint fields of `Topics` the iteration over its topics leaves free"
)]
fn announce<H: Host>(
    h: &mut H,
    scratch: &mut Vec<u8>,
    nodes: &mut Vec<NodeId>,
    owed: &mut BTreeSet<NodeId>,
    hubs: &[NodeId],
    topic: &[u8],
    st: &mut Topic,
    max: usize,
    local_changed: bool,
    inc: u64,
) {
    tell_members(h, scratch, nodes, owed, topic, st, max, inc);
    if local_changed && !hubs.is_empty() {
        build_list(nodes, st, true, max);
        // The other hub keeps this set whole and reads the version only to join the pieces.
        // At most `MAX_HUBS` (64) hubs, one bit each.
        let mut refused = 0u64;
        for first in (0..pieces(nodes.len())).map(|i| i * SUBS_PIECE) {
            if !piece_frame(scratch, topic, (inc, st.told_seq), nodes, first) {
                break;
            }
            for (bit, hub) in (0u32..).zip(hubs) {
                let mask = 1u64.wrapping_shl(bit);
                if refused & mask == 0 && !h.send(hub, Lane::Main, scratch) {
                    refused |= mask;
                }
            }
        }
    }
}

impl Topic {
    /// Forget the hints a hub's list names: the list covers them, and no node is in both.
    fn drop_covered_hints(&mut self) {
        let peers = &self.peers;
        self.hints.retain(|n| peers.binary_search(n).is_err());
    }

    /// The version of this topic's list a member holds from `hub`, if it holds one. Read from the topic itself, since
    /// the loops that send SUB take the topic table out of `Topics` while they run.
    pub(crate) fn held(&self, hub: &NodeId) -> Option<Ver> {
        if self.peers_from == Some(*hub) {
            self.peers_ver
        } else {
            None
        }
    }
}

impl Topics {
    /// Replicate the subscriber list of `topic` after a change; `local_changed` when the local set changed. `fresh`
    /// is a recipient that must be sent the whole list (a subscriber that just subscribed, again or for the first
    /// time): it is sent from the start unless it is in the middle of the list already, which a SUB does not restart.
    pub(crate) fn announce_topic<H: Host>(
        &mut self,
        h: &mut H,
        topic: &[u8],
        local_changed: bool,
        fresh: Option<&NodeId>,
    ) {
        if let Some(st) = self.topics.get_mut(topic) {
            if let Some(f) = fresh {
                st.stale.entry(*f).or_insert(0);
            }
            announce(
                h,
                &mut self.scratch,
                &mut self.nodes,
                &mut self.owed,
                &self.hubs,
                topic,
                st,
                self.limits.max_subscribers,
                local_changed,
                self.inc,
            );
        }
    }

    /// A publisher that is not a hub: remember it and tell it the subscribers, so it can reach them with no hub.
    pub(crate) fn note_publisher<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8]) {
        if !self.ensure_topic(topic) {
            return;
        }
        let Some(st) = self.topics.get_mut(topic) else {
            return;
        };
        if st.subs.contains_key(from) || st.pubs.len() >= PUBS_MAX || !st.pubs.insert(*from) {
            return;
        }
        st.stale.insert(*from, 0);
        flush_stale(h, &mut self.scratch, &mut self.owed, topic, st, Some(from), self.inc);
    }

    /// The stream of `peer` has room again: send it the rest of the whole list of every topic it is stale in, from its
    /// place. A peer no stream refused a list costs a lookup in `owed`, not a walk of the topic table.
    pub(crate) fn subs_writable<H: Host>(&mut self, h: &mut H, peer: &NodeId) {
        if !self.owed.remove(peer) {
            return;
        }
        for (k, st) in &mut self.topics {
            if st.stale.contains_key(peer) {
                flush_stale(h, &mut self.scratch, &mut self.owed, k, st, Some(peer), self.inc);
            }
        }
    }

    /// Hub: how many nodes are in `owed`, the ones a refused list left owed the whole list in some topic. A superset
    /// of the nodes still owed in a topic: an entry stays until its stream has room, though the topic dropped it.
    pub fn subs_owed(&self) -> usize {
        self.owed.len()
    }

    /// The version of `topic`'s list this member holds from `hub`, if it holds one: what its SUB to `hub` carries.
    pub(crate) fn held_ver(&self, hub: &NodeId, topic: &[u8]) -> Option<Ver> {
        self.topics.get(topic).and_then(|st| st.held(hub))
    }

    /// The hub's current version of `topic`'s list.
    pub(crate) fn cur_ver(&self, topic: &[u8]) -> Ver {
        (self.inc, self.topics.get(topic).map_or(0, |st| st.told_seq))
    }

    /// `member` was confirmed down: keep its subscriptions for the lease and push it nothing.
    // vertexia: hold, restore and release scan the topic table (at most `max_topics`); a per-member topic index if the
    // table is ever raised far.
    pub fn hold<H: Host>(&mut self, h: &mut H, member: &NodeId) {
        let mut any = false;
        for (k, st) in &mut self.topics {
            if let Some(live) = st.subs.get_mut(member)
                && core::mem::replace(live, false)
            {
                // A held member is pushed nothing; its next subscribe says from when it wants the log.
                st.behind.remove(member);
                any = true;
                announce(
                    h,
                    &mut self.scratch,
                    &mut self.nodes,
                    &mut self.owed,
                    &self.hubs,
                    k,
                    st,
                    self.limits.max_subscribers,
                    true,
                    self.inc,
                );
            }
        }
        if any {
            self.trace(|| Trace::SubsHeld { member: *member });
        }
    }

    /// `member` returned within the lease: its held subscriptions are live again, and it is told which. It missed
    /// the changes made while it was held, so it is sent the whole list.
    pub fn restore<H: Host>(&mut self, h: &mut H, member: &NodeId) {
        let mut topics = 0u16;
        for (k, st) in &mut self.topics {
            if let Some(live) = st.subs.get_mut(member)
                && !core::mem::replace(live, true)
            {
                topics = topics.saturating_add(1);
                if wire::build(&mut self.scratch, ty::RESTORED, k, &[]).is_ok() {
                    h.send(member, Lane::Reply, &self.scratch);
                }
                st.stale.insert(*member, 0);
                announce(
                    h,
                    &mut self.scratch,
                    &mut self.nodes,
                    &mut self.owed,
                    &self.hubs,
                    k,
                    st,
                    self.limits.max_subscribers,
                    true,
                    self.inc,
                );
            }
        }
        if topics > 0 {
            self.trace(|| Trace::SubsRestored {
                member: *member,
                topics,
            });
        }
    }

    /// `member`'s session ended and it was not confirmed down: forget its subscriptions. If it was behind in a topic,
    /// the topic keeps the span, so the member is told when it subscribes again and is not offered what it was owed.
    /// Its adjacency record goes once it expired and no log holds a message of it.
    pub fn release<H: Host>(&mut self, h: &mut H, member: &NodeId) {
        self.reach.leave(member);
        self.owed.remove(member);
        let wall = h.wall_ms();
        let mut any = false;
        for (k, st) in &mut self.topics {
            let was_pub = st.pubs.remove(member);
            st.forget_place(member, wall);
            st.stale.remove(member);
            if st.subs.remove(member).is_some() {
                any = true;
                announce(
                    h,
                    &mut self.scratch,
                    &mut self.nodes,
                    &mut self.owed,
                    &self.hubs,
                    k,
                    st,
                    self.limits.max_subscribers,
                    true,
                    self.inc,
                );
            } else {
                any |= was_pub;
            }
        }
        if any {
            self.trace(|| Trace::SubsReleased { member: *member });
        }
    }

    /// A SUBS frame. A hub answers a recipient's ASK with the whole list, and keeps another hub's local set (once all
    /// its pieces came) and tells its own recipients what changed in the union. A member replaces its list with a whole
    /// one (the pieces of one version, gathered per hub, never a part of it) and remembers which hub sent it and its
    /// version; it applies a delta only from that hub and only on the version it
    /// holds. A delta on any other base means the member missed a change: it applies nothing, waits for a whole list
    /// (deltas meanwhile are ignored) and asks the hub for one.
    pub(crate) fn on_subs<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8], rest: &[u8]) {
        if let Some(why) = self.take_subs(h, from, topic, rest) {
            self.trace(|| Trace::SubsDropped {
                from: *from,
                topic: topic_tag(topic),
                why,
            });
        }
    }

    /// [`Topics::on_subs`] but the trace: why the frame changed nothing, if it did not (a piece that is not the last
    /// changes nothing and is not traced). Every field the sender controls is checked before any state changes; an
    /// off-base change and a piece out of order still ask for the whole list.
    fn take_subs<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8], rest: &[u8]) -> Option<SubsDrop> {
        let Some((kind, rest)) = rest.split_first() else {
            return Some(SubsDrop::Malformed);
        };
        if *kind == ASK {
            let is_hub = self.is_hub;
            let Some(st) = self.topics.get_mut(topic).filter(|st| is_hub && is_recipient(st, from)) else {
                return Some(SubsDrop::NotRecipient);
            };
            st.stale.insert(*from, 0);
            flush_stale(h, &mut self.scratch, &mut self.owed, topic, st, Some(from), self.inc);
            return None;
        }
        if !self.is_boot(from) {
            return Some(SubsDrop::NotHub);
        }
        let Some((ver, rest)) = read_ver(rest) else {
            return Some(SubsDrop::Malformed);
        };
        if *kind == FULL {
            return self.take_piece(h, from, topic, ver, rest);
        }
        let Some((ids, tail)) = read_ids(rest) else {
            return Some(SubsDrop::Malformed);
        };
        let rem = read_ids(tail).map(|(rem, _)| rem);
        let Some(rem) = rem.filter(|_| *kind == DELTA && !self.is_hub) else {
            return Some(SubsDrop::Malformed);
        };
        if !self.ensure_topic(topic) {
            return Some(SubsDrop::TopicsFull);
        }
        let (max, primary, me) = (self.limits.max_subscribers, self.primary, self.me);
        let st = self.topics.get_mut(topic)?;
        // A change from the primary after a late whole list of another hub: the primary is the source, whatever the
        // list came from, so the member asks it for its whole list.
        if st.peers_from != Some(*from) {
            if primary == Some(*from) {
                st.peers_from = Some(*from);
                st.peers_ver = None;
                ask(h, &mut self.scratch, from, topic);
            }
            return Some(SubsDrop::OtherHub);
        }
        // Not newer than the version held: a late frame of an old session, nothing to apply or to ask for.
        if st
            .peers_ver
            .is_some_and(|(e, s)| e == ver.0 && s.wrapping_sub(ver.1) < 1 << 31)
        {
            return Some(SubsDrop::Old);
        }
        // A removal of an id the member holds, from a list cut below the hub's, brings an id the member never saw into
        // the hub's cut: only the whole list tells which. (An id past the cut changes nothing here.)
        if st.peers_ver == Some((ver.0, ver.1.wrapping_sub(1)))
            && !(st.peers_cut && rem.iter().any(|r| st.peers.binary_search(r).is_ok()))
        {
            st.peers_cut |= apply(&mut st.peers, ids, rem, max);
            st.peers_ver = Some(ver);
            st.drop_covered_hints();
            confirm(h, st, from, topic, &me);
            return None;
        }
        // A missed change: the member waits for a whole list and asks once; changes meanwhile are dropped.
        if st.peers_ver.take().is_some() {
            ask(h, &mut self.scratch, from, topic);
        }
        Some(SubsDrop::OffBase)
    }

    /// A piece of a whole list, `rest` being what follows its version: gathered per sending hub, and acted on only when
    /// the list is whole.
    fn take_piece<H: Host>(
        &mut self,
        h: &mut H,
        from: &NodeId,
        topic: &[u8],
        ver: Ver,
        rest: &[u8],
    ) -> Option<SubsDrop> {
        let Some((first, total, ids)) = read_piece(rest) else {
            return Some(SubsDrop::Malformed);
        };
        if !self.ensure_topic(topic) {
            return Some(SubsDrop::TopicsFull);
        }
        let (is_hub, inc, me, max) = (self.is_hub, self.inc, self.me, self.limits.max_subscribers);
        let st = self.topics.get_mut(topic)?;
        match gather(&mut st.parts, from, ver, first, total, ids, max) {
            Gathered::Partial => None,
            Gathered::Gap { ask: wanted } => {
                // A hub keeps the last whole list of the other hub and asks for nothing.
                if !is_hub {
                    if st.peers_from == Some(*from) {
                        st.peers_ver = None;
                    }
                    if wanted {
                        ask(h, &mut self.scratch, from, topic);
                    }
                }
                Some(SubsDrop::Gap)
            }
            Gathered::Whole(whole) => {
                let list = whole.as_deref().unwrap_or(ids);
                if is_hub {
                    let e = st.rsubs.entry(*from).or_default();
                    e.clear();
                    e.extend(list.iter().take(max).copied());
                    tell_members(
                        h,
                        &mut self.scratch,
                        &mut self.nodes,
                        &mut self.owed,
                        topic,
                        st,
                        max,
                        inc,
                    );
                } else {
                    st.peers.clear();
                    st.peers.extend(list.iter().take(max).copied());
                    st.peers_cut = usize::from(total) > max;
                    st.peers_from = Some(*from);
                    st.peers_ver = Some(ver);
                    st.drop_covered_hints();
                    confirm(h, st, from, topic, &me);
                }
                None
            }
        }
    }

    /// A RESTORED frame: the hub made this member's held subscription live again.
    pub(crate) fn on_restored<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8]) {
        if self.is_boot(from) && !self.is_hub {
            h.event(Event::Restored { hub: from, topic });
            self.trace(|| Trace::RestoredSeen {
                hub: *from,
                topic: topic_tag(topic),
            });
        }
    }

    /// The number of subscribers (live or held) a hub tracks for `topic`.
    pub fn subscriber_count(&self, topic: &[u8]) -> usize {
        self.topics.get(topic).map_or(0, |st| st.subs.len().min(TABLE_MAX))
    }
}

/// ASK `hub` for the whole list of `topic`.
fn ask<H: Host>(h: &mut H, scratch: &mut Vec<u8>, hub: &NodeId, topic: &[u8]) {
    if wire::build(scratch, ty::SUBS, topic, &[&[ASK]]).is_ok() {
        h.send(hub, Lane::Main, scratch);
    }
}

/// The first list from a hub that names this member since it subscribed: the application learns a hub holds the
/// subscription, once until it leaves the topic.
fn confirm<H: Host>(h: &mut H, st: &mut Topic, from: &NodeId, topic: &[u8], me: &NodeId) {
    if st.sub && !st.confirmed && st.peers.contains(me) {
        st.confirmed = true;
        h.event(Event::Subscribed { hub: from, topic });
    }
}

/// `count | ids | tail`: the ids the count names and the bytes after them; `None` when fewer ids follow.
fn read_ids(b: &[u8]) -> Option<(&[NodeId], &[u8])> {
    let (count, rest) = b.split_first_chunk::<2>()?;
    let (ids, tail) = rest.split_at_checked(usize::from(u16::from_be_bytes(*count)).checked_mul(32)?)?;
    Some((ids.as_chunks::<32>().0, tail))
}

/// `first | total | count | ids` of a piece; `None` when it is short or names ids that cannot be in the list: more
/// than `total` ranks, or no id in a list that has some.
fn read_piece(b: &[u8]) -> Option<(u16, u16, &[NodeId])> {
    let (first, rest) = b.split_first_chunk::<2>()?;
    let (total, rest) = rest.split_first_chunk::<2>()?;
    let (first, total) = (u16::from_be_bytes(*first), u16::from_be_bytes(*total));
    let (ids, _) = read_ids(rest)?;
    let end = usize::from(first) + ids.len();
    (end <= usize::from(total) && (!ids.is_empty() || total == 0)).then_some((first, total, ids))
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    reason = "tests assert"
)]
mod tests {
    use alloc::collections::BTreeMap;
    use alloc::vec::Vec;

    use super::{Gathered, apply, delta, gather};
    use vinc_membership::NodeId;

    fn id(n: u8) -> NodeId {
        [n; 32]
    }

    /// A sorted list of the ids whose bit is set in `mask`, at most `max` of them.
    fn list(mask: u16, max: usize) -> Vec<NodeId> {
        (0..16u8).filter(|b| mask & (1 << b) != 0).map(id).take(max).collect()
    }

    /// Every pair of lists over 16 ids: the delta of `old` to `new`, applied to `old`, gives `new`, and it names
    /// each node at most once.
    #[test]
    fn a_delta_applied_gives_the_new_list() {
        for max in [3usize, 16] {
            for a in (0u16..=u16::MAX).step_by(97) {
                for b in (0u16..=u16::MAX).step_by(89) {
                    let (old, new) = (list(a, max), list(b, max));
                    let (add, rem) = delta(&old, &new);
                    assert!(add.iter().all(|n| !old.contains(n) && new.contains(n)));
                    assert!(rem.iter().all(|n| old.contains(n) && !new.contains(n)));
                    let mut got = old.clone();
                    apply(&mut got, &add, &rem, max);
                    assert_eq!(got, new);
                }
            }
        }
    }

    /// Every split of a list of 10 into non-empty pieces, fed in order, is a whole list only at the last piece, and the
    /// list is the first `max` ids with the cut known from the total. A piece out of order breaks the gathering once.
    #[test]
    fn pieces_gather_to_the_list_cut_at_max() {
        let (hub, ver) = (id(200), (7, 3));
        let all: Vec<NodeId> = (0..10).map(id).collect();
        for max in [4usize, 10, 64] {
            for cuts in 0u16..1024 {
                let mut parts = BTreeMap::new();
                let mut at = 0usize;
                let mut got = None;
                while at < 10 {
                    let len = (1..=10 - at)
                        .find(|n| at + n == 10 || cuts & (1 << (at + n)) != 0)
                        .unwrap();
                    let piece = &all[at..at + len];
                    let r = gather(&mut parts, &hub, ver, at as u16, 10, piece, max);
                    at += len;
                    if at < 10 {
                        assert_eq!(r, Gathered::Partial, "a piece that is not the last");
                    } else if len == 10 {
                        assert_eq!(r, Gathered::Whole(None), "one piece is the list itself");
                    } else {
                        got = Some(r);
                    }
                }
                if let Some(r) = got {
                    assert_eq!(r, Gathered::Whole(Some(all.iter().take(max).copied().collect())));
                }
                assert!(parts.is_empty(), "a whole list leaves no gathering");
            }
        }

        let mut parts = BTreeMap::new();
        assert_eq!(gather(&mut parts, &hub, ver, 0, 10, &all[..3], 64), Gathered::Partial);
        // A piece that skips ranks, the rest of that version, and a piece of another version all break it once.
        assert_eq!(
            gather(&mut parts, &hub, ver, 5, 10, &all[5..8], 64),
            Gathered::Gap { ask: true }
        );
        assert_eq!(
            gather(&mut parts, &hub, ver, 3, 10, &all[3..6], 64),
            Gathered::Gap { ask: false }
        );
        // A first piece starts over.
        assert_eq!(gather(&mut parts, &hub, ver, 0, 10, &all[..3], 64), Gathered::Partial);
        assert_eq!(
            gather(&mut parts, &hub, (7, 4), 3, 10, &all[3..6], 64),
            Gathered::Gap { ask: true }
        );
        // A piece of a list whose first piece never came.
        assert_eq!(
            gather(&mut parts, &id(201), ver, 3, 10, &all[3..6], 64),
            Gathered::Gap { ask: true }
        );
        // Two hubs gather apart.
        assert_eq!(gather(&mut parts, &hub, ver, 0, 10, &all[..3], 64), Gathered::Partial);
        assert_eq!(
            gather(&mut parts, &id(201), ver, 0, 10, &all[..5], 64),
            Gathered::Partial
        );
        assert_eq!(
            gather(&mut parts, &hub, ver, 3, 10, &all[3..10], 64),
            Gathered::Whole(Some(all.clone()))
        );
    }
}
