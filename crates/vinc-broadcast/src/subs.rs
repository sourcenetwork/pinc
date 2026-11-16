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
//! are sent the hub's local set whole, when it changes. Deltas keep the bytes a change costs a recipient independent
//! of the number of subscribers: the whole list on every change made the join of `n` subscribers cost `n` lists of up
//! to `max_subscribers` nodes on every session. A SUBS frame that changes nothing is traced with why
//! ([`Trace::SubsDropped`]).
//!
//! Invariants: a list holds at most `max_subscribers` nodes in id order, so two hubs with the same tables send the
//! same bytes; `told` is the list built from the tables after every change, and `(incarnation, told_seq)` its
//! version; a member's list is always the list its hub had at the version the member holds: a delta is applied only
//! on its own base, and only from the hub of the member's list (a change from the primary makes it the hub of the
//! list, and the member asks it for the whole list), a join hint never enters it, and a member whose limit
//! cut the list asks for the whole list on a change that removes (the id past the cut is not in the change); `stale`
//! holds only recipients, and `Topics::owed` holds every recipient stale in some topic, so a stream's room is a lookup,
//! not a walk of the topics; a held member receives no push; a restore tells the member exactly the topics it had; a
//! release of a member that was behind in a topic leaves the span of what it was owed in that topic.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use vinc_membership::NodeId;

use crate::consts::TABLE_MAX;
use crate::event::{SubsDrop, Trace, topic_tag};
use crate::host::{Event, Host, Lane};
use crate::node::{Topic, Topics};
use crate::wire::{self, ty};

/// How many recent publishers a hub tells the subscriber list of one topic.
const PUBS_MAX: usize = 256;

/// A SUBS frame that carries the whole list (`version | count | ids`): the receiver replaces its own.
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

/// A FULL frame of `list` at version `ver` in `scratch`. An empty list is sent too, so a node that knew subscribers
/// learns they are gone.
fn full_frame(scratch: &mut Vec<u8>, topic: &[u8], ver: Ver, list: &[NodeId]) -> bool {
    wire::build(
        scratch,
        ty::SUBS,
        topic,
        &[&[FULL], &ver_bytes(ver), &count(list.len()), list.as_flattened()],
    )
    .is_ok()
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

/// Bring the recipients of `topic` to the current list: a delta to those that are not stale, then the whole list to
/// the stale ones. A recipient whose stream refuses its frame is stale until one takes the whole list. `inc` is the
/// hub's incarnation, the first half of every version it sends.
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
        let built = wire::build(scratch, ty::SUBS, topic, &parts).is_ok();
        let live = st.subs.iter().filter(|(_, l)| **l).map(|(p, _)| p);
        let others = st.pubs.iter().filter(|p| !st.subs.contains_key(*p));
        let mut refused = Vec::new();
        for p in live.chain(others).filter(|p| !st.stale.contains(*p)) {
            if !built || !h.send(p, Lane::Reply, scratch) {
                refused.push(*p);
            }
        }
        st.stale.extend(refused);
        st.told.clone_from(nodes);
    }
    flush_stale(h, scratch, owed, topic, st, None, inc);
}

/// Send the whole list to the stale recipients of `st`, or only to `only`; a recipient whose stream took it is no
/// longer stale. A stale entry that is no longer a recipient is dropped: it is sent nothing, and the whole list again
/// if it comes back. Every recipient still stale afterwards is in `owed`, so its stream's room brings it the list.
fn flush_stale<H: Host>(
    h: &mut H,
    scratch: &mut Vec<u8>,
    owed: &mut BTreeSet<NodeId>,
    topic: &[u8],
    st: &mut Topic,
    only: Option<&NodeId>,
    inc: u64,
) {
    let gone: Vec<NodeId> = st.stale.iter().filter(|p| !is_recipient(st, p)).copied().collect();
    for p in &gone {
        st.stale.remove(p);
    }
    if !st.stale.is_empty() && full_frame(scratch, topic, (inc, st.told_seq), &st.told) {
        st.stale
            .retain(|p| only.is_some_and(|o| o != p) || !h.send(p, Lane::Reply, scratch));
    }
    owed.extend(st.stale.iter().copied());
}

/// Tell the recipients of `topic` what changed, and, when the local set changed, the other hubs the local set.
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
    if local_changed {
        build_list(nodes, st, true, max);
        // The other hub keeps this set whole and does not read its version.
        if full_frame(scratch, topic, (inc, st.told_seq), nodes) {
            for hub in hubs {
                h.send(hub, Lane::Main, scratch);
            }
        }
    }
}

impl Topic {
    /// Forget the hints a hub's list names: the list covers them, and no node is in both.
    fn drop_covered_hints(&mut self) {
        let peers = &self.peers;
        self.hints.retain(|n| !peers.contains(n));
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
    /// is a recipient that must be sent the whole list (a subscriber that just subscribed, again or for the first time).
    pub(crate) fn announce_topic<H: Host>(
        &mut self,
        h: &mut H,
        topic: &[u8],
        local_changed: bool,
        fresh: Option<&NodeId>,
    ) {
        if let Some(st) = self.topics.get_mut(topic) {
            if let Some(f) = fresh {
                st.stale.insert(*f);
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
        st.stale.insert(*from);
        flush_stale(h, &mut self.scratch, &mut self.owed, topic, st, Some(from), self.inc);
    }

    /// The stream of `peer` has room again: send it the whole list of every topic it is stale in. A peer no stream
    /// refused a list costs a lookup in `owed`, not a walk of the topic table.
    pub(crate) fn subs_writable<H: Host>(&mut self, h: &mut H, peer: &NodeId) {
        if !self.owed.remove(peer) {
            return;
        }
        for (k, st) in &mut self.topics {
            if st.stale.contains(peer) {
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
                st.stale.insert(*member);
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

    /// A SUBS frame. A hub answers a recipient's ASK with the whole list, and keeps another hub's local set (always
    /// whole) and tells its own recipients what changed in the union. A member replaces its list with a whole one and
    /// remembers which hub sent it and its version; it applies a delta only from that hub and only on the version it
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

    /// [`Topics::on_subs`] but the trace: why the frame changed nothing, if it did not. Every field the sender
    /// controls is checked before any state changes; an off-base change still asks for the whole list.
    fn take_subs<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8], rest: &[u8]) -> Option<SubsDrop> {
        let Some((kind, rest)) = rest.split_first() else {
            return Some(SubsDrop::Malformed);
        };
        if *kind == ASK {
            let is_hub = self.is_hub;
            let Some(st) = self.topics.get_mut(topic).filter(|st| is_hub && is_recipient(st, from)) else {
                return Some(SubsDrop::NotRecipient);
            };
            st.stale.insert(*from);
            flush_stale(h, &mut self.scratch, &mut self.owed, topic, st, Some(from), self.inc);
            return None;
        }
        if !self.is_boot(from) {
            return Some(SubsDrop::NotHub);
        }
        let parsed = read_ver(rest).and_then(|(ver, r)| read_ids(r).map(|(ids, tail)| (ver, ids, tail)));
        let Some((ver, ids, tail)) = parsed else {
            return Some(SubsDrop::Malformed);
        };
        let rem = read_ids(tail).map(|(rem, _)| rem);
        let (is_hub, inc, me) = (self.is_hub, self.inc, self.me);
        if !(*kind == FULL || (*kind == DELTA && !is_hub && rem.is_some())) {
            return Some(SubsDrop::Malformed);
        }
        if !self.ensure_topic(topic) {
            return Some(SubsDrop::TopicsFull);
        }
        let (max, primary) = (self.limits.max_subscribers, self.primary);
        let st = self.topics.get_mut(topic)?;
        match (*kind, rem) {
            (FULL, _) if is_hub => {
                let e = st.rsubs.entry(*from).or_default();
                e.clear();
                e.extend(ids.iter().take(max).copied());
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
                None
            }
            (FULL, _) => {
                st.peers.clear();
                st.peers.extend(ids.iter().take(max).copied());
                st.peers_cut = ids.len() > max;
                st.peers_from = Some(*from);
                st.peers_ver = Some(ver);
                st.drop_covered_hints();
                confirm(h, st, from, topic, &me);
                None
            }
            // A change from the primary after a late whole list of another hub: the primary is the source, whatever
            // the list came from, so the member asks it for its whole list.
            _ if st.peers_from != Some(*from) => {
                if primary == Some(*from) {
                    st.peers_from = Some(*from);
                    st.peers_ver = None;
                    ask(h, &mut self.scratch, from, topic);
                }
                Some(SubsDrop::OtherHub)
            }
            // A removal from a list cut below the hub's brings an id the member never saw into the hub's cut: only the
            // whole list tells which.
            // Not newer than the version held: a late frame of an old session, nothing to apply or to ask for.
            _ if st
                .peers_ver
                .is_some_and(|(e, s)| e == ver.0 && s.wrapping_sub(ver.1) < 1 << 31) =>
            {
                Some(SubsDrop::Old)
            }
            (_, Some(rem))
                if st.peers_ver == Some((ver.0, ver.1.wrapping_sub(1))) && (!st.peers_cut || rem.is_empty()) =>
            {
                st.peers_cut |= apply(&mut st.peers, ids, rem, max);
                st.peers_ver = Some(ver);
                st.drop_covered_hints();
                confirm(h, st, from, topic, &me);
                None
            }
            _ => {
                // A missed change: the member waits for a whole list and asks once; changes meanwhile are dropped.
                if st.peers_ver.take().is_some() {
                    ask(h, &mut self.scratch, from, topic);
                }
                Some(SubsDrop::OffBase)
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

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;

    use super::{apply, delta};
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
}
