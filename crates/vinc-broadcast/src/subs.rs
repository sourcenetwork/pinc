//! The subscriber tables of a hub: held, restored and forgotten subscriptions, and the replication of the
//! subscriber set to the members, which the member-to-member fallback needs.
//!
//! Membership tells the hub what happened to a member: [`Topics::hold`] when it is confirmed down (its subscriptions
//! are kept for the lease and nothing is pushed to it), [`Topics::restore`] when it returns within the lease (the
//! subscriptions are live again and the member is told, one RESTORED per topic), [`Topics::release`] when it is gone
//! for good. Whenever the live subscribers of a topic change, the hub tells the subscribers and the recent
//! publishers the full set (SUBS), and the other hubs its local set, so that a member cut off from every hub still
//! knows whom to reach.
//!
//! Invariants: a SUBS frame lists at most `max_subscribers` nodes in id order, so two hubs with the same tables send the
//! same bytes; a held member receives no push; a restore tells the member exactly the topics it had.

use alloc::vec::Vec;
use vinc_membership::NodeId;

use crate::consts::TABLE_MAX;
use crate::event::{Trace, topic_tag};
use crate::host::{Event, Host, Lane};
use crate::node::{Topic, Topics};
use crate::wire::{self, ty};

/// How many recent publishers a hub tells the subscriber set of one topic.
const PUBS_MAX: usize = 256;

/// Lay the SUBS frame of `st` in `scratch`: the union of the live local subscribers and the other hubs' reports
/// (or only the local ones), in id order. An empty set is sent too, so a node that knew subscribers learns they are
/// gone.
fn build_subs(
    scratch: &mut Vec<u8>,
    nodes: &mut Vec<NodeId>,
    st: &Topic,
    topic: &[u8],
    local_only: bool,
    max: usize,
) -> bool {
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
    let count = u16::try_from(nodes.len()).unwrap_or(u16::MAX).to_be_bytes();
    wire::build(scratch, ty::SUBS, topic, &[&count, nodes.as_flattened()]).is_ok()
}

/// Tell the members of `topic` the subscriber set, and the other hubs the local one.
// vertexia: the whole set is pushed on every change, O(subscribers) frames of O(subscribers) bytes, bounded by
// the configured `max_subscribers`; delta frames if topics should carry thousands of subscribers.
fn announce<H: Host>(
    h: &mut H,
    scratch: &mut Vec<u8>,
    nodes: &mut Vec<NodeId>,
    hubs: &[NodeId],
    topic: &[u8],
    st: &Topic,
    max: usize,
) {
    if build_subs(scratch, nodes, st, topic, false, max) {
        let live = st.subs.iter().filter(|(_, l)| **l).map(|(p, _)| p);
        let others = st.pubs.iter().filter(|p| !st.subs.contains_key(*p));
        for p in live.chain(others) {
            h.send(p, Lane::Reply, scratch);
        }
    }
    if build_subs(scratch, nodes, st, topic, true, max) {
        for hub in hubs {
            h.send(hub, Lane::Main, scratch);
        }
    }
}

impl Topics {
    /// Replicate the subscriber set of `topic` after a change.
    pub(crate) fn announce_topic<H: Host>(&mut self, h: &mut H, topic: &[u8]) {
        if let Some(st) = self.topics.get(topic) {
            announce(
                h,
                &mut self.scratch,
                &mut self.nodes,
                &self.hubs,
                topic,
                st,
                self.limits.max_subscribers,
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
        let Some(st) = self.topics.get(topic) else {
            return;
        };
        if build_subs(
            &mut self.scratch,
            &mut self.nodes,
            st,
            topic,
            false,
            self.limits.max_subscribers,
        ) && !self.nodes.is_empty()
        {
            h.send(from, Lane::Reply, &self.scratch);
        }
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
                    &self.hubs,
                    k,
                    st,
                    self.limits.max_subscribers,
                );
            }
        }
        if any {
            self.trace(|| Trace::SubsHeld { member: *member });
        }
    }

    /// `member` returned within the lease: its held subscriptions are live again, and it is told which.
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
                announce(
                    h,
                    &mut self.scratch,
                    &mut self.nodes,
                    &self.hubs,
                    k,
                    st,
                    self.limits.max_subscribers,
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

    /// `member` is gone for good: forget its subscriptions. Its adjacency record goes once it expired and no log holds
    /// a message of it.
    pub fn release<H: Host>(&mut self, h: &mut H, member: &NodeId) {
        self.reach.leave(member);
        let mut any = false;
        for (k, st) in &mut self.topics {
            let was_pub = st.pubs.remove(member);
            st.behind.remove(member);
            if st.subs.remove(member).is_some() {
                any = true;
                announce(
                    h,
                    &mut self.scratch,
                    &mut self.nodes,
                    &self.hubs,
                    k,
                    st,
                    self.limits.max_subscribers,
                );
            } else {
                any |= was_pub;
            }
        }
        if any {
            self.trace(|| Trace::SubsReleased { member: *member });
        }
    }

    /// A SUBS frame from a hub: a hub keeps the other hubs' sets and passes the union on to its members; a member
    /// keeps the set for the fallback.
    pub(crate) fn on_subs<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8], rest: &[u8]) {
        if !self.is_boot(from) || !self.ensure_topic(topic) {
            return;
        }
        let Some((count, ids)) = rest.split_first_chunk::<2>() else {
            return;
        };
        let n = usize::from(u16::from_be_bytes(*count)).min(self.limits.max_subscribers);
        let list = ids.as_chunks::<32>().0.iter().take(n);
        let is_hub = self.is_hub;
        let me = self.me;
        let Some(st) = self.topics.get_mut(topic) else {
            return;
        };
        if is_hub {
            let e = st.rsubs.entry(*from).or_default();
            e.clear();
            e.extend(list.copied());
        } else {
            // vertexia: the last report wins; a per-hub merge if hubs disagree for long.
            st.peers.clear();
            st.peers.extend(list.copied());
            if st.sub && !st.confirmed && st.peers.contains(&me) {
                st.confirmed = true;
                h.event(Event::Subscribed { hub: from, topic });
            }
        }
        if is_hub
            && let Some(st) = self.topics.get(topic)
            && build_subs(
                &mut self.scratch,
                &mut self.nodes,
                st,
                topic,
                false,
                self.limits.max_subscribers,
            )
        {
            for p in st
                .subs
                .iter()
                .filter(|(_, l)| **l)
                .map(|(p, _)| p)
                .chain(st.pubs.iter())
            {
                h.send(p, Lane::Reply, &self.scratch);
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
