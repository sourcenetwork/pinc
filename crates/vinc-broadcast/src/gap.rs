//! Subscriptions and gap repair: SUB(since), then HAVE, then GET, then MSG.
//!
//! A subscriber tells its primary hub the time it wants the topic from (`since`, in the wall-clock milliseconds the
//! hub stamps its log with). The hub answers with the ids it logged since (HAVE), or with the messages themselves
//! when the subscriber asks for a replay (flag 1 on SUB, `REPLAY_PUSH`): all of them, oldest first, bounded by the log
//! and paced by the subscriber's stream. The subscriber asks for the ids it lacks
//! (GET) and the hub sends them (MSG). A periodic check (`GAP_AE`) repeats the question while a topic is live, so a
//! message a dead session swallowed is fetched; hubs also exchange the ids of their logs (HAVE) every [`HUB_AE`].
//!
//! A hub offers every id of the span it is asked about or exchanges, in as many HAVE frames as that takes, so a node
//! that was cut off learns of everything the log still holds, not only of the newest ids.
//!
//! A message a GET or a replay asks for that the subscriber's stream has no room for is not dropped: the subscriber
//! is behind from it (`behind.rs`), let go from the start so that a repair never paces the topic, and is sent the
//! log from that place, in order, when its stream has room; if the log evicted any of it by then it is told with
//! RESTORED. So a gap larger than a stream takes is repaired whole, not a stream-full for each periodic check.
//!
//! A hub that cannot give a subscriber everything it asks for says so (RESTORED, `Event::Restored` at the
//! subscriber), once for the subscription or the request. That is the case when a SUB that makes the member a live
//! subscriber, or the replay a restarted member asks for from its floor, asks from a time at or before a message the
//! log has dropped since (evicted or expired; the floor's own message counts, so a member that restarts after the log
//! let go of the last message it was sent is told although nothing else may be missing). Or when it asks from a time
//! the answer does not reach back from to a message the hub owed a subscriber whose session ended while it was
//! behind: after that message was logged and no later than the hub forgot the place (`Topic::forgot`; the subscriber
//! that was behind asks from before its session ended, so it is told unless its answer covers what it was owed; the
//! hub keeps one span for the topic and no record of the member). And when a GET names an id the log no longer
//! holds. A subscriber that subscribes for the first time asks from now and is not told. A live subscriber's
//! periodic check is not judged: it was pushed everything since it became live, or is behind and told from there.
//!
//! Invariants: a HAVE and a GET carry at most [`HAVE_MAX`] ids; a GET names only ids the node lacks; a replay sends
//! every message the log holds since the floor, oldest first, and never a member's own back to it; a message asked
//! for by a subscriber whose stream is full is owed from the log, never dropped; a live subscriber that asked for a
//! message the log dropped is told, and the notice waits for room in its stream as a message does.

use vinc_membership::{Nanos, NodeId};

use alloc::vec::Vec;

use crate::behind::Behind;
use crate::consts::{
    AE_FROM, AE_TO, GAP_EVERY, GAP_LIVE, GAP_SPAN, HAVE_MAX, HUB_AE, LOG_CAP, RESUB_BACK_MS, TABLE_MAX,
};
use crate::event::{Trace, topic_tag};
use crate::host::{Host, Lane};
use crate::log::HubLog;
use crate::node::{Refused, Topic, Topics, TraceQueue};
use crate::reach::{offers, reaches};
use crate::wire::{self, Head, get_u64, ty};

/// Offer `mids` to `peers` as HAVE frames: every id, [`HAVE_MAX`] to a frame, oldest first. `sent` hears the peer and
/// the id count of each frame. A log holds at most [`LOG_CAP`] messages, so an offer is at most four frames a peer.
fn offer<H: Host>(
    h: &mut H,
    ids: &mut Vec<u8>,
    scratch: &mut Vec<u8>,
    peers: &[NodeId],
    topic: &[u8],
    mids: impl Iterator<Item = u64>,
    mut sent: impl FnMut(&NodeId, u16),
) {
    let mut mids = mids.peekable();
    while mids.peek().is_some() {
        ids.clear();
        for mid in mids.by_ref().take(HAVE_MAX) {
            ids.extend_from_slice(&mid.to_le_bytes());
        }
        if wire::build(scratch, ty::HAVE, topic, &[ids]).is_err() {
            return;
        }
        let count = u16::try_from(ids.len() / 8).unwrap_or(u16::MAX);
        for p in peers {
            h.send(p, Lane::Reply, scratch);
            sent(p, count);
        }
    }
}

impl Topics {
    // vertexia: `since` is a wall-clock instant compared with the hub's wall clock, so a skewed clock shifts the
    // window it asks for (HAVE and GET still dedupe); an age relative to the hub's own clock removes the skew.
    /// The point in time a (re)subscription asks the hub to log back to.
    fn since_ms(&self) -> u64 {
        let base = self.gather.rfloor.map_or(self.born_wall, |f| f.wall);
        // Back to 15 s before the last message the hub pushed, and no later than the point up to which the periodic
        // checks form an unbroken chain from the start: a message swallowed before a newer one arrived, or on a topic
        // the checks skipped as quiet, would otherwise fall out of every window when a link flap skips a check.
        if self.last_rx_wall == 0 {
            return base;
        }
        base.max(self.last_rx_wall.saturating_sub(RESUB_BACK_MS).min(self.last_gap_wall))
    }

    pub(crate) fn send_sub<H: Host>(&mut self, h: &mut H, hub: &NodeId, topic: &[u8], since_ms: u64, replay: bool) {
        if *hub == self.me {
            return;
        }
        let since = since_ms.to_be_bytes();
        let flag = [1u8];
        let parts: &[&[u8]] = if replay { &[&since, &flag] } else { &[&since] };
        if wire::build(&mut self.scratch, ty::SUB, topic, parts).is_ok() {
            h.send(hub, Lane::Main, &self.scratch);
            self.trace(|| Trace::SubSent {
                hub: *hub,
                topic: topic_tag(topic),
                since_ms,
                replay,
            });
        }
    }

    /// Subscribe to `topic`.
    ///
    /// # Errors
    /// [`Refused`] for a topic over 255 bytes or a full topic table.
    pub fn subscribe<H: Host>(&mut self, h: &mut H, _now: Nanos, topic: &[u8]) -> Result<(), Refused> {
        if topic.len() > crate::consts::MAX_TOPIC {
            return Err(Refused::TopicTooLong);
        }
        let st = self.topic(topic).ok_or(Refused::TopicsFull)?;
        if !st.sub {
            st.sub = true;
            st.confirmed = false;
            if let Some(p) = self.primary {
                let since = h.wall_ms();
                self.send_sub(h, &p, topic, since, false);
            }
        }
        Ok(())
    }

    /// Unsubscribe from `topic`.
    pub fn unsubscribe<H: Host>(&mut self, h: &mut H, topic: &[u8]) {
        let Some(st) = self.topics.get_mut(topic) else {
            return;
        };
        if !core::mem::replace(&mut st.sub, false) {
            return;
        }
        st.confirmed = false;
        if let Some(p) = self.primary.filter(|p| *p != self.me)
            && wire::build(&mut self.scratch, ty::UNSUB, topic, &[]).is_ok()
        {
            h.send(&p, Lane::Main, &self.scratch);
        }
    }

    /// Ask `hub` again for every subscribed topic from `since_ms`.
    fn resub_all<H: Host>(&mut self, h: &mut H, hub: &NodeId, since_ms: u64) {
        let topics = core::mem::take(&mut self.topics);
        for (k, st) in &topics {
            if st.sub {
                self.send_sub(h, hub, k, since_ms, false);
            }
        }
        self.topics = topics;
    }

    /// Membership asks the node to subscribe again at `hub` (a snapshot, a new session or a restored entry).
    pub fn resubscribe<H: Host>(&mut self, h: &mut H, now: Nanos, hub: &NodeId) {
        // The hub hears whom this node is connected to before it answers the subscriptions.
        if self.is_boot(hub) {
            self.send_adj(h, Some(hub));
        }
        if !self.is_hub && self.primary == Some(*hub) {
            let since = self.since_ms();
            self.resub_all(h, hub, since);
        }
        // A new session has a new stream: the publishes that waited for room in the old one go out now.
        self.send_unsent(h, now, hub);
    }

    /// The primary hub changed: leave the old one and subscribe at the new one with gap repair.
    pub fn primary_changed<H: Host>(&mut self, h: &mut H, _now: Nanos, old: Option<&NodeId>, new: &NodeId) {
        self.primary = Some(*new);
        self.trace(|| Trace::Primary { hub: *new });
        if self.is_hub {
            return;
        }
        if self.is_boot(new) {
            self.send_adj(h, Some(new));
        }
        let since = self.since_ms();
        let topics = core::mem::take(&mut self.topics);
        for (k, st) in &topics {
            if !st.sub {
                continue;
            }
            if let Some(o) = old.filter(|o| **o != self.me && h.hub_up(o))
                && wire::build(&mut self.scratch, ty::UNSUB, k, &[]).is_ok()
            {
                h.send(o, Lane::Reply, &self.scratch);
            }
            self.send_sub(h, new, k, since, false);
        }
        self.topics = topics;
    }

    /// The floors are known: replay the topics from the floor at the primary hub.
    pub(crate) fn replay_subscriptions<H: Host>(&mut self, h: &mut H, floor_ms: u64) {
        let Some(p) = self.primary.filter(|p| *p != self.me) else {
            return;
        };
        let topics = core::mem::take(&mut self.topics);
        for (k, st) in &topics {
            if st.sub {
                self.send_sub(h, &p, k, floor_ms, true);
            }
        }
        self.topics = topics;
    }

    /// `GAP_AE`: while a topic is live, ask the primary again for the ids it logged in the last [`GAP_SPAN`].
    pub(crate) fn gap_ae<H: Host>(&mut self, h: &mut H, now: Nanos) {
        if self.is_hub || now < self.next_gap {
            return;
        }
        self.next_gap = now.saturating_add(GAP_EVERY);
        let Some(p) = self.primary.filter(|p| *p != self.me && h.hub_up(p)) else {
            return;
        };
        let floor = self.gather.rfloor.map_or(self.born_wall, |f| f.wall);
        let since = h.wall_ms().saturating_sub(GAP_SPAN / 1_000_000).max(floor);
        let wall = h.wall_ms();
        let topics = core::mem::take(&mut self.topics);
        let mut asked = false;
        for (k, st) in &topics {
            if st.sub && st.seen.newest().is_some_and(|t| now.saturating_sub(t) < GAP_LIVE) {
                self.send_sub(h, &p, k, since, false);
                asked = true;
            }
        }
        self.topics = topics;
        // The check reaches back GAP_SPAN: it extends the chain only if it overlaps the point the chain reached.
        if asked && wall.saturating_sub(GAP_SPAN / 1_000_000) <= self.last_gap_wall {
            self.last_gap_wall = wall;
        }
    }

    /// Hub-to-hub HAVE: tell the other hubs the ids logged in `[-30 s, -1 s]`.
    pub(crate) fn hub_ae<H: Host>(&mut self, h: &mut H, now: Nanos) {
        if !self.is_hub || now < self.next_ae {
            return;
        }
        // Stay on the 5 s grid that began at start, however long the hub idled without a log.
        let behind = now.saturating_sub(self.next_ae);
        self.next_ae = self.next_ae.saturating_add((behind / HUB_AE + 1) * HUB_AE);
        let up: Vec<NodeId> = self.hubs.iter().filter(|x| h.hub_up(x)).copied().collect();
        let topics = core::mem::take(&mut self.topics);
        for (k, st) in &topics {
            let Some(log) = st.log.as_ref().filter(|l| l.len() > 0) else {
                continue;
            };
            let tq = &mut self.tq;
            offer(
                h,
                &mut self.ids,
                &mut self.scratch,
                &up,
                k,
                log.window(now, AE_FROM, AE_TO),
                |peer, count| {
                    tq.push(|| Trace::HaveSent {
                        peer: *peer,
                        topic: topic_tag(k),
                        count,
                    });
                },
            );
        }
        self.topics = topics;
    }

    /// A hub offers `member` the ids it logged in the last `span` for each topic the member subscribes to: the host
    /// adopted another session of the member, and what went out on the closed session may be lost.
    pub fn have_to<H: Host>(&mut self, h: &mut H, now: Nanos, member: &NodeId, span: Nanos) {
        if !self.is_hub {
            return;
        }
        let topics = core::mem::take(&mut self.topics);
        for (k, st) in &topics {
            let Some(log) = st.log.as_ref().filter(|_| st.subs.contains_key(member)) else {
                continue;
            };
            let to = [*member];
            let reach = &self.reach;
            let mids = log.window(now, span, 0).filter(|m| offers(reach, log, *m, member));
            offer(h, &mut self.ids, &mut self.scratch, &to, k, mids, |_, _| {});
        }
        self.topics = topics;
    }

    /// A SUB at a hub: record the subscriber and answer with HAVE, or replay the messages when flag 1 is set.
    pub(crate) fn on_sub<H: Host>(&mut self, h: &mut H, now: Nanos, from: &NodeId, topic: &[u8], rest: &[u8]) {
        let Some(since) = get_u64(rest).filter(|_| self.is_hub && *from != self.me) else {
            return;
        };
        // A subscriber this hub keeps behind subscribes again on a new session, whose stream no host reports writable
        // (only a full stream that drains is): it goes on from its place in the log now, and is pushed live once
        // caught up.
        if self.lagging.contains(from) {
            self.peer_writable(h, now, from);
        }
        let replay = rest.get(8) == Some(&1);
        if !self.ensure_topic(topic) {
            return;
        }
        let Some(st) = self.topics.get_mut(topic) else {
            return;
        };
        let changed = if st.subs.contains_key(from) || st.subs.len() < TABLE_MAX {
            st.subs.insert(*from, true) != Some(true)
        } else {
            false
        };
        // The member becomes a live subscriber, or a new life of it replays from its floor, and asks from a time the
        // hub cannot serve in full: the log dropped a message logged since then, or the time lies after a message the
        // hub owed a subscriber whose session ended and before the hub forgot that place, so the answer does not
        // reach back to the message.
        let short =
            (changed || replay) && (st.log.as_ref().is_some_and(|l| l.dropped_since(since)) || st.forgot_since(since));
        let mut owed = None;
        if let Some(log) = st.log.as_ref() {
            if replay {
                // Every message the log holds since the floor, oldest first, as far as the stream takes; the rest is
                // owed below. (The reference model pushes the newest 256 and nothing of the others.)
                for mid in log.since(since) {
                    let Some(l) = log.get(mid) else { continue };
                    let Ok((head, _)) = Head::parse(l) else {
                        continue;
                    };
                    if head.origin == from
                        || !reaches(&self.reach, head.origin, from)
                        || wire::build(&mut self.scratch, ty::MSG, topic, &[l]).is_err()
                    {
                        continue;
                    }
                    if h.send(from, Lane::Reply, &self.scratch) {
                        self.sent.note(from, head.ts, head.origin);
                    } else if h.backlogged(from, self.scratch.len()) {
                        // The stream is full: the rest of the replay is owed from the log, in order.
                        owed = log.seq_of(mid);
                        break;
                    }
                }
            } else {
                let tq = &mut self.tq;
                let to = [*from];
                offer(
                    h,
                    &mut self.ids,
                    &mut self.scratch,
                    &to,
                    topic,
                    log.since(since).filter(|m| offers(&self.reach, log, *m, from)),
                    |peer, count| {
                        tq.push(|| Trace::HaveSent {
                            peer: *peer,
                            topic: topic_tag(topic),
                            count,
                        });
                    },
                );
            }
        }
        if let Some(next) = owed {
            let wall = h.wall_ms();
            if let Some(st) = self.topics.get_mut(topic) {
                owe(st, &mut self.lagging, from, next, wall);
            }
        }
        if short && let Some(st) = self.topics.get_mut(topic) {
            tell_short(h, &mut self.scratch, &mut self.tq, st, &mut self.lagging, from, topic);
        }
        if changed {
            self.announce_topic(h, topic);
        }
    }

    /// An UNSUB at a hub.
    pub(crate) fn on_unsub<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8]) {
        if self.is_hub
            && self.topics.get_mut(topic).is_some_and(|st| {
                st.behind.remove(from);
                st.subs.remove(from).is_some()
            })
        {
            self.announce_topic(h, topic);
        }
    }

    /// A HAVE from a hub: ask for the ids this node lacks.
    pub(crate) fn on_have<H: Host>(&mut self, h: &mut H, now: Nanos, from: &NodeId, topic: &[u8], rest: &[u8]) {
        if !self.is_boot(from) || !self.ensure_topic(topic) {
            return;
        }
        let Some(st) = self.topics.get_mut(topic) else {
            return;
        };
        self.ids.clear();
        for mid in rest.as_chunks::<8>().0 {
            let key = u64::from_le_bytes(*mid);
            if self.ids.len() < 8 * HAVE_MAX
                && !st.seen.contains(key, now)
                && !st.log.as_ref().is_some_and(|l| l.contains(key))
            {
                self.ids.extend_from_slice(mid);
                if st.requested.len() >= LOG_CAP {
                    st.requested.clear();
                }
                st.requested.insert(*mid);
            }
        }
        if !self.ids.is_empty() && wire::build(&mut self.scratch, ty::GET, topic, &[&self.ids]).is_ok() {
            h.send(from, Lane::Reply, &self.scratch);
            let count = u16::try_from(self.ids.len() / 8).unwrap_or(u16::MAX);
            self.trace(|| Trace::GetSent {
                peer: *from,
                topic: topic_tag(topic),
                count,
            });
        }
    }

    /// A GET at a hub: send the messages behind the ids it still holds. Once the subscriber's stream has no room, the
    /// message it refused and the ones asked for after it are owed from the log (the earliest of them is the
    /// subscriber's place), not dropped. A subscriber that names an id the log dropped since it was offered is told.
    pub(crate) fn on_get<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8], rest: &[u8]) {
        let wall = h.wall_ms();
        let Some(st) = self.topics.get_mut(topic) else {
            return;
        };
        let Some(log) = st.log.as_ref() else {
            return;
        };
        // The place of the earliest message asked for that found the stream full.
        let mut owed: Option<u64> = None;
        let mut dropped = false;
        for mid in rest.get(..8 * HAVE_MAX).unwrap_or(rest).as_chunks::<8>().0 {
            let key = u64::from_le_bytes(*mid);
            let Some(l) = log.get(key) else {
                dropped = true;
                continue;
            };
            let Ok((head, _)) = Head::parse(l) else {
                continue;
            };
            if !reaches(&self.reach, head.origin, from) {
                continue;
            }
            if owed.is_none() {
                if wire::build(&mut self.scratch, ty::MSG, topic, &[l]).is_err() {
                    continue;
                }
                if h.send(from, Lane::Reply, &self.scratch) {
                    self.sent.note(from, head.ts, head.origin);
                    continue;
                }
                if !h.backlogged(from, self.scratch.len()) {
                    // The session is gone, or the host cannot tell: the next HAVE asks again, as before.
                    continue;
                }
            }
            if let Some(seq) = log.seq_of(key) {
                owed = Some(owed.map_or(seq, |o| o.min(seq)));
            }
        }
        if let Some(next) = owed {
            owe(st, &mut self.lagging, from, next, wall);
        }
        if dropped {
            tell_short(h, &mut self.scratch, &mut self.tq, st, &mut self.lagging, from, topic);
        }
    }
}

/// Tell `peer`, a live subscriber, that the hub cannot give it every message of `topic` it asked for (RESTORED). The
/// notice is owed like a message: a subscriber that is behind is told once it has caught up, and one whose stream has
/// no room for the notice is behind at the end of the log, let go, until it has. If its session is gone the topic
/// keeps the time, and it is told when it subscribes again.
fn tell_short<H: Host>(
    h: &mut H,
    scratch: &mut Vec<u8>,
    tq: &mut TraceQueue,
    st: &mut Topic,
    lagging: &mut alloc::collections::BTreeSet<NodeId>,
    peer: &NodeId,
    topic: &[u8],
) {
    if st.subs.get(peer) != Some(&true) {
        return;
    }
    tq.push(|| Trace::Short {
        peer: *peer,
        topic: topic_tag(topic),
    });
    if let Some(b) = st.behind.get_mut(peer) {
        b.lost = true;
        return;
    }
    if wire::build(scratch, ty::RESTORED, topic, &[]).is_err() || h.send(peer, Lane::Reply, scratch) {
        return;
    }
    let wall = h.wall_ms();
    match st.log.as_ref().map(HubLog::end) {
        Some(next) if h.backlogged(peer, scratch.len()) => {
            st.behind.insert(
                *peer,
                Behind {
                    next,
                    progress_ms: wall,
                    held: true,
                    lost: true,
                },
            );
            lagging.insert(*peer);
        }
        _ => st.note_forgot(0, wall),
    }
}

/// `peer`'s stream had no room for a logged message it asked for: `peer` is behind from sequence number `next` of the
/// topic's log, or from its earlier place if it has one, let go from the start (a repair never holds back the log).
/// Only a live subscriber has a place.
fn owe(st: &mut Topic, lagging: &mut alloc::collections::BTreeSet<NodeId>, peer: &NodeId, next: u64, wall_ms: u64) {
    if st.subs.get(peer) != Some(&true) {
        return;
    }
    let b = st.behind.entry(*peer).or_insert(Behind {
        next,
        progress_ms: wall_ms,
        held: true,
        lost: false,
    });
    b.next = b.next.min(next);
    lagging.insert(*peer);
}
