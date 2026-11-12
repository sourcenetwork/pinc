//! Subscriptions and gap repair: SUB(since), then HAVE, then GET, then MSG.
//!
//! A subscriber tells its primary hub the time it wants the topic from (`since`, in the wall-clock milliseconds the
//! hub stamps its log with). The hub answers with the ids it logged since (HAVE), or with the messages themselves
//! when the subscriber asks for a replay (flag 1 on SUB, `REPLAY_PUSH`). The subscriber asks for the ids it lacks
//! (GET) and the hub sends them (MSG). A periodic check (`GAP_AE`) repeats the question while a topic is live, so a
//! message a dead session swallowed is fetched; hubs also exchange the ids of their logs (HAVE) every [`HUB_AE`].
//!
//! Invariants: a HAVE and a GET carry at most [`HAVE_MAX`] ids; a GET names only ids the node lacks; a replay sends
//! at most [`REPLAY_PUSH_MAX`] messages and never a member's own back to it.

use vinc_membership::{Nanos, NodeId};

use crate::consts::{
    AE_FROM, AE_TO, GAP_EVERY, GAP_LIVE, GAP_SPAN, HAVE_MAX, HUB_AE, REPLAY_PUSH_MAX, RESUB_BACK_MS, TABLE_MAX,
};
use crate::event::{Trace, topic_tag};
use crate::host::{Host, Lane};
use crate::node::{Refused, Topics};
use crate::wire::{self, Head, get_u64, ty};

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
    pub fn resubscribe<H: Host>(&mut self, h: &mut H, _now: Nanos, hub: &NodeId) {
        if !self.is_hub && self.primary == Some(*hub) {
            let since = self.since_ms();
            self.resub_all(h, hub, since);
        }
    }

    /// The primary hub changed: leave the old one and subscribe at the new one with gap repair.
    pub fn primary_changed<H: Host>(&mut self, h: &mut H, _now: Nanos, old: Option<&NodeId>, new: &NodeId) {
        self.primary = Some(*new);
        self.trace(|| Trace::Primary { hub: *new });
        if self.is_hub {
            return;
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
        let topics = core::mem::take(&mut self.topics);
        for (k, st) in &topics {
            let Some(log) = st.log.as_ref().filter(|l| l.len() > 0) else {
                continue;
            };
            let total = log.window(now, AE_FROM, AE_TO).count();
            self.ids.clear();
            for mid in log.window(now, AE_FROM, AE_TO).skip(total.saturating_sub(HAVE_MAX)) {
                self.ids.extend_from_slice(&mid.to_le_bytes());
            }
            if self.ids.is_empty() || wire::build(&mut self.scratch, ty::HAVE, k, &[&self.ids]).is_err() {
                continue;
            }
            let count = u16::try_from(self.ids.len() / 8).unwrap_or(u16::MAX);
            for hub in &self.hubs {
                if h.hub_up(hub) {
                    h.send(hub, Lane::Reply, &self.scratch);
                    self.tq.push(|| Trace::HaveSent {
                        peer: *hub,
                        topic: topic_tag(k),
                        count,
                    });
                }
            }
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
            let total = log.window(now, span, 0).count();
            self.ids.clear();
            for mid in log.window(now, span, 0).skip(total.saturating_sub(HAVE_MAX)) {
                self.ids.extend_from_slice(&mid.to_le_bytes());
            }
            if !self.ids.is_empty() && wire::build(&mut self.scratch, ty::HAVE, k, &[&self.ids]).is_ok() {
                h.send(member, Lane::Reply, &self.scratch);
            }
        }
        self.topics = topics;
    }

    /// A SUB at a hub: record the subscriber and answer with HAVE, or replay the messages when flag 1 is set.
    pub(crate) fn on_sub<H: Host>(&mut self, h: &mut H, _now: Nanos, from: &NodeId, topic: &[u8], rest: &[u8]) {
        let Some(since) = get_u64(rest).filter(|_| self.is_hub && *from != self.me) else {
            return;
        };
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
        if let Some(log) = st.log.as_ref() {
            let total = log.since(since).count();
            if replay {
                for mid in log.since(since).skip(total.saturating_sub(REPLAY_PUSH_MAX)) {
                    let Some(l) = log.get(mid) else { continue };
                    let Ok((head, _)) = Head::parse(l) else {
                        continue;
                    };
                    if head.origin != from
                        && wire::build(&mut self.scratch, ty::MSG, topic, &[l]).is_ok()
                        && h.send(from, Lane::Reply, &self.scratch)
                    {
                        self.sent.note(from, head.ts, head.origin);
                    }
                }
            } else {
                self.ids.clear();
                for mid in log.since(since).skip(total.saturating_sub(HAVE_MAX)) {
                    self.ids.extend_from_slice(&mid.to_le_bytes());
                }
                if !self.ids.is_empty() && wire::build(&mut self.scratch, ty::HAVE, topic, &[&self.ids]).is_ok() {
                    h.send(from, Lane::Reply, &self.scratch);
                    let count = u16::try_from(self.ids.len() / 8).unwrap_or(u16::MAX);
                    self.tq.push(|| Trace::HaveSent {
                        peer: *from,
                        topic: topic_tag(topic),
                        count,
                    });
                }
            }
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
                if st.requested.len() >= 2 * HAVE_MAX {
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

    /// A GET at a hub: send the messages behind the ids it still holds.
    pub(crate) fn on_get<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8], rest: &[u8]) {
        let Some(log) = self.topics.get(topic).and_then(|st| st.log.as_ref()) else {
            return;
        };
        for mid in rest.get(..8 * HAVE_MAX).unwrap_or(rest).as_chunks::<8>().0 {
            let Some(l) = log.get(u64::from_le_bytes(*mid)) else {
                continue;
            };
            let Ok((head, _)) = Head::parse(l) else {
                continue;
            };
            if wire::build(&mut self.scratch, ty::MSG, topic, &[l]).is_ok() && h.send(from, Lane::Reply, &self.scratch)
            {
                self.sent.note(from, head.ts, head.origin);
            }
        }
    }
}
