//! Publishing: sign and hand a message to the hubs, retry until a hub acknowledges it, and reach the subscribers
//! directly when no hub can be reached.
//!
//! `HUB_FAN`: when every hub is up the publisher sends FANP to its primary and FAN to the others (on the second
//! stream), so each hub pushes to its own subscribers at once; otherwise it sends PUB to the primary, which mirrors
//! it. A hub acknowledges with PACK; without one the publisher retries on the next hub every [`PUB_RETRY`] and gives
//! up after [`PUB_GIVEUP`].
//!
//! A burst faster than the path to the hub fills the hub's stream. A publish the stream has no room for is not sent
//! and not dropped: it stays in the pending table marked unsent, the publishes after it wait behind it so the hub
//! gets them in order, and they go out when the host says the stream has room again ([`Topics::peer_writable`]).
//!
//! The fallback covers the case where publisher and subscriber are both cut off from every hub but can reach each
//! other: while no hub is reachable the publisher sends the message over a member session (`MEMBER_PUSH`) to the
//! subscribers of the topic that the membership view still lists, at most [`FALLBACK_BATCH`] per step, one step at
//! publish and one at each retry, and never twice to the same subscriber. Receivers dedupe by message id.
//!
//! Invariants: a publish is signed over the topic, id and body hash before any byte leaves; at most
//! [`PENDING_MAX`] publishes wait, and a publish past that is refused, so every accepted publish ends acknowledged or
//! given up; an unsent publish is sent before any publish accepted after it; the fallback sends to no node outside
//! the topic's subscriber set.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use pinc_crypto::IdentityAlg;
use pinc_crypto::identity::MAX_SIGNATURE_LEN;
use pinc_membership::{Nanos, NodeId};

use crate::auth;
use crate::consts::{FALLBACK_BATCH, MAX_TOPIC, PENDING_MAX, PUB_GIVEUP, PUB_RETRY, PUSH_STALL_MS};
use crate::event::{PublishMode, Trace, topic_tag};
use crate::host::{Event, Host, Lane};
use crate::node::{Pending, Refused, Topic, Topics};
use crate::wire::{self, Head, ty};

/// Send `head | body` of `mid` to subscribers of the topic that were not served yet; returns how many were sent
/// this step. Free over the fields it needs so a pending entry can be borrowed meanwhile.
#[allow(clippy::too_many_arguments)]
fn fallback_step<H: Host>(
    h: &mut H,
    scratch: &mut Vec<u8>,
    topics: &BTreeMap<Vec<u8>, Topic>,
    me: &NodeId,
    topic: &[u8],
    mid: [u8; 8],
    head: &[u8],
    body: &[u8],
    served: &mut Vec<NodeId>,
) -> usize {
    let Some(st) = topics.get(topic) else { return 0 };
    if wire::build(scratch, ty::MEMBER_PUSH, topic, &[head, body]).is_err() {
        return 0;
    }
    let mut sent = 0;
    for peer in st.peers.iter().chain(&st.hints) {
        if sent >= FALLBACK_BATCH {
            break;
        }
        if peer == me || served.contains(peer) || !h.in_view(peer) {
            continue;
        }
        if h.send_member(peer, scratch) {
            served.push(*peer);
            sent += 1;
            h.event(Event::Fallback { topic, mid, to: peer });
        }
    }
    sent
}

/// What became of a publish handed to its first hub.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Handed {
    /// The hub's session took the frame.
    Taken,
    /// The session did not take it and will not later: the retry covers it.
    Refused,
    /// The hub's stream has no room now; the host says when it has.
    NoRoom,
}

impl Topics {
    /// A publish the pending table cannot track would get no retry and no outcome, so it is refused before anything
    /// leaves. A hub stores its own publishes, and a node with no hub list tracks none.
    fn room_to_track(&self) -> Result<(), Refused> {
        if !self.is_hub && !self.hubs.is_empty() && self.pending.len() >= PENDING_MAX {
            return Err(Refused::Backlog);
        }
        Ok(())
    }

    /// Sign `body` and publish it to `topic`; returns the message id.
    ///
    /// # Errors
    /// [`Refused`] for a topic over 255 bytes, a body over the limit, a full topic table, [`PENDING_MAX`] publishes
    /// still waiting for a hub, or on a hub a log full of messages its subscribers are still owed ([`Refused::Backlog`]:
    /// publish again later), or a signing failure.
    pub fn publish<H: Host>(&mut self, h: &mut H, now: Nanos, topic: &[u8], body: &[u8]) -> Result<[u8; 8], Refused> {
        if topic.len() > MAX_TOPIC {
            return Err(Refused::TopicTooLong);
        }
        self.room_to_track()?;
        if body.len() > self.limits.max_body {
            return Err(Refused::BodyTooLarge {
                limit: self.limits.max_body,
            });
        }
        if !self.ensure_topic(topic) {
            return Err(Refused::TopicsFull);
        }
        self.seq += 1;
        let mid = auth::message_id(&self.me, self.inc, self.seq, topic);
        self.hlc = self.hlc.tick(h.wall_ms());
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let sl = auth::sign(&self.key, topic, &mid, body, self.hlc, true, &mut sig).ok_or(Refused::Sign)?;
        // `data` is `topic | head | body`; the head borrows this node's id and key only to be written out.
        let mut data = self.take_buf();
        data.clear();
        data.extend_from_slice(topic);
        let head = Head {
            mid,
            origin: &self.me,
            alg: self.alg,
            pk: if self.alg == IdentityAlg::Ed25519 {
                &[]
            } else {
                &self.pk
            },
            sig: sig.get(..sl).unwrap_or_default(),
            isb: true,
            ts: self.hlc,
        };
        let hlen = head.len();
        head.write(
            u32::try_from(body.len()).map_err(|_| Refused::BodyTooLarge {
                limit: self.limits.max_body,
            })?,
            &mut data,
        );
        data.extend_from_slice(body);
        let key = u64::from_le_bytes(mid);
        if let Some(st) = self.topics.get_mut(topic) {
            st.seen.insert(key, now, true);
        }
        let tlen = topic.len();
        if self.is_hub {
            self.trace(|| Trace::Published {
                topic: topic_tag(topic),
                mid,
                mode: PublishMode::Local,
            });
            let rest = data.get(tlen..).unwrap_or_default();
            // Not stored: the log can evict nothing for it, because subscribers that are behind are still owed the rest.
            let stored =
                Head::parse(rest).is_ok_and(|(hd, b)| self.hub_store(h, now, None, false, topic, &hd, rest, b));
            self.give_buf(data);
            if stored {
                return Ok(mid);
            }
            // A subscriber that stalls can be let go once it took nothing for the stall time: ask again just after.
            self.room_at = Some(now.saturating_add((PUSH_STALL_MS + 1) * 1_000_000));
            return Err(Refused::Backlog);
        }
        // Behind publishes that wait for room in the hub's stream this one waits too, so the hub gets them in order.
        let (mode, handed) = if self.unsent > 0 {
            (self.publish_mode(h), Handed::NoRoom)
        } else {
            self.send_publish(h, topic, &data, tlen, hlen)
        };
        self.trace(|| Trace::Published {
            topic: topic_tag(topic),
            mid,
            mode,
        });
        let served = self.first_fallback(h, topic, mid, &data, tlen, hlen);
        self.track(Pending {
            mid,
            data,
            tlen,
            hlen,
            t0: now,
            next_try: now.saturating_add(PUB_RETRY),
            idx: 0,
            served,
            unsent: handed == Handed::NoRoom,
        });
        Ok(mid)
    }

    /// While no hub is reachable, the first fallback step of a fresh publish; the subscribers it was sent to.
    fn first_fallback<H: Host>(
        &mut self,
        h: &mut H,
        topic: &[u8],
        mid: [u8; 8],
        data: &[u8],
        tlen: usize,
        hlen: usize,
    ) -> Vec<NodeId> {
        let mut served = Vec::new();
        if !self.any_hub_up(h) {
            let rest = data.get(tlen..).unwrap_or_default();
            let (head, body) = rest.split_at(hlen.min(rest.len()));
            fallback_step(
                h,
                &mut self.scratch,
                &self.topics,
                &self.me,
                topic,
                mid,
                head,
                body,
                &mut served,
            );
            self.trace_fallback(mid, &served);
        }
        served
    }

    /// Keep a publish until a hub acknowledges it. A node with no hub list tracks none.
    fn track(&mut self, p: Pending) {
        if self.pending.len() < PENDING_MAX && !self.hubs.is_empty() {
            self.unsent += usize::from(p.unsent);
            self.pending.push(p);
        } else {
            self.give_buf(p.data);
        }
    }

    /// The hub a fresh publish goes to first: the primary, or the first of the list.
    fn first_hub(&self) -> Option<NodeId> {
        self.primary
            .filter(|p| self.hubs.contains(p))
            .or_else(|| self.hubs.first().copied())
    }

    /// How a fresh publish is handed over now: to every hub at once when all are up, else to one.
    fn publish_mode<H: Host>(&self, h: &H) -> PublishMode {
        if self.first_hub().is_some() && self.hubs.iter().all(|x| h.hub_up(x)) {
            PublishMode::Fan
        } else {
            PublishMode::Single
        }
    }

    /// Hand a fresh publish to the hubs: FANP to the primary and FAN to the others when all are up, else PUB. Returns
    /// the mode and what became of the frame for the first hub. When its stream has no room nothing is sent to any
    /// hub: the publish waits and goes to all of them later.
    fn send_publish<H: Host>(
        &mut self,
        h: &mut H,
        topic: &[u8],
        data: &[u8],
        tlen: usize,
        hlen: usize,
    ) -> (PublishMode, Handed) {
        let rest = data.get(tlen..).unwrap_or_default();
        let (head, body) = rest.split_at(hlen.min(rest.len()));
        let mode = self.publish_mode(h);
        let Some(first) = self.first_hub() else {
            return (mode, Handed::Refused);
        };
        let kind = if mode == PublishMode::Fan { ty::FANP } else { ty::PUB };
        let handed = if wire::build(&mut self.scratch, kind, topic, &[head, body]).is_err() {
            Handed::Refused
        } else if h.send(&first, Lane::Main, &self.scratch) {
            Handed::Taken
        } else if h.backlogged(&first, self.scratch.len()) {
            Handed::NoRoom
        } else {
            Handed::Refused
        };
        if mode == PublishMode::Fan
            && handed != Handed::NoRoom
            && wire::build(&mut self.scratch, ty::FAN, topic, &[head, body]).is_ok()
        {
            for x in self.hubs.iter().filter(|x| **x != first) {
                h.send(x, Lane::Fan, &self.scratch);
            }
        }
        (mode, handed)
    }

    /// The stream of hub `peer` has room again: hand over the publishes that waited for it, oldest first, until it is
    /// full again. Each starts its retry time when it is sent.
    pub(crate) fn send_unsent<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId) {
        if self.unsent == 0 || !self.hubs.contains(peer) {
            return;
        }
        let mut i = 0;
        while self.unsent > 0 {
            let Some(p) = self.pending.get_mut(i) else { break };
            if !p.unsent {
                i += 1;
                continue;
            }
            let (data, tlen, hlen) = (core::mem::take(&mut p.data), p.tlen, p.hlen);
            let (_, handed) = self.send_publish(h, data.get(..tlen).unwrap_or_default(), &data, tlen, hlen);
            let Some(p) = self.pending.get_mut(i) else { break };
            p.data = data;
            // Still no room, or the session is gone: the retry finds it another hub.
            if handed != Handed::Taken {
                break;
            }
            p.unsent = false;
            p.next_try = now.saturating_add(PUB_RETRY);
            self.unsent -= 1;
            i += 1;
        }
    }

    fn trace_fallback(&mut self, mid: [u8; 8], served: &[NodeId]) {
        for to in served {
            self.tq.push(|| Trace::FallbackSent { mid, to: *to });
        }
    }

    /// Retry the publishes no hub acknowledged on the next hub, give up on the old ones, and step the fallback while
    /// no hub is reachable.
    pub(crate) fn pub_retry<H: Host>(&mut self, h: &mut H, now: Nanos) {
        let no_hub = !self.any_hub_up(h);
        let mut i = 0;
        while let Some(p) = self.pending.get(i) {
            if now.saturating_sub(p.t0) > PUB_GIVEUP || self.hubs.is_empty() {
                let p = self.take_pending(i);
                let mid = p.mid;
                self.give_buf(p.data);
                h.event(Event::PublishGaveUp { mid });
                self.trace(|| Trace::PubGaveUp { mid });
                continue;
            }
            if now >= p.next_try {
                let n = self.hubs.len();
                let Some(p) = self.pending.get_mut(i) else { break };
                p.idx += 1;
                p.next_try = now.saturating_add(PUB_RETRY);
                let hub = self.hubs.get(p.idx % n).copied();
                let topic = p.data.get(..p.tlen).unwrap_or_default();
                let rest = p.data.get(p.tlen..).unwrap_or_default();
                let (head, body) = rest.split_at(p.hlen.min(rest.len()));
                if let Some(hub) = hub
                    && wire::build(&mut self.scratch, ty::PUB, topic, &[head, body]).is_ok()
                {
                    // A publish that never left for want of room leaves here if this hub's stream takes it.
                    if h.send(&hub, Lane::Main, &self.scratch) && p.unsent {
                        p.unsent = false;
                        self.unsent -= 1;
                    }
                    let mid = p.mid;
                    self.tq.push(|| Trace::PubRetry { hub, mid });
                }
                if no_hub {
                    let from = p.served.len();
                    let mid = p.mid;
                    fallback_step(
                        h,
                        &mut self.scratch,
                        &self.topics,
                        &self.me,
                        topic,
                        mid,
                        head,
                        body,
                        &mut p.served,
                    );
                    for to in p.served.iter().skip(from) {
                        self.tq.push(|| Trace::FallbackSent { mid, to: *to });
                    }
                }
            }
            i += 1;
        }
    }

    /// The earliest instant a pending publish needs attention.
    pub(crate) fn pending_deadline(&self) -> Option<Nanos> {
        self.pending
            .iter()
            .map(|p| p.next_try.min(p.t0.saturating_add(PUB_GIVEUP).saturating_add(1)))
            .min()
    }
}
