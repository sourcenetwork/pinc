//! Publishing: sign and hand a message to the hubs, retry until a hub acknowledges it, and reach the subscribers
//! directly when no hub can be reached.
//!
//! `HUB_FAN`: when every hub is up the publisher sends FANP to its primary and FAN to the others (on the second
//! stream), so each hub pushes to its own subscribers at once; otherwise it sends PUB to the primary, which mirrors
//! it. A hub acknowledges with PACK; without one the publisher retries on the next hub every [`PUB_RETRY`] and gives
//! up after [`PUB_GIVEUP`].
//!
//! The fallback covers the case where publisher and subscriber are both cut off from every hub but can reach each
//! other: while no hub is reachable the publisher sends the message over a member session (`MEMBER_PUSH`) to the
//! subscribers of the topic that the membership view still lists, at most [`FALLBACK_BATCH`] per step, one step at
//! publish and one at each retry, and never twice to the same subscriber. Receivers dedupe by message id.
//!
//! Invariants: a publish is signed over the topic, id and body hash before any byte leaves; at most
//! [`PENDING_MAX`] publishes wait; the fallback sends to no node outside the topic's subscriber set.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use vinc_crypto::IdentityAlg;
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_membership::{Nanos, NodeId};

use crate::auth;
use crate::consts::{FALLBACK_BATCH, MAX_BODY, MAX_TOPIC, PENDING_MAX, PUB_GIVEUP, PUB_RETRY};
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
    for peer in &st.peers {
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

impl Topics {
    /// Sign `body` and publish it to `topic`; returns the message id.
    ///
    /// # Errors
    /// [`Refused`] for a topic over 255 bytes, a body over the limit, a full topic table or a signing failure.
    pub fn publish<H: Host>(&mut self, h: &mut H, now: Nanos, topic: &[u8], body: &[u8]) -> Result<[u8; 8], Refused> {
        if topic.len() > MAX_TOPIC {
            return Err(Refused::TopicTooLong);
        }
        if body.len() > MAX_BODY {
            return Err(Refused::BodyTooLarge);
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
        head.write(u32::try_from(body.len()).map_err(|_| Refused::BodyTooLarge)?, &mut data);
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
            if let Some(rest) = data.get(tlen..)
                && let Ok((head, body)) = Head::parse(rest)
            {
                self.hub_store(h, now, None, false, topic, &head, rest, body);
            }
            self.give_buf(data);
            return Ok(mid);
        }
        let mode = self.send_publish(h, topic, &data, tlen, hlen);
        self.trace(|| Trace::Published {
            topic: topic_tag(topic),
            mid,
            mode,
        });
        let mut served = Vec::new();
        if !self.any_hub_up(h) {
            let (head, body) = data
                .get(tlen..)
                .unwrap_or_default()
                .split_at(hlen.min(data.len() - tlen));
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
            self.trace_fallback(topic, mid, &served, 0);
        }
        if self.pending.len() < PENDING_MAX && !self.hubs.is_empty() {
            self.pending.push(Pending {
                mid,
                data,
                tlen,
                hlen,
                t0: now,
                next_try: now.saturating_add(PUB_RETRY),
                idx: 0,
                served,
            });
        } else {
            self.give_buf(data);
        }
        Ok(mid)
    }

    /// Hand a fresh publish to the hubs: FANP to the primary and FAN to the others when all are up, else PUB.
    fn send_publish<H: Host>(&mut self, h: &mut H, topic: &[u8], data: &[u8], tlen: usize, hlen: usize) -> PublishMode {
        let rest = data.get(tlen..).unwrap_or_default();
        let (head, body) = rest.split_at(hlen.min(rest.len()));
        let Some(first) = self
            .primary
            .filter(|p| self.hubs.contains(p))
            .or_else(|| self.hubs.first().copied())
        else {
            return PublishMode::Single;
        };
        if self.hubs.iter().all(|x| h.hub_up(x)) {
            if wire::build(&mut self.scratch, ty::FANP, topic, &[head, body]).is_ok() {
                h.send(&first, Lane::Main, &self.scratch);
            }
            if wire::build(&mut self.scratch, ty::FAN, topic, &[head, body]).is_ok() {
                for x in self.hubs.iter().filter(|x| **x != first) {
                    h.send(x, Lane::Fan, &self.scratch);
                }
            }
            PublishMode::Fan
        } else {
            if wire::build(&mut self.scratch, ty::PUB, topic, &[head, body]).is_ok() {
                h.send(&first, Lane::Main, &self.scratch);
            }
            PublishMode::Single
        }
    }

    fn trace_fallback(&mut self, _topic: &[u8], mid: [u8; 8], served: &[NodeId], from: usize) {
        for to in served.iter().skip(from) {
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
                let p = self.pending.remove(i);
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
                    h.send(&hub, Lane::Main, &self.scratch);
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
