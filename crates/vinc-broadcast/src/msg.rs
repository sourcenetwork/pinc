//! A message arriving: verification, the hub log and push, local delivery, the access-control hold.
//!
//! Every message is checked before it is used: the head must parse, the origin must not be revoked, and the
//! signature must cover the topic, the id and the exact body. A hub acknowledges a PUB or FANP only for a message it
//! has stored (or already holds), so an acknowledged message is one the hub verified.
//!
//! Invariants: a message is delivered at most once per id within the dedupe window; a message from an origin the
//! access-control layer has not yet answered for is held (at most [`HELD_MAX`]) and delivered or dropped on the
//! answer; the steady path (verify, log, push, deliver) allocates nothing.

use alloc::vec::Vec;

use vinc_membership::{Nanos, NodeId};
use vinc_wire::hlc::Hlc;

use crate::auth;
use crate::consts::{ACP_CAP, CHECKS_MAX, HELD_MAX, SEEN_CAP, TABLE_MAX};
use crate::event::{HoldWhy, Reject, Trace, topic_tag};
use crate::host::{Event, Host, Lane};
use crate::log::HubLog;
use crate::node::{Held, Topics};
use crate::wire::{self, Head, ty};

impl Topics {
    fn is_dup(&self, topic: &[u8], key: u64, now: Nanos) -> bool {
        self.topics
            .get(topic)
            .is_some_and(|st| st.seen.contains(key, now) || st.log.as_ref().is_some_and(|l| l.contains(key)))
    }

    fn send_pack<H: Host>(&mut self, h: &mut H, to: &NodeId, mid: [u8; 8]) {
        if wire::build(&mut self.scratch, ty::PACK, &[], &[&mid]).is_ok() {
            h.send(to, Lane::Reply, &self.scratch);
        }
    }

    /// A PUB, FAN, FANP, MSG or `MEMBER_PUSH` frame from `from`.
    pub(crate) fn on_msg<H: Host>(&mut self, h: &mut H, now: Nanos, from: &NodeId, t: u8, topic: &[u8], rest: &[u8]) {
        let allowed = match t {
            ty::PUB | ty::FAN | ty::FANP => self.is_hub,
            ty::MSG => self.is_boot(from),
            _ => true,
        };
        if !allowed {
            return;
        }
        let Ok((head, body)) = Head::parse(rest) else {
            self.note_reject([0; 8], Reject::BadHead);
            return;
        };
        if body.len() > self.limits.max_body {
            self.note_reject(head.mid, Reject::BadHead);
            return;
        }
        let (mid, key) = (head.mid, u64::from_le_bytes(head.mid));
        let ack = self.is_hub && matches!(t, ty::PUB | ty::FANP);
        if self.is_dup(topic, key, now) {
            if ack {
                self.send_pack(h, from, mid);
            }
            self.note_reject(mid, Reject::Duplicate);
            return;
        }
        if self.revoked.contains(head.origin) {
            self.note_reject(mid, Reject::Revoked);
            return;
        }
        if !auth::verify(&head, topic, body) {
            self.note_reject(mid, Reject::BadSignature);
            return;
        }
        let wall = h.wall_ms();
        self.observe(head.ts, wall);
        // A message a peer pushed over a member session says nothing about what the hub logged meanwhile, so only the
        // hub path moves the point a re-subscription asks the log back from.
        if t != ty::MEMBER_PUSH {
            self.last_rx_wall = wall;
        }
        if let Some(st) = self.topics.get_mut(topic)
            && st.requested.remove(&mid)
        {
            h.event(Event::GapRepaired { topic, mid });
            self.trace(|| Trace::Repaired {
                topic: topic_tag(topic),
                mid,
            });
        }
        if self.is_hub {
            if matches!(t, ty::PUB | ty::FANP) && !self.is_boot(from) {
                self.note_publisher(h, from, topic);
            }
            let fanned = matches!(t, ty::FAN | ty::FANP);
            // The acknowledgement follows the store: a publisher that hears PACK stops retrying, so a message the
            // hub could not keep (no room for the topic) must not be acknowledged.
            if self.hub_store(h, now, Some(from), fanned, topic, &head, rest, body) && ack {
                self.send_pack(h, from, mid);
            }
        } else {
            self.offer(h, now, topic, mid, head.origin, from, body, head.ts);
        }
    }

    pub(crate) fn note_reject(&mut self, mid: [u8; 8], why: Reject) {
        self.trace(|| Trace::Rejected { mid, why });
    }

    /// Log a verified message, push it to the live subscribers and mirror it to the other hubs unless it was fanned.
    /// `rest` is the head and body as they arrived; `sender` is `None` for this hub's own publish. Returns whether the
    /// message is in the log.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn hub_store<H: Host>(
        &mut self,
        h: &mut H,
        now: Nanos,
        sender: Option<&NodeId>,
        fanned: bool,
        topic: &[u8],
        head: &Head<'_>,
        rest: &[u8],
        body: &[u8],
    ) -> bool {
        let key = u64::from_le_bytes(head.mid);
        let wall = h.wall_ms();
        if !self.ensure_topic(topic) {
            self.note_reject(head.mid, Reject::TopicsFull);
            return false;
        }
        let log_bytes = self.limits.log_bytes;
        let Some(st) = self.topics.get_mut(topic) else {
            return false;
        };
        let (log, seen) = (&mut st.log, &mut st.seen);
        let log = log.get_or_insert_with(|| HubLog::new(log_bytes));
        let head_bytes = rest.get(..head.len()).unwrap_or_default();
        let stored = log.push(key, now, wall, head_bytes, body, |old| {
            // Only an id the set lost needs a record: a second one at the same instant would leave the id forgotten
            // when the first is popped.
            if !seen.contains(old, now) {
                seen.insert(old, now, true);
            }
        });
        if !stored {
            self.note_reject(head.mid, Reject::LogFull);
            return false;
        }
        self.trace(|| Trace::Stored {
            topic: topic_tag(topic),
            mid: head.mid,
            fanned,
        });
        if wire::build(&mut self.scratch, ty::MSG, topic, &[rest]).is_ok() {
            // Subscribers whose stream has no room for this message: none in the usual case, so nothing is allocated.
            let mut fell: Vec<NodeId> = Vec::new();
            if let Some(st) = self.topics.get(topic) {
                for (p, live) in &st.subs {
                    // A subscriber that is behind gets this message from the log, after the ones before it.
                    if !*live || Some(p) == sender || p == head.origin || st.behind.contains_key(p) {
                        continue;
                    }
                    // A floor advances only for a message a session took: one nobody carried was never delivered.
                    if h.send(p, Lane::Reply, &self.scratch) {
                        self.sent.note(p, head.ts, head.origin);
                    } else if h.backlogged(p, self.scratch.len()) {
                        fell.push(*p);
                    }
                }
            }
            if !fell.is_empty() {
                self.fall_behind(topic, &fell);
            }
            if !fanned && sender.is_none_or(|s| !self.hubs.contains(s)) {
                for hub in &self.hubs {
                    if Some(hub) != sender {
                        h.send(hub, Lane::Main, &self.scratch);
                    }
                }
            }
        }
        let subscribed = self.topics.get(topic).is_some_and(|st| st.sub);
        if subscribed && *head.origin != self.me {
            let hop = sender.copied().unwrap_or(self.me);
            self.offer(h, now, topic, head.mid, head.origin, &hop, body, head.ts);
        } else if let Some(st) = self.topics.get_mut(topic) {
            st.seen.insert(key, now, true);
        }
        true
    }

    /// A verified message reaches this node: apply the replay floors, mark it seen, and deliver it if the node
    /// subscribes and the origin is allowed.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn offer<H: Host>(
        &mut self,
        h: &mut H,
        now: Nanos,
        topic: &[u8],
        mid: [u8; 8],
        origin: &NodeId,
        hop: &NodeId,
        body: &[u8],
        ts: Hlc,
    ) {
        let key = u64::from_le_bytes(mid);
        if !self.ensure_topic(topic) {
            self.note_reject(mid, Reject::TopicsFull);
            return;
        }
        let Some(st) = self.topics.get(topic) else {
            return;
        };
        if st.seen.len() >= SEEN_CAP {
            self.note_reject(mid, Reject::SeenFull);
            return;
        }
        let subscribed = st.sub;
        let old = self.is_old(origin, ts);
        if self.gather.gathering() && !self.is_hub {
            // Until every hub reported its floor, a message cannot be told from one an earlier life delivered.
            self.hold_for_floor(mid, origin, hop, ts, topic, body);
            return;
        }
        let verdict = self.acp.get(origin).copied().filter(|(_, exp)| *exp >= now);
        let holds = subscribed && !old && *origin != self.me && verdict.is_none();
        let already = self.held.iter().any(|e| e.mid == mid);
        if holds && !already && self.held.len() >= HELD_MAX {
            // No room to wait for the answer: ask, and leave the id unseen so the gap repair brings it again.
            self.ask_check(h, origin, topic);
            self.note_reject(mid, Reject::HeldFull);
            return;
        }
        if let Some(st) = self.topics.get_mut(topic) {
            st.seen.insert(key, now, false);
        }
        if !subscribed || old || *origin == self.me {
            if old {
                self.note_reject(mid, Reject::Old);
            }
            return;
        }
        if let Some((allow, _)) = verdict {
            if allow {
                self.deliver(h, topic, mid, origin, hop, body);
            }
            return;
        }
        // A copy that arrives after the dedupe set forgot the first, while the answer is still out, waits once.
        if !already {
            let mut data = self.take_buf();
            if Self::pack(&mut data, topic, body) {
                self.held.push(Held {
                    mid,
                    origin: *origin,
                    hop: *hop,
                    ts,
                    data,
                });
                self.trace(|| Trace::Held { mid, why: HoldWhy::Acp });
            } else {
                self.give_buf(data);
            }
        }
        self.ask_check(h, origin, topic);
    }

    /// Ask the access-control layer about `origin` unless a check for it is out.
    fn ask_check<H: Host>(&mut self, h: &mut H, origin: &NodeId, topic: &[u8]) {
        if !self.checks.iter().any(|(_, o)| o == origin) && self.checks.len() < CHECKS_MAX {
            let id = self.next_check;
            self.next_check = self.next_check.wrapping_add(1);
            self.checks.push((id, *origin));
            self.trace(|| Trace::AcpAsked { id });
            h.event(Event::AcpCheck { id, origin, topic });
        }
    }

    /// Offer a message that was held for the floors, unless it arrived by another path meanwhile.
    pub(crate) fn offer_held<H: Host>(&mut self, h: &mut H, now: Nanos, e: Held) {
        if let Some((topic, body)) = Self::unpack(&e.data)
            && !self.is_dup(topic, u64::from_le_bytes(e.mid), now)
        {
            self.offer(h, now, topic, e.mid, &e.origin, &e.hop, body, e.ts);
        }
        self.give_buf(e.data);
    }

    fn deliver<H: Host>(&mut self, h: &mut H, topic: &[u8], mid: [u8; 8], origin: &NodeId, hop: &NodeId, body: &[u8]) {
        h.event(Event::Message {
            topic,
            origin,
            hop,
            mid,
            body,
        });
        self.trace(|| Trace::Delivered {
            topic: topic_tag(topic),
            mid,
        });
    }

    /// The access-control layer answered check `id`: cache the verdict for [`ACP_CAP`] and deliver or drop what was
    /// held for the origin.
    pub fn acp_answer<H: Host>(&mut self, h: &mut H, now: Nanos, id: u32, allow: bool) {
        let Some(pos) = self.checks.iter().position(|(c, _)| *c == id) else {
            return;
        };
        let (_, origin) = self.checks.remove(pos);
        self.trace(|| Trace::AcpAnswered { id, allow });
        if self.acp.contains_key(&origin) || self.acp.len() < TABLE_MAX {
            self.acp.insert(origin, (allow, now.saturating_add(ACP_CAP)));
        }
        let mut i = 0;
        while let Some(e) = self.held.get(i) {
            if e.origin != origin {
                i += 1;
                continue;
            }
            let e = self.held.remove(i);
            if allow && let Some((topic, body)) = Self::unpack(&e.data) {
                self.deliver(h, topic, e.mid, &e.origin, &e.hop, body);
            }
            self.give_buf(e.data);
        }
    }
}
