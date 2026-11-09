//! A message arriving: verification, the hub log and push, local delivery, the access-control hold.
//!
//! Every message is checked before it is used: the head must parse, the origin must not be revoked, and the
//! signature must cover the topic, the id and the exact body. A hub acknowledges a PUB or FANP only for a message it
//! has stored (or already holds), so an acknowledged message is one the hub verified.
//!
//! Invariants: a message is delivered at most once per id within the dedupe window; a message from an origin the
//! access-control layer has not yet answered for is held (at most [`HELD_MAX`]) and delivered or dropped on the
//! answer; the steady path (verify, log, push, deliver) allocates nothing.

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
            h.send(to, Lane::Main, &self.scratch);
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
        if ack {
            self.send_pack(h, from, mid);
        }
        let wall = h.wall_ms();
        self.observe(head.ts, wall);
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
            self.hub_store(h, now, Some(from), fanned, topic, &head, rest, body);
        } else {
            self.offer(h, now, topic, mid, head.origin, body, head.ts);
        }
    }

    pub(crate) fn note_reject(&mut self, mid: [u8; 8], why: Reject) {
        self.trace(|| Trace::Rejected { mid, why });
    }

    /// Log a verified message, push it to the live subscribers and mirror it to the other hubs unless it was fanned.
    /// `rest` is the head and body as they arrived; `sender` is `None` for this hub's own publish.
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
    ) {
        let key = u64::from_le_bytes(head.mid);
        let wall = h.wall_ms();
        if !self.ensure_topic(topic) {
            self.note_reject(head.mid, Reject::TopicsFull);
            return;
        }
        let Some(st) = self.topics.get_mut(topic) else {
            return;
        };
        let (log, seen) = (&mut st.log, &mut st.seen);
        let log = log.get_or_insert_with(HubLog::new);
        let head_bytes = rest.get(..head.len()).unwrap_or_default();
        let stored = log.push(key, now, wall, head_bytes, body, |old| {
            seen.insert(old, now, true);
        });
        if !stored {
            self.note_reject(head.mid, Reject::LogFull);
            return;
        }
        self.trace(|| Trace::Stored {
            topic: topic_tag(topic),
            mid: head.mid,
            fanned,
        });
        if wire::build(&mut self.scratch, ty::MSG, topic, &[rest]).is_ok() {
            if let Some(st) = self.topics.get(topic) {
                for (p, live) in &st.subs {
                    // A floor advances only for a message a session took: one nobody carried was never delivered.
                    if *live && Some(p) != sender && p != head.origin && h.send(p, Lane::Main, &self.scratch) {
                        self.sent.note(p, head.ts, head.origin);
                    }
                }
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
            self.offer(h, now, topic, head.mid, head.origin, body, head.ts);
        } else if let Some(st) = self.topics.get_mut(topic) {
            st.seen.insert(key, now, true);
        }
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
            self.hold_for_floor(mid, origin, ts, topic, body);
            return;
        }
        if let Some(st) = self.topics.get_mut(topic) {
            st.seen.insert(key, now, false);
        }
        self.last_rx_wall = h.wall_ms();
        if !subscribed || old || *origin == self.me {
            if old {
                self.note_reject(mid, Reject::Old);
            }
            return;
        }
        match self.acp.get(origin).copied() {
            Some((allow, exp)) if exp >= now => {
                if allow {
                    self.deliver(h, topic, mid, origin, body);
                }
                return;
            }
            _ => {}
        }
        if self.held.len() < HELD_MAX {
            let mut data = self.take_buf();
            if Self::pack(&mut data, topic, body) {
                self.held.push(Held {
                    mid,
                    origin: *origin,
                    ts,
                    data,
                });
                self.trace(|| Trace::Held { mid, why: HoldWhy::Acp });
            } else {
                self.give_buf(data);
            }
        }
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
            self.offer(h, now, topic, e.mid, &e.origin, body, e.ts);
        }
        self.give_buf(e.data);
    }

    fn deliver<H: Host>(&mut self, h: &mut H, topic: &[u8], mid: [u8; 8], origin: &NodeId, body: &[u8]) {
        h.event(Event::Message {
            topic,
            origin,
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
                self.deliver(h, topic, e.mid, &e.origin, body);
            }
            self.give_buf(e.data);
        }
    }
}
