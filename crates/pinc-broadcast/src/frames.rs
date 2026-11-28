//! Frame dispatch: what the machine does with each frame the host hands it.
//!
//! The host calls [`Topics::frame`] for every frame of a type membership does not own (the hub stream) and for every
//! frame arriving on a member session. A frame from a revoked peer is dropped unread, and a frame a node has no use
//! for (a SUB at a member, a FLOOR from a non-hub) is ignored, never an error.

use pinc_membership::{Nanos, NodeId};

use crate::event::Trace;
use crate::host::{Event, Host};
use crate::node::Topics;
use crate::wire::{MID_LEN, ty};

impl Topics {
    /// Handle one frame of type `t` with `topic` and `rest` from `from`.
    pub fn frame<H: Host>(&mut self, h: &mut H, now: Nanos, from: &NodeId, t: u8, topic: &[u8], rest: &[u8]) {
        if self.revoked.contains(from) {
            return;
        }
        match t {
            ty::FLOOR => self.on_floor(h, now, from, topic, rest),
            ty::PUB | ty::MSG | ty::FAN | ty::FANP | ty::MEMBER_PUSH => self.on_msg(h, now, from, t, topic, rest),
            ty::PACK => self.on_pack(h, from, rest),
            ty::SUB => self.on_sub(h, now, from, topic, rest),
            ty::UNSUB => self.on_unsub(h, from, topic),
            ty::HAVE => self.on_have(h, now, from, topic, rest),
            ty::GET => self.on_get(h, from, topic, rest),
            ty::PFULL => self.on_pfull(h, from, topic, rest),
            ty::SUBS => self.on_subs(h, now, from, topic, rest),
            ty::RESTORED => self.on_restored(h, from, topic),
            ty::ADJ => self.on_adj(h, now, from, rest),
            _ => {}
        }
    }

    /// A hub could not store a publish for a full topic table. Taken only from a hub, for a pending publish of this
    /// topic and id. The publish is not sent again to that hub, and ends refused once every hub refused it.
    fn on_pfull<H: Host>(&mut self, h: &mut H, from: &NodeId, topic: &[u8], rest: &[u8]) {
        let Some(mid) = rest.first_chunk::<MID_LEN>().copied() else {
            return;
        };
        let Some(bit) = self.hubs.iter().position(|x| x == from) else {
            return;
        };
        let Some(pos) = self
            .pending
            .iter()
            .position(|p| p.mid == mid && p.data.get(..p.tlen) == Some(topic))
        else {
            return;
        };
        let Some(p) = self.pending.get_mut(pos) else {
            return;
        };
        p.refused |= 1 << bit;
        if p.refused.count_ones() as usize >= self.hubs.len() {
            let p = self.take_pending(pos);
            self.give_buf(p.data);
            self.rejects.note_pub_refused_seen();
            h.event(Event::PublishFull { hub: from, topic, mid });
            self.trace(|| Trace::PubRefused { hub: *from, mid });
        }
    }

    /// A hub acknowledged a publish: stop retrying it. `pending` holds only this node's own publishes, and a hub
    /// acknowledges an id only for the message it stored under it, told by the print of its signature, so
    /// an acknowledgement of a pending id is final for this node's own message. If another origin took the id first the
    /// hub sends none, and the publish ends in the give-up like one no hub acknowledged.
    fn on_pack<H: Host>(&mut self, h: &mut H, from: &NodeId, rest: &[u8]) {
        let Some(mid) = rest.first_chunk::<MID_LEN>().copied() else {
            return;
        };
        if !self.is_boot(from) {
            return;
        }
        // vertexia: a linear scan of at most PENDING_MAX entries; an index by id if the bound is raised.
        if let Some(pos) = self.pending.iter().position(|p| p.mid == mid) {
            let p = self.take_pending(pos);
            self.give_buf(p.data);
            h.event(Event::PublishAcked { mid });
            self.trace(|| Trace::PubAcked { mid });
        }
    }
}
