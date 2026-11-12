//! Frame dispatch: what the machine does with each frame the host hands it.
//!
//! The host calls [`Topics::frame`] for every frame of a type membership does not own (the hub stream) and for every
//! frame arriving on a member session. A frame from a revoked peer is dropped unread, and a frame a node has no use
//! for (a SUB at a member, a FLOOR from a non-hub) is ignored, never an error.

use vinc_membership::{Nanos, NodeId};

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
            ty::FLOOR => self.on_floor(h, now, from, rest),
            ty::PUB | ty::MSG | ty::FAN | ty::FANP | ty::MEMBER_PUSH => self.on_msg(h, now, from, t, topic, rest),
            ty::PACK => self.on_pack(h, from, rest),
            ty::SUB => self.on_sub(h, now, from, topic, rest),
            ty::UNSUB => self.on_unsub(h, from, topic),
            ty::HAVE => self.on_have(h, now, from, topic, rest),
            ty::GET => self.on_get(h, from, topic, rest),
            ty::SUBS => self.on_subs(h, from, topic, rest),
            ty::RESTORED => self.on_restored(h, from, topic),
            _ => {}
        }
    }

    /// A hub acknowledged a publish: stop retrying it.
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
