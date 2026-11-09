//! Frame dispatch: what a node does with each frame of the hub stream.
//!
//! Every frame first renews the sender (a hub's lease on a member, this node's hearing of a hub) and, from a hub,
//! samples the round trip. Then membership frames go to the roster or the view, and anything else goes to the
//! broadcast layer untouched.
//!
//! Invariants: a frame from a revoked peer is dropped unread; a frame a node has no use for (a HELLO to a member, a
//! DELTA from a non-hub) is ignored, never an error; at most [`MAX_FRAMES_PER_CALL`] frames are parsed per call.

use crate::codec::{Frame, FrameError, NodeId};
use crate::consts::{HYST_ABS, RENEW, RTT_SAMPLE_MAX};
use crate::event::{QuietCause, Trace};
use crate::node::Membership;
use crate::session::{Host, Nanos};

/// The most frames one [`Membership::on_bytes`] call parses.
pub const MAX_FRAMES_PER_CALL: usize = 512;

impl Membership {
    /// Refresh our hearing of each hub from the transport: any authenticated packet on the session shows the hub is
    /// alive, with no HELLO round trip.
    pub(crate) fn pulse_refresh<H: Host>(&mut self, h: &H, now: Nanos) {
        for i in 0..self.boot.len() {
            let Some(hub) = self.boot.get(i).copied() else {
                continue;
            };
            if hub == self.me || !self.up.contains_key(&hub) {
                continue;
            }
            let t = self.heard.get(&hub).copied();
            if t.is_none_or(|t| now.saturating_sub(t) >= RENEW)
                && let Some(ev) = h.evidence(&hub)
                && t.is_none_or(|t| ev.last_rx > t)
            {
                // The transport heard the hub again after a long silence: a partition healed.
                if !self.is_hub && t.is_some_and(|t| ev.last_rx.saturating_sub(t) > h.give_up(&hub)) {
                    self.begin_quiet(now, QuietCause::Heal);
                }
                self.heard.insert(hub, ev.last_rx);
            }
        }
    }

    /// Parse and handle the complete frames at the start of `buf`; returns how many bytes were used. The rest is a
    /// partial frame to keep until more bytes arrive.
    ///
    /// # Errors
    /// [`FrameError`] for a frame that does not parse. The host must reset the stream: the framing is lost.
    pub fn on_bytes<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId, buf: &[u8]) -> Result<usize, FrameError> {
        let mut used = 0;
        for _ in 0..MAX_FRAMES_PER_CALL {
            let Some(rest) = buf.get(used..) else { break };
            match Frame::read_with(rest, self.max_frame) {
                Ok(Some((f, n))) => {
                    self.on_frame(h, now, peer, &f);
                    used += n;
                }
                Ok(None) => break,
                Err(e) => {
                    self.trace(Trace::BadFrame { peer: *peer });
                    return Err(e);
                }
            }
        }
        Ok(used)
    }

    /// Handle one frame from `peer`.
    pub fn on_frame<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId, f: &Frame<'_>) {
        if self.revoked.contains(peer) || self.leaving {
            return;
        }
        self.trace(Trace::FrameIn {
            peer: *peer,
            ty: f.ty(),
        });
        self.pulse_refresh(h, now);
        let from_hub = self.is_boot(peer);
        if from_hub {
            let silent = self
                .heard
                .get(peer)
                .is_some_and(|t| now.saturating_sub(*t) > h.give_up(peer));
            if !self.is_hub && silent {
                self.begin_quiet(now, QuietCause::Heal);
            }
            self.heard.insert(*peer, now);
            if let Some(v) = self.hello_at.get_mut(peer) {
                *v = None;
            }
            if matches!(f, Frame::Ack | Frame::Snap(_))
                && let Some(t0) = self.hsent.get_mut(peer).and_then(Option::take)
                && now.saturating_sub(t0) < RTT_SAMPLE_MAX
            {
                self.rtt_sample(peer, now - t0);
                if !self.is_hub
                    && let Some(p) = self.primary
                    && p != *peer
                {
                    let cur = self.hrtt.get(&p).copied();
                    let new = self.hrtt.get(peer).copied().unwrap_or(u64::MAX);
                    if self.hub_up(now, peer) && cur.is_none_or(|c| new.saturating_add(HYST_ABS) < c * 3 / 4) {
                        self.reselect(h, now);
                    }
                }
            }
            if self.primary.is_none() {
                self.reselect(h, now);
            }
        }
        if self.is_hub
            && !matches!(f, Frame::Hello(_))
            && let Some(l) = self.roster.get_mut(peer)
        {
            l.renewed = now;
        }
        match f {
            Frame::Hello(hello) => {
                if self.is_hub {
                    self.on_hello(h, now, peer, hello);
                }
            }
            Frame::Probe => {
                if from_hub && !self.is_hub {
                    self.hello_to(h, now, peer, false);
                }
            }
            Frame::Down(d) => {
                if self.is_hub && from_hub {
                    self.on_down(h, now, d);
                } else if from_hub {
                    self.apply_down(h, now, peer, d.member, d.inc);
                }
            }
            Frame::Delta(e) => {
                if from_hub {
                    self.apply_delta(h, now, peer, e);
                }
            }
            Frame::Snap(s) => {
                if from_hub {
                    self.apply_snap(h, now, peer, s);
                }
            }
            Frame::Ack => {}
            Frame::Other(o) => h.frame(peer, o.ty, o.topic, o.rest),
        }
    }
}
