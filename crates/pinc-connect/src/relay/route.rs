//! Forwarding: how a packet from one node finds the destination node (SEND to RECV, the hub tunnel, the mailbox and
//! `RELAY_FORWARD`).
//!
//! The rules, in order, for a packet from `src` to `dst`:
//! 1. `dst` is this relay: the packet is for the relay's own endpoint ([`super::Effect::Local`]).
//! 2. `dst` holds a carrier here: RECV on its carrier, in alias form after first use. If that carrier has been
//!    silent for [`super::rule::TUNNEL_STALE_NS`] the packet is also tunnelled down the member's UDP session (the
//!    receiver drops the duplicate).
//! 3. `dst` has a UDP session heard within [`super::rule::HUB_TUNNEL_FRESH_NS`], the host can send on its validated
//!    direct route now ([`super::Sink::tunnel_ready`]) and the packet fits a datagram: SPL. Otherwise the packet goes on
//!    to the next rule, as for a member with no UDP session.
//! 4. `dst` is asleep (its sleep notice is held and it has no carrier): the packet goes into the mailbox and the host
//!    is asked to wake the member.
//! 5. Otherwise, unless the packet itself came from a peer relay (no loops): the home relay is the one that
//!    forwarded `dst`'s packets to us within [`super::rule::FWD_BACK_NS`] (`FWD_BACK`), else the home in `dst`'s record;
//!    the packet goes there over the authenticated session. A home that is this relay, or has no authenticated
//!    session, is a refusal.

use pinc_crypto::NodeId;

use super::datagram::{Datagram, MAX_TUNNEL_DATAGRAM};
use super::{Effect, Reject, Relay, Route, Sink, Trace, rule};
use crate::carrier::frame::Frame;

/// A packet on its way: who from, who to, the flag byte and the opaque bytes.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Pkt<'a> {
    pub(crate) src: &'a NodeId,
    pub(crate) dst: &'a NodeId,
    pub(crate) flag: u8,
    pub(crate) packet: &'a [u8],
}

/// Where a packet entered the relay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Origin {
    /// From a member's carrier.
    Client,
    /// Forwarded by a peer relay.
    Peer,
    /// From a member's UDP session.
    Tunnel,
}

impl<const C: usize, const R: usize, const MN: usize, const MB: usize> Relay<C, R, MN, MB> {
    fn routed<S: Sink>(&mut self, src: &NodeId, dst: &NodeId, route: Route, bytes: usize, sink: &mut S) {
        match route {
            Route::Local => self.stats.local += 1,
            Route::Carrier => self.stats.carrier += 1,
            Route::Tunnel => self.stats.tunnel += 1,
            Route::Peer => self.stats.peer += 1,
            Route::Mailbox => self.stats.mailboxed += 1,
        }
        sink.emit(Effect::Trace(Trace::Routed {
            src: *src,
            dst: *dst,
            route,
            bytes,
        }));
    }

    /// Route one packet by the rules in the module documentation.
    pub(crate) fn route<S: Sink>(
        &mut self,
        now: u64,
        pkt: &Pkt<'_>,
        origin: Origin,
        sink: &mut S,
    ) -> Result<(), Reject> {
        let Pkt { src, dst, flag, packet } = *pkt;
        if *dst == self.cfg.me {
            self.local(src, packet, sink);
            return Ok(());
        }
        if self.deliver_client(now, pkt, true, sink) {
            return Ok(());
        }
        if self.tunnel_down(now, dst, src, flag, packet, sink) {
            return Ok(());
        }
        if self.mark_live(now, dst) {
            return self.hold(now, dst, src, flag, packet, sink);
        }
        if origin == Origin::Peer {
            return Err(self.reject(sink, Reject::NoRoute, Some(*src)));
        }
        self.forward(now, src, dst, flag, packet, sink)
    }

    /// RECV on `dst`'s carrier. Returns false if `dst` has none.
    pub(crate) fn deliver_client<S: Sink>(&mut self, now: u64, pkt: &Pkt<'_>, stale_copy: bool, sink: &mut S) -> bool {
        let Pkt { src, dst, flag, packet } = *pkt;
        let Some(c) = self.clients.get_mut(dst) else {
            return false;
        };
        let stale = now.saturating_sub(c.last_rx) > rule::TUNNEL_STALE_NS;
        let frame = c.tx.recv_frame(src, flag, packet);
        sink.emit(Effect::Carrier { to: *dst, frame });
        self.routed(src, dst, Route::Carrier, packet.len(), sink);
        if stale_copy && stale {
            self.tunnel_down(now, dst, src, flag, packet, sink);
        }
        true
    }

    /// Whether `node` has a UDP session heard within [`rule::HUB_TUNNEL_FRESH_NS`].
    fn fresh(&self, now: u64, node: &NodeId) -> bool {
        self.udp
            .get(node)
            .is_some_and(|heard| now.saturating_sub(*heard) < rule::HUB_TUNNEL_FRESH_NS)
    }

    /// SPL down `dst`'s UDP session if it is fresh and the packet fits.
    pub(crate) fn tunnel_down<S: Sink>(
        &mut self,
        now: u64,
        dst: &NodeId,
        src: &NodeId,
        flag: u8,
        packet: &[u8],
        sink: &mut S,
    ) -> bool {
        if !self.fresh(now, dst)
            || !sink.tunnel_ready(dst)
            || packet.is_empty()
            || 35 + packet.len() > MAX_TUNNEL_DATAGRAM
        {
            return false;
        }
        sink.emit(Effect::Udp {
            to: super::UdpTarget::Member(*dst),
            datagram: Datagram::Spl {
                src: *src,
                flag,
                packet,
            },
        });
        self.routed(src, dst, Route::Tunnel, packet.len(), sink);
        true
    }

    fn hold<S: Sink>(
        &mut self,
        now: u64,
        dst: &NodeId,
        src: &NodeId,
        flag: u8,
        packet: &[u8],
        sink: &mut S,
    ) -> Result<(), Reject> {
        use crate::mailbox::Push;
        match self.mailbox.push(now, dst, src, flag, packet) {
            Push::Stored { seq, dropped, first } => {
                self.routed(src, dst, Route::Mailbox, packet.len(), sink);
                sink.emit(Effect::Trace(Trace::MailboxStored {
                    node: *dst,
                    seq,
                    dropped,
                }));
                let rearm = self
                    .sleeping
                    .get_mut(dst)
                    .is_some_and(|s| first || now.saturating_sub(s.woke) >= rule::WAKE_REARM_NS);
                if rearm {
                    if let Some(s) = self.sleeping.get_mut(dst) {
                        s.woke = now;
                    }
                    sink.emit(Effect::Trace(Trace::WakeRequested { node: *dst }));
                    sink.emit(Effect::Wake { node: *dst });
                }
                Ok(())
            }
            Push::TooLarge | Push::NoSlot => Err(self.reject(sink, Reject::MailboxRefused, Some(*src))),
        }
    }

    /// `RELAY_FORWARD`: one hop to the home relay of `dst`.
    fn forward<S: Sink>(
        &mut self,
        now: u64,
        src: &NodeId,
        dst: &NodeId,
        flag: u8,
        packet: &[u8],
        sink: &mut S,
    ) -> Result<(), Reject> {
        let back = self
            .fwd_back
            .get(dst)
            .filter(|fb| now.saturating_sub(fb.at) < rule::FWD_BACK_NS && fb.relay != self.cfg.me)
            .map(|fb| fb.relay);
        let home = back.or_else(|| self.records.get(dst).map(|s| s.home));
        let Some(home) = home.filter(|h| *h != self.cfg.me) else {
            return Err(self.reject(sink, Reject::NoRoute, Some(*src)));
        };
        if !self.is_peer(&home) {
            return Err(self.reject(sink, Reject::NoPeerSession, Some(*src)));
        }
        sink.emit(Effect::PeerRelay {
            to: home,
            frame: Frame::Forward {
                src: *src,
                dst: *dst,
                flag,
                packet,
            },
        });
        self.routed(src, dst, Route::Peer, packet.len(), sink);
        Ok(())
    }

    /// Hand over what `node` holds if its route is ready (a fresh UDP session the host can send on): silent and
    /// one comparison when the mailbox holds nothing, and silent when the route is not ready.
    pub(super) fn release_held<S: Sink>(&mut self, now: u64, node: &NodeId, sink: &mut S) {
        if self.mailbox.members() == 0 || self.mailbox.pending(node).0 == 0 {
            return;
        }
        if self.fresh(now, node) && sink.tunnel_ready(node) {
            self.deliver_held(now, node, sink);
        }
    }

    /// Hand the mailbox contents of `node` to it, oldest first, in one [`Mailbox::drain`](crate::mailbox::Mailbox::drain):
    /// on its carrier if one is open, else down its fresh UDP session. A message leaves the mailbox only when it was
    /// handed over (or expires). Over a UDP session a message too long for a datagram is stepped over: it stays held,
    /// in its place, for the carrier, and the shorter ones behind it still go. A hand-over the host refuses stops the
    /// pass: that message and those behind it stay held, and the stop is counted once as [`Reject::NoTunnel`]; a
    /// message that does not fit is not a refusal and is not counted. Each held byte is read once and moved at most
    /// once in a pass, in place; the pass holds one packet buffer on the stack.
    pub(crate) fn deliver_held<S: Sink>(&mut self, now: u64, node: &NodeId, sink: &mut S) {
        use crate::mailbox::{Delivered, Mailbox, Offer};
        if self.mailbox.pending(node).0 == 0 {
            return;
        }
        let open = self.clients.contains(node);
        if !open && !self.fresh(now, node) {
            return;
        }
        let mut buf = [0u8; crate::carrier::frame::MAX_PACKET_LEN];
        let fit = if open {
            crate::carrier::frame::MAX_PACKET_LEN
        } else {
            MAX_TUNNEL_DATAGRAM - 35
        };
        Mailbox::drain(
            self,
            |r| &mut r.mailbox,
            now,
            node,
            fit,
            &mut buf,
            |r, m: &Delivered, body| {
                let sent = if open {
                    r.deliver_client(
                        now,
                        &Pkt {
                            src: &m.src,
                            dst: node,
                            flag: m.flag,
                            packet: body,
                        },
                        false,
                        sink,
                    )
                } else {
                    r.tunnel_down(now, node, &m.src, m.flag, body, sink)
                };
                if !sent {
                    r.reject(sink, Reject::NoTunnel, Some(*node));
                    return Offer {
                        taken: false,
                        go_on: false,
                    };
                }
                sink.emit(Effect::Trace(Trace::MailboxDelivered {
                    node: *node,
                    seq: m.seq,
                }));
                Offer {
                    taken: true,
                    go_on: true,
                }
            },
        );
    }

    /// A member came back without reopening its carrier (its UDP session woke): the sleep mark is cleared and the
    /// mailbox is delivered down the UDP session if it is fresh and its route is ready. Otherwise the mail stays held:
    /// a fresh route the host refuses is counted once as [`Reject::NoTunnel`]; a stale session, or a message too long
    /// for the route, is not a refusal. The next packet heard from the member hands it over when the route is ready
    /// ([`Relay::udp_heard`]).
    pub fn member_returned<S: Sink>(&mut self, now: u64, node: &NodeId, sink: &mut S) {
        if self.sleeping.remove(node).is_some() {
            sink.emit(Effect::Trace(Trace::SleepEnded { node: *node }));
        }
        self.deliver_held(now, node, sink);
    }

    /// Record that `node` was heard on its validated UDP session at `now`; false if the table has no room for it.
    pub(super) fn stamp(&mut self, now: u64, node: &NodeId) -> bool {
        self.udp.insert(*node, now).is_ok()
    }

    /// The host heard `node` on its validated UDP session at `now`: tunnel packets may use it for
    /// [`rule::HUB_TUNNEL_FRESH_NS`], and what the mailbox holds for `node` is handed over if its route is ready.
    /// A host calls it once after the endpoint read each packet from the member's validated direct route (the relay
    /// itself stamps and releases for each datagram from a validated member it is given), and applies the effects it
    /// emits. A release stops at a refused hand-over and counts it once as [`Reject::NoTunnel`]; a route that is not
    /// ready is silent. With no member holding mail it costs the stamp and one comparison.
    ///
    /// # Errors
    /// [`Reject::SessionsFull`] if the table has no room for a new member; it is traced and counted once.
    pub fn udp_heard<S: Sink>(&mut self, now: u64, node: &NodeId, sink: &mut S) -> Result<(), Reject> {
        if !self.stamp(now, node) {
            return Err(self.reject(sink, Reject::SessionsFull, Some(*node)));
        }
        self.release_held(now, node, sink);
        Ok(())
    }

    /// Forget the UDP session of `node`.
    pub fn udp_gone(&mut self, node: &NodeId) {
        self.udp.remove(node);
    }

    /// The relay's own endpoint sends `packet` to `dst` through the relay's routes (a SELFR frame to a member whose
    /// carrier is open, otherwise the usual rules with the relay as the source).
    ///
    /// # Errors
    /// [`Reject::NoRoute`] and the other routing refusals.
    pub fn send_local<S: Sink>(
        &mut self,
        now: u64,
        dst: &NodeId,
        flag: u8,
        packet: &[u8],
        sink: &mut S,
    ) -> Result<(), Reject> {
        if self.clients.contains(dst) {
            sink.emit(Effect::Carrier {
                to: *dst,
                frame: Frame::SelfRecv { packet },
            });
            let me = self.cfg.me;
            self.routed(&me, dst, Route::Carrier, packet.len(), sink);
            return Ok(());
        }
        let me = self.cfg.me;
        self.route(
            now,
            &Pkt {
                src: &me,
                dst,
                flag,
                packet,
            },
            Origin::Client,
            sink,
        )
    }
}
