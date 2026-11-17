//! The UDP side of the relay: address discovery (QAD), lookup over UDP, sleep notices and hub tunnel uploads.
//!
//! - **QAD:** a query's nonce is answered with the address the query came from, so a node learns its reflexive
//!   address and measures the round trip to pick its home relay.
//! - **Lookup:** DNSQ is answered from the record store; a record too large for a datagram is answered "too large"
//!   and the node asks again over its carrier.
//! - **Sleep notice (TETHER):** a signed notice from a node that holds, or just lost, a carrier here marks its next
//!   carrier close as a suspension. It is accepted from UDP or from the node's own carrier.
//! - **Hub tunnel upload (SPU):** a packet a member sends over its validated UDP session is routed like a carrier
//!   packet. The host passes the member's id only for a datagram that arrived on a validated session; an SPU
//!   without one is refused.

use core::net::SocketAddr;

use vinc_crypto::NodeId;

use super::datagram::{Datagram, MAX_DNS_DATAGRAM};
use super::route::Pkt;
use super::sleep::{Notice, SKEW_MS, SleepError};
use super::{Effect, Reject, Relay, Sink, Sleeper, Trace, UdpTarget, route};

impl<const C: usize, const R: usize, const MN: usize, const MB: usize> Relay<C, R, MN, MB> {
    /// A UDP datagram arrived from `src`. `from_member` is the node whose validated UDP session carried it, if the
    /// host knows one; such a datagram also refreshes the member's tunnel freshness.
    ///
    /// # Errors
    /// The [`Reject`] reason; the datagram is dropped and traced.
    pub fn datagram<S: Sink>(
        &mut self,
        now: u64,
        src: SocketAddr,
        from_member: Option<&NodeId>,
        bytes: &[u8],
        sink: &mut S,
    ) -> Result<(), Reject> {
        let d = Datagram::decode(bytes).map_err(|e| self.reject(sink, Reject::BadDatagram(e), from_member.copied()))?;
        if let Some(m) = from_member {
            let _ = self.udp_heard(now, m, sink);
        }
        match d {
            Datagram::Qad { nonce } => {
                self.stats.qad += 1;
                sink.emit(Effect::Trace(Trace::QadAnswered));
                sink.emit(Effect::Udp {
                    to: UdpTarget::Reply(src),
                    datagram: Datagram::Qadr { nonce, addr: src },
                });
                Ok(())
            }
            Datagram::DnsQuery { peer } => {
                let answer = self.answer(now, &peer, MAX_DNS_DATAGRAM - 35, sink);
                sink.emit(Effect::Udp {
                    to: UdpTarget::Reply(src),
                    datagram: Datagram::DnsReply { peer, answer },
                });
                Ok(())
            }
            Datagram::Sleep { notice } => self.sleep_notice(now, notice, None, sink),
            Datagram::Spu { dst, flag, packet } => {
                let Some(member) = from_member else {
                    return Err(self.reject(sink, Reject::Unauthenticated, None));
                };
                if dst == self.cfg.me {
                    return Err(self.reject(sink, Reject::NoRoute, Some(*member)));
                }
                self.route(
                    now,
                    &Pkt {
                        src: member,
                        dst: &dst,
                        flag,
                        packet,
                    },
                    route::Origin::Tunnel,
                    sink,
                )
            }
            Datagram::Qadr { .. } | Datagram::DnsReply { .. } | Datagram::Spl { .. } => {
                Err(self.reject(sink, Reject::UnexpectedFrame, from_member.copied()))
            }
        }
    }

    /// A signed sleep notice arrived, over UDP (`sender` is `None`) or on the carrier of `sender`.
    ///
    /// # Errors
    /// [`Reject::BadSleep`] naming the cause, or [`Reject::SessionsFull`] if the table has no room.
    pub fn sleep_notice<S: Sink>(
        &mut self,
        now: u64,
        bytes: &[u8],
        sender: Option<&NodeId>,
        sink: &mut S,
    ) -> Result<(), Reject> {
        let n = Notice::parse(bytes).map_err(|e| self.reject(sink, Reject::BadSleep(e), sender.copied()))?;
        let refuse =
            |this: &mut Self, sink: &mut S, e: SleepError| this.reject(sink, Reject::BadSleep(e), Some(n.node));
        if sender.is_some_and(|s| *s != n.node) {
            return Err(refuse(self, sink, SleepError::WrongSender));
        }
        if (now / 1_000_000).abs_diff(n.ts_ms) >= SKEW_MS {
            return Err(refuse(self, sink, SleepError::Skew));
        }
        if !self.clients.contains(&n.node) && !self.gone.contains(&n.node) {
            return Err(refuse(self, sink, SleepError::UnknownNode));
        }
        let me = self.cfg.me;
        n.verify(&me).map_err(|e| refuse(self, sink, e))?;
        let woke = self.sleeping.get(&n.node).map_or(0, |s| s.woke);
        if self.sleeping.insert(n.node, Sleeper { at: now, woke }).is_err() {
            return Err(self.reject(sink, Reject::SessionsFull, Some(n.node)));
        }
        sink.emit(Effect::Trace(Trace::SleepAccepted { node: n.node }));
        Ok(())
    }
}
