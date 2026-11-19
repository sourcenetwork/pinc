//! The relay a hub runs for its members, as the host core drives it: the carrier streams of members (TCP, with the
//! carrier handshake and its frames), the effects the relay asks for, and the slots under which a member's relayed
//! packets reach the node.
//!
//! Invariants: a carrier stream belongs to at most one member and a member has at most one carrier (a newer one replaces
//! the older and the older is closed); an effect the relay asks for is carried out in the order it came.

use std::collections::HashMap;

use pinc_connect::carrier::MAX_FRAME_LEN;
use pinc_connect::carrier::session::{Poll, ProtectedCarrier};
use pinc_connect::relay::{Effect, Relay, SessionId as RSession, Sink, Trace, UdpTarget};
use pinc_core::relay_addr;
use pinc_crypto::{NodeId, Software};
use pinc_security::{Env, KeyHandle, ResponderStores, SoftKeys};

use super::core::{Core, LOCAL_RELAY, Op, StreamId};

/// The relay a hub runs for its members.
pub(super) type HubRelay = Relay<24, 16, 8, 4096>;

pub(super) enum Eff {
    Carrier(NodeId, Vec<u8>),
    Udp(UdpTarget, Vec<u8>),
    Local(NodeId, Vec<u8>),
    Close(NodeId, RSession),
    Trace(Trace),
}

#[derive(Default)]
pub(super) struct Collect(pub(super) Vec<Eff>);

impl Sink for Collect {
    fn emit(&mut self, e: Effect<'_>) {
        let eff = match e {
            Effect::Carrier { to, frame } => {
                let mut b = vec![0u8; MAX_FRAME_LEN];
                let Ok(n) = frame.encode(&mut b) else { return };
                b.truncate(n);
                Eff::Carrier(to, b)
            }
            Effect::Udp { to, datagram } => {
                let mut b = vec![0u8; 2048];
                let Ok(n) = datagram.encode(&mut b) else { return };
                b.truncate(n);
                Eff::Udp(to, b)
            }
            Effect::Local { from, packet } => Eff::Local(from, packet.to_vec()),
            Effect::Close { node, session, .. } => Eff::Close(node, session),
            Effect::PeerRelay { .. } | Effect::Wake { .. } => return,
            Effect::Trace(t) => Eff::Trace(t),
        };
        self.0.push(eff);
    }
}

pub(super) struct RStream {
    pub(super) carrier: Box<ProtectedCarrier<Software>>,
    pub(super) node: Option<NodeId>,
    pub(super) session: Option<RSession>,
}

/// The relay a hub runs for its members.
pub(super) struct HubSide {
    pub(super) relay: Box<HubRelay>,
    pub(super) streams: HashMap<StreamId, RStream>,
    pub(super) by_node: HashMap<NodeId, StreamId>,
    pub(super) stores: ResponderStores<4, 4>,
    pub(super) slots: Vec<NodeId>,
    pub(super) scid: u64,
}

pub(super) enum Step {
    Idle,
    Flush,
    Frame,
    Open(NodeId),
    Dead,
}

impl<const K: usize, const D: usize> Core<K, D> {
    pub(super) fn slot(&mut self, n: &NodeId) -> Option<u16> {
        let hub = self.hub.as_mut()?;
        let i = hub.slots.iter().position(|x| x == n).unwrap_or_else(|| {
            hub.slots.push(*n);
            hub.slots.len() - 1
        });
        u16::try_from(i).ok()
    }

    // ---------------------------------------------------------------- the relay of a hub

    pub(super) fn apply(&mut self, now: u64, s: Collect) {
        for e in s.0 {
            match e {
                Eff::Carrier(to, plain) => self.write_frame(to, &plain),
                Eff::Udp(UdpTarget::Reply(a), d) => self.small.push_back((a, d)),
                Eff::Udp(UdpTarget::Member(n), d) => {
                    if let Some(a) = self.node.member_addr(&n) {
                        self.small.push_back((a, d));
                    }
                }
                Eff::Local(from, packet) => {
                    if let Some(slot) = self.slot(&from) {
                        let mut p = packet;
                        self.node
                            .handle_datagram(now, self.addr, relay_addr(false, LOCAL_RELAY, slot), &mut p);
                    }
                }
                Eff::Close(node, session) => {
                    let Some(hub) = self.hub.as_mut() else { continue };
                    if let Some(sid) = hub.by_node.get(&node).copied()
                        && hub.streams.get(&sid).and_then(|r| r.session) == Some(session)
                    {
                        self.ops.push_back(Op::Close { stream: sid });
                        hub.streams.remove(&sid);
                        hub.by_node.remove(&node);
                    }
                }
                Eff::Trace(t) => self.node.relay_trace(now, &t),
            }
        }
    }

    pub(super) fn write_frame(&mut self, to: NodeId, plain: &[u8]) {
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(sid) = hub.by_node.get(&to).copied() else {
            return;
        };
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        let Ok(n) = rs.carrier.seal_bytes(&self.prov, plain, &mut out) else {
            return;
        };
        out.truncate(n);
        self.ops.push_back(Op::Write { stream: sid, data: out });
    }

    pub(super) fn flush_handshake(&mut self, sid: StreamId) {
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut buf = vec![0u8; 32 * 1024];
        loop {
            let n = rs.carrier.transmit(&mut buf);
            if n == 0 {
                break;
            }
            if let Some(d) = buf.get(..n) {
                self.ops.push_back(Op::Write {
                    stream: sid,
                    data: d.to_vec(),
                });
            }
        }
    }

    pub(super) fn drain(&mut self, now: u64, sid: StreamId) {
        for _ in 0..1024 {
            let mut sink = Collect::default();
            let step = {
                let Some(hub) = self.hub.as_mut() else { return };
                let Some(rs) = hub.streams.get_mut(&sid) else { return };
                let mut env = Env {
                    provider: &self.prov,
                    now,
                    drbg: &mut self.hdrbg,
                };
                match rs.carrier.poll(&mut env, &mut hub.stores) {
                    Ok(Poll::Idle) => Step::Idle,
                    Ok(Poll::Handshake) => Step::Flush,
                    Ok(Poll::KeyRequest) => {
                        let soft = SoftKeys {
                            signer: Some((KeyHandle(1), &self.kp)),
                            prekeys: None,
                        };
                        if rs.carrier.answer_soft(&mut env, &soft).is_ok() {
                            Step::Flush
                        } else {
                            Step::Dead
                        }
                    }
                    Ok(Poll::Open(peer)) => Step::Open(peer),
                    Ok(Poll::Frame(f)) => {
                        if let (Some(node), Some(sess)) = (rs.node, rs.session) {
                            let _ = hub.relay.carrier_frame(now, &node, sess, &f, &mut sink);
                        }
                        Step::Frame
                    }
                    Err(e) => {
                        if e.is_fatal() {
                            Step::Dead
                        } else {
                            Step::Flush
                        }
                    }
                }
            };
            match step {
                Step::Idle => {
                    self.flush_handshake(sid);
                    return;
                }
                Step::Flush => self.flush_handshake(sid),
                Step::Frame => self.apply(now, sink),
                Step::Open(peer) => {
                    self.flush_handshake(sid);
                    let mut s = Collect::default();
                    let Some(hub) = self.hub.as_mut() else { return };
                    if let Ok(sess) = hub.relay.carrier_opened(now, peer, &mut s) {
                        if let Some(rs) = hub.streams.get_mut(&sid) {
                            rs.node = Some(peer);
                            rs.session = Some(sess);
                        }
                        if let Some(old) = hub.by_node.insert(peer, sid)
                            && old != sid
                        {
                            hub.streams.remove(&old);
                            self.ops.push_back(Op::Close { stream: old });
                        }
                    }
                    self.apply(now, s);
                }
                Step::Dead => {
                    self.ops.push_back(Op::Close { stream: sid });
                    self.drop_stream(now, sid);
                    return;
                }
            }
        }
    }

    pub(super) fn drop_stream(&mut self, now: u64, sid: StreamId) {
        let Some(hub) = self.hub.as_mut() else { return };
        if let Some(rs) = hub.streams.remove(&sid)
            && let (Some(node), Some(sess)) = (rs.node, rs.session)
        {
            if hub.by_node.get(&node) == Some(&sid) {
                hub.by_node.remove(&node);
            }
            let mut s = Collect::default();
            hub.relay.carrier_closed(now, &node, sess, &mut s);
            self.apply(now, s);
        }
    }

    // ---------------------------------------------------------------- inputs
}
