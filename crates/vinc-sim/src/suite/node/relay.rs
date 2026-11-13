//! The relay a hub runs for its members: the host side of `vinc_connect::relay`.
//!
//! A hub accepts the carriers its members open (plain TCP or WebSocket streams), runs the authenticated handshake on
//! each, hands the decoded frames to the relay and writes the relay's frames back. Datagrams that are relay requests
//! (address discovery, lookups) go to the relay; the packets the relay delivers to the hub's own node reach it as
//! datagrams from a synthetic relay address, and the packets the node sends to a member's synthetic address are
//! handed to the relay.
//!
//! Invariants: a member has at most one live carrier at the hub (a newer one replaces the older); every carrier that
//! ends is reported to the relay and to the node exactly once; the relay and the node see the same local time.

use std::collections::BTreeMap;
use std::net::SocketAddr;

use vinc_connect::carrier::MAX_FRAME_LEN;
use vinc_connect::carrier::session::{self, Poll, ProtectedCarrier};
use vinc_connect::carrier::ws::{Decoder, Role as WsRole};
use vinc_connect::relay::datagram::Datagram;
use vinc_connect::relay::{Config as RelayConfig, Effect, Relay, SessionId as RSession, Sink, Trace, UdpTarget};
use vinc_core::relay_addr;
use vinc_crypto::NodeId;
use vinc_node::{MemberNotice, is_relay_request};
use vinc_security::{ConnId, Env, KeyHandle, LocalIdentity, ResponderStores, SoftKeys};

use super::core::Core;
use crate::suite::crypto::Tracked;
use crate::{StreamId, StreamOp};

/// The relay-path index the hub's own relay uses for its members: an index no client has.
pub(super) const LOCAL_RELAY: u8 = 0xFE;

pub(super) type HubRelay = Relay<{ super::SESSIONS }, 128, 16, 4096>;

pub(super) enum Eff {
    Carrier(NodeId, Vec<u8>),
    Udp(UdpTarget, Vec<u8>),
    Peer(NodeId, Vec<u8>),
    Local(NodeId, Vec<u8>),
    Close(NodeId, RSession),
    Trace(Trace),
}

#[derive(Default)]
pub(super) struct Collect(Vec<Eff>);

impl Sink for Collect {
    fn emit(&mut self, e: Effect<'_>) {
        self.0.push(match e {
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
            Effect::PeerRelay { to, frame } => {
                let mut b = vec![0u8; MAX_FRAME_LEN];
                let Ok(n) = frame.encode(&mut b) else { return };
                b.truncate(n);
                Eff::Peer(to, b)
            }
            Effect::Wake { .. } => return,
            Effect::Trace(t) => Eff::Trace(t),
        });
    }
}

pub(super) struct RStream {
    pub(super) carrier: Box<ProtectedCarrier<Tracked>>,
    pub(super) node: Option<NodeId>,
    session: Option<RSession>,
    ws: Option<Decoder>,
    sniffed: bool,
    /// The carrier joins this relay to a peer relay; its frames are the relays' own.
    pub(super) peer: bool,
    /// This relay dialed the carrier.
    pub(super) dialer: bool,
}

impl RStream {
    /// A carrier this relay dialed (`dialer`) or accepted.
    pub(super) fn new(carrier: Box<ProtectedCarrier<Tracked>>, dialer: bool) -> Self {
        Self {
            carrier,
            node: None,
            session: None,
            ws: None,
            sniffed: dialer,
            peer: dialer,
            dialer,
        }
    }
}

enum Step {
    Idle,
    Flush,
    Frame,
    Open(NodeId),
    Dead,
}

/// The relay of a hub and the carriers it serves.
pub(super) struct HubSide {
    pub(super) relay: Box<HubRelay>,
    pub(super) streams: BTreeMap<StreamId, RStream>,
    by_node: BTreeMap<[u8; 32], StreamId>,
    /// The carrier of each peer relay that is up.
    pub(super) peer_by_node: BTreeMap<[u8; 32], StreamId>,
    /// The peer relays this relay dials.
    pub(super) peers_out: Vec<super::peers::PeerOut>,
    stores: ResponderStores<4, 4>,
    slots: Vec<NodeId>,
    pub(super) scid: u64,
}

impl HubSide {
    pub(super) fn new(me: NodeId, seed: u64) -> Self {
        Self {
            relay: Box::new(HubRelay::new(RelayConfig::new(me, seed))),
            streams: BTreeMap::new(),
            by_node: BTreeMap::new(),
            peer_by_node: BTreeMap::new(),
            peers_out: Vec::new(),
            stores: ResponderStores::default(),
            slots: Vec::new(),
            scid: 0,
        }
    }

    /// The relay's next deadline, in local time: its own timers and the next dial of a peer relay.
    pub(super) fn next_deadline(&self) -> Option<u64> {
        let dials = self.peers_out.iter().filter(|p| p.stream.is_none()).map(|p| p.retry_at);
        self.relay.next_deadline().into_iter().chain(dials).min()
    }
}

fn wrap(rs: &RStream, bytes: &[u8]) -> Vec<u8> {
    if rs.ws.is_some() {
        super::carrier::ws_frames(bytes, None)
    } else {
        bytes.to_vec()
    }
}

impl Core {
    pub(super) fn write_op(&mut self, stream: StreamId, data: Vec<u8>) {
        let op = StreamOp::Write {
            stream,
            len: data.len(),
            send_at: None,
        };
        self.wire.ops.push_back((op, data));
    }

    /// The slot a member has in the relay's synthetic address space.
    fn slot(hub: &mut HubSide, n: &NodeId) -> u16 {
        let i = hub.slots.iter().position(|x| x == n).unwrap_or_else(|| {
            hub.slots.push(*n);
            hub.slots.len() - 1
        });
        u16::try_from(i).unwrap_or(u16::MAX)
    }

    /// A datagram reached this hub: a relay request, or traffic for the node.
    pub(super) fn hub_datagram(&mut self, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        let now = self.local;
        let request = self.hub.is_some() && is_relay_request(data);
        if request {
            let member = self.node.as_ref().and_then(|n| n.member_at(&remote));
            let mut s = Collect::default();
            if let Some(h) = self.hub.as_mut() {
                // A refused request is dropped and traced by the relay itself.
                let refused = h.relay.datagram(now, remote, member.as_ref(), data, &mut s).is_err();
                if refused
                    && self.shared.is_watched(self.idx)
                    && super::in_trace_window(self.now)
                    && let Ok(Datagram::Spu { dst, .. }) = Datagram::decode(data)
                {
                    let to = self.shared.index_of(&dst).unwrap_or(usize::MAX);
                    let line = format!("n{} true{} refused a tunnel packet to {to}", self.idx, self.now);
                    self.shared.note_trace(line);
                }
            }
            self.reply_from = Some(local);
            self.apply(s);
            self.reply_from = None;
            return;
        }
        if data.first().is_some_and(|b| *b >= 0x40)
            && let Some(n) = self.node.as_ref().and_then(|n| n.member_at(&remote))
            && let Some(h) = self.hub.as_mut()
        {
            let _ = h.relay.udp_heard(&n, now);
        }
        if let Some(node) = self.node.as_mut() {
            node.handle_datagram(now, local, remote, data);
        }
    }

    /// The node sent a packet to the synthetic address of a member of its own relay.
    pub(super) fn hub_send_local(&mut self, slot: u16, packet: &[u8]) {
        let now = self.local;
        let mut s = Collect::default();
        if let Some(h) = self.hub.as_mut()
            && let Some(node) = h.slots.get(usize::from(slot)).copied()
        {
            // No route to a member that left is the relay's refusal; the packet is lost as on a real path.
            let _ = h.relay.send_local(now, &node, 0, packet, &mut s);
        }
        self.apply(s);
    }

    /// What the node told the hub's relay about its members since the last call. True if there was any.
    pub(super) fn hub_members(&mut self) -> bool {
        let now = self.local;
        let mut any = false;
        while let Some(notice) = self.node.as_mut().and_then(|n| n.poll_member()) {
            any = true;
            let Some(h) = self.hub.as_mut() else { continue };
            match notice {
                MemberNotice::Gone(n) => h.relay.udp_gone(&n),
                MemberNotice::Awake(n) => {
                    let mut s = Collect::default();
                    h.relay.member_returned(now, &n, &mut s);
                    self.apply(s);
                }
            }
        }
        any
    }

    /// The relay's timers.
    pub(super) fn hub_timeout(&mut self) {
        let now = self.local;
        let mut s = Collect::default();
        if let Some(h) = self.hub.as_mut()
            && h.relay.next_deadline().is_some_and(|d| d <= now)
        {
            h.relay.handle_timeout(now, &mut s);
        }
        self.apply(s);
        self.hub_dial_peers();
    }

    pub(super) fn apply(&mut self, s: Collect) {
        let now = self.local;
        let from = self.udp_addr();
        for e in s.0 {
            match e {
                Eff::Carrier(to, plain) => self.write_frame(&to, &plain),
                Eff::Peer(to, plain) => self.write_peer(&to, &plain),
                Eff::Udp(UdpTarget::Reply(a), d) => {
                    // From the address the request came to: a reply from another family or interface is lost.
                    if let Some(f) = self.reply_from.or(from) {
                        self.wire.datagrams.push_back((f, a, d));
                    }
                }
                Eff::Udp(UdpTarget::Member(n), d) => {
                    // From the address of the member's session, to its address: a member reached over IPv6 is not
                    // reached from the hub's IPv4 address.
                    if let Some((f, a)) = self.node.as_ref().and_then(|node| node.member_route(&n)) {
                        self.wire.datagrams.push_back((f, a, d));
                    }
                }
                Eff::Local(f, mut packet) => {
                    let slot = self.hub.as_mut().map_or(0, |h| Self::slot(h, &f));
                    if let (Some(node), Some(local)) = (self.node.as_mut(), from) {
                        node.handle_datagram(now, local, relay_addr(false, LOCAL_RELAY, slot), &mut packet);
                    }
                }
                Eff::Close(node, session) => {
                    let Some(h) = self.hub.as_mut() else { continue };
                    if let Some(sid) = h.by_node.get(&node.bytes).copied()
                        && h.streams.get(&sid).and_then(|r| r.session) == Some(session)
                    {
                        h.streams.remove(&sid);
                        h.by_node.remove(&node.bytes);
                        self.wire.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
                    }
                }
                Eff::Trace(t) => self.relay_trace(&t),
            }
        }
    }

    fn relay_trace(&mut self, t: &Trace) {
        if super::decision_trace()
            && let Trace::CarrierClosed { node, .. } = t
            && let Some(peer) = self.shared.index_of(node)
        {
            self.decision("CarrierGone", peer);
        }
        if self.shared.is_watched(self.idx) && super::in_trace_window(self.now) {
            let ix = |id: &NodeId| self.shared.index_of(id).unwrap_or(usize::MAX);
            let line = match t {
                Trace::Routed { src, dst, route, bytes } => {
                    format!("Routed {} -> {} {route:?} {bytes}", ix(src), ix(dst))
                }
                other => self.shared.name_ids(&format!("{other:?}")),
            };
            self.shared
                .note_trace(format!("n{} true{} Relay({line})", self.idx, self.now));
        }
        let now = self.local;
        if let Some(node) = self.node.as_mut() {
            node.relay_trace(now, t);
        }
    }

    fn write_frame(&mut self, to: &NodeId, plain: &[u8]) {
        let prov = self.provider();
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(sid) = hub.by_node.get(&to.bytes).copied() else {
            return;
        };
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        let Ok(n) = rs.carrier.seal_bytes(&prov, plain, &mut out) else {
            return;
        };
        out.truncate(n);
        let data = wrap(rs, &out);
        self.write_op(sid, data);
    }

    pub(super) fn flush_handshake(&mut self, sid: StreamId) {
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut buf = vec![0u8; 32 * 1024];
        let mut out = Vec::new();
        loop {
            let n = rs.carrier.transmit(&mut buf);
            let Some(b) = buf.get(..n).filter(|b| !b.is_empty()) else {
                break;
            };
            out.push(wrap(rs, b));
        }
        for data in out {
            self.write_op(sid, data);
        }
    }

    pub(super) fn drain(&mut self, sid: StreamId) {
        for _ in 0..1024 {
            let now = self.local;
            let prov = self.provider();
            let mut sink = Collect::default();
            let step = {
                let Some(hub) = self.hub.as_mut() else { return };
                let Some(rs) = hub.streams.get_mut(&sid) else { return };
                let mut env = Env {
                    provider: &prov,
                    now,
                    drbg: &mut self.hub_drbg,
                };
                match rs.carrier.poll(&mut env, &mut hub.stores) {
                    Ok(Poll::Idle) => Step::Idle,
                    Ok(Poll::KeyRequest) => {
                        let soft = SoftKeys {
                            signer: Some((KeyHandle(1), &self.kp)),
                            prekeys: self.prekeys.as_ref(),
                        };
                        // A handshake may need several key operations in a row, and answering the last one
                        // completes it.
                        loop {
                            match rs.carrier.answer_soft(&mut env, &soft) {
                                Ok(Poll::KeyRequest) => {}
                                Ok(Poll::Open(peer)) => break Step::Open(peer),
                                Ok(_) => break Step::Flush,
                                Err(_) => break Step::Dead,
                            }
                        }
                    }
                    Ok(Poll::Open(peer)) => Step::Open(peer),
                    Ok(Poll::Frame(f)) => {
                        if rs.peer {
                            if let Some(node) = rs.node {
                                // A refused frame is dropped and traced by the relay; the carrier stays up.
                                let _ = hub.relay.peer_frame(now, &node, &f, &mut sink);
                            }
                        } else if let (Some(node), Some(sess)) = (rs.node, rs.session) {
                            let _ = hub.relay.carrier_frame(now, &node, sess, &f, &mut sink);
                        }
                        Step::Frame
                    }
                    Err(e) if e.is_fatal() => Step::Dead,
                    Ok(Poll::Handshake) | Err(_) => Step::Flush,
                }
            };
            match step {
                Step::Idle => {
                    self.flush_handshake(sid);
                    return;
                }
                Step::Flush => self.flush_handshake(sid),
                Step::Frame => self.apply(sink),
                Step::Open(peer) => self.hub_open(sid, peer),
                Step::Dead => {
                    self.wire.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
                    self.hub_closed(sid);
                    return;
                }
            }
        }
    }

    fn hub_open(&mut self, sid: StreamId, peer: NodeId) {
        let now = self.local;
        self.flush_handshake(sid);
        let is_peer = self
            .hub
            .as_ref()
            .and_then(|h| h.streams.get(&sid))
            .is_some_and(|r| r.dialer || r.carrier.is_peer_relay());
        if is_peer {
            self.hub_peer_open(sid, peer);
            return;
        }
        let mut s = Collect::default();
        let mut replaced = None;
        if let Some(hub) = self.hub.as_mut()
            && let Ok(sess) = hub.relay.carrier_opened(now, peer, &mut s)
        {
            if let Some(rs) = hub.streams.get_mut(&sid) {
                rs.node = Some(peer);
                rs.session = Some(sess);
            }
            if let Some(old) = hub.by_node.insert(peer.bytes, sid)
                && old != sid
            {
                hub.streams.remove(&old);
                replaced = Some(old);
            }
        }
        if let Some(old) = replaced {
            self.wire.ops.push_back((StreamOp::Close { stream: old }, Vec::new()));
        }
        self.apply(s);
    }

    /// A carrier stream of this hub ended.
    pub(super) fn hub_closed(&mut self, sid: StreamId) {
        let now = self.local;
        let mut s = Collect::default();
        self.hub_peer_closed(sid);
        if let Some(hub) = self.hub.as_mut()
            && let Some(rs) = hub.streams.remove(&sid)
            && let (Some(node), Some(sess)) = (rs.node, rs.session)
        {
            if hub.by_node.get(&node.bytes) == Some(&sid) {
                hub.by_node.remove(&node.bytes);
            }
            hub.relay.carrier_closed(now, &node, sess, &mut s);
        }
        self.apply(s);
    }

    /// A member opened a carrier stream to this hub.
    pub(super) fn hub_accept(&mut self, stream: StreamId) {
        let Ok(identity) = LocalIdentity::from_keypair(&self.kp, KeyHandle(1)) else {
            return;
        };
        let Some(hub) = self.hub.as_mut() else { return };
        hub.scid += 1;
        let Some(scid) = ConnId::new(&hub.scid.to_be_bytes()) else {
            return;
        };
        let Ok(cfg) = session::responder_config(identity, scid) else {
            return;
        };
        hub.streams
            .insert(stream, RStream::new(Box::new(ProtectedCarrier::accept(cfg)), false));
    }

    /// A record arrived on a carrier stream of this hub.
    pub(super) fn hub_record(&mut self, stream: StreamId, data: &mut [u8]) {
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(rs) = hub.streams.get_mut(&stream) else {
            return;
        };
        if !rs.sniffed {
            rs.sniffed = true;
            // A WebSocket frame starts 0x82 (final binary); a handshake unit starts with a length below 0x8000.
            if data.first() == Some(&0x82) {
                rs.ws = Some(Decoder::new(WsRole::Client));
            }
        }
        let payloads = match rs.ws.as_mut() {
            Some(dec) => super::carrier::ws_payloads(dec, data),
            None => vec![data.to_vec()],
        };
        for p in payloads {
            let mut rest: &[u8] = &p;
            for _ in 0..64 {
                let Some(rs) = self.hub.as_mut().and_then(|h| h.streams.get_mut(&stream)) else {
                    return;
                };
                let n = rs.carrier.receive(rest);
                rest = rest.get(n..).unwrap_or_default();
                self.drain(stream);
                if rest.is_empty() || n == 0 {
                    break;
                }
            }
        }
    }
}
