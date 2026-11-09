//! A simulated relay node: the `vinc-connect` relay with its own endpoint (the hub), the protected carrier accepting
//! sessions over simulated TCP and WebSocket streams, and the UDP side of the relay.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::must_use_candidate,
    clippy::large_stack_arrays
)]

use std::collections::{HashMap, VecDeque};
use std::net::SocketAddr;

use vinc_connect::carrier::MAX_FRAME_LEN;
use vinc_connect::carrier::session::{self, Poll, ProtectedCarrier};
use vinc_connect::carrier::ws::{self, Decoder, Opcode, Role as WsRole, WsFrame};
use vinc_connect::relay::{Config, Effect, Relay, SessionId as RSession, Sink, Trace, UdpTarget};
use vinc_core::{Command, Event, Query, SessionId, is_relay_addr, relay_addr, relay_parts};
use vinc_crypto::NodeId;
use vinc_security::{ConnId, Env, KeyHandle, ResponderStores, SoftKeys};
use vinc_sim::{StreamEvent, StreamId, StreamOp, Time};

use crate::Caps;
use crate::connect_host::{Ev, Host, Outbox};

pub type RelayT = Relay<16, 16, 8, 4096>;

enum Eff {
    Carrier(NodeId, Vec<u8>),
    Udp(UdpTarget, Vec<u8>),
    Local(NodeId, Vec<u8>),
    Close(NodeId, RSession),
    Wake(NodeId),
    Trace(Trace),
}

#[derive(Default)]
struct Collect(Vec<Eff>);

impl Sink for Collect {
    fn emit(&mut self, e: Effect<'_>) {
        self.0.push(match e {
            Effect::Carrier { to, frame } => {
                let mut b = vec![0u8; MAX_FRAME_LEN];
                let n = frame.encode(&mut b).unwrap();
                b.truncate(n);
                Eff::Carrier(to, b)
            }
            Effect::PeerRelay { .. } => return,
            Effect::Udp { to, datagram } => {
                let mut b = vec![0u8; 2048];
                let n = datagram.encode(&mut b).unwrap();
                b.truncate(n);
                Eff::Udp(to, b)
            }
            Effect::Local { from, packet } => Eff::Local(from, packet.to_vec()),
            Effect::Close { node, session, .. } => Eff::Close(node, session),
            Effect::Wake { node } => Eff::Wake(node),
            Effect::Trace(t) => Eff::Trace(t),
        });
    }
}

struct RStream {
    carrier: Box<ProtectedCarrier<Caps>>,
    node: Option<NodeId>,
    session: Option<RSession>,
    ws: Option<Decoder>,
    sniffed: bool,
}

pub struct RelayNode {
    pub host: Host,
    pub relay: Box<RelayT>,
    pub addr: SocketAddr,
    streams: HashMap<StreamId, RStream>,
    by_node: HashMap<NodeId, StreamId>,
    stores: ResponderStores<4, 4>,
    slots: Vec<NodeId>,
    members: HashMap<SessionId, NodeId>,
    pub out: Outbox,
    pub events: VecDeque<Ev>,
    now: Time,
    scid: u64,
    /// Every relay trace event with its time.
    pub traces: Vec<(Time, Trace)>,
    pub wakes: Vec<(Time, NodeId)>,
    /// Carriers that opened, with the time.
    pub carriers_opened: Vec<(Time, NodeId)>,
    pub carriers_ws: u64,
    /// Stream records received.
    pub records: u64,
    /// Lookups answered over UDP and over a carrier.
    pub dns_udp: u64,
    pub dns_carrier: u64,
    /// Every datagram the hub endpoint transmitted: time, destination and length.
    pub tx_log: Vec<(Time, SocketAddr, usize)>,
}

impl RelayNode {
    pub fn new(tag: u8, addr: SocketAddr, now: Time) -> Self {
        let host = Host::new(tag, addr, now);
        let relay = Box::new(RelayT::new(Config::new(host.me, 0x5eed ^ u64::from(tag))));
        Self {
            host,
            relay,
            addr,
            streams: HashMap::new(),
            by_node: HashMap::new(),
            stores: ResponderStores::default(),
            slots: Vec::new(),
            members: HashMap::new(),
            out: Outbox::default(),
            events: VecDeque::new(),
            now,
            scid: 0,
            traces: Vec::new(),
            wakes: Vec::new(),
            carriers_opened: Vec::new(),
            carriers_ws: 0,
            records: 0,
            dns_udp: 0,
            dns_carrier: 0,
            tx_log: Vec::new(),
        }
    }

    pub fn id(&self) -> NodeId {
        self.host.me
    }

    fn slot(&mut self, n: &NodeId) -> u16 {
        let i = self.slots.iter().position(|x| x == n).unwrap_or_else(|| {
            self.slots.push(*n);
            self.slots.len() - 1
        });
        u16::try_from(i).unwrap()
    }

    /// The address of a validated hub session with `node`.
    fn member_addr(&self, node: &NodeId) -> Option<SocketAddr> {
        let (sid, _) = self.members.iter().find(|(_, n)| *n == node)?;
        self.session_remote(*sid)
    }

    fn session_remote(&self, sid: SessionId) -> Option<SocketAddr> {
        match self.host.ep.query(Query::Stats(sid)) {
            vinc_core::Answer::Stats(st) if st.path_validated => st.route.map(|(_, r)| r).filter(|r| !is_relay_addr(r)),
            _ => None,
        }
    }

    fn member_at(&self, src: &SocketAddr) -> Option<NodeId> {
        self.members
            .iter()
            .find(|(sid, _)| self.session_remote(**sid) == Some(*src))
            .map(|(_, n)| *n)
    }

    pub fn pump(&mut self, now: Time) {
        self.now = now;
        for _ in 0..64 {
            let mut busy = self.events_step(now);
            busy |= self.tx_step(now);
            if !busy {
                return;
            }
        }
        panic!("the host loop of a relay does not settle at {now}");
    }

    fn events_step(&mut self, now: u64) -> bool {
        let mut did = false;
        while let Some(ev) = self.host.next_event() {
            did = true;
            self.host.duty(now, &ev);
            match ev {
                Event::Incoming { session, node, .. } => {
                    self.members.insert(session, node);
                    let _ = self.host.command(
                        now,
                        Command::SetRole {
                            session,
                            role: vinc_core::Role::Member,
                        },
                    );
                }
                Event::Closed { session, .. } => {
                    if let Some(n) = self.members.remove(&session) {
                        self.relay.udp_gone(&n);
                    }
                }
                Event::PeerAwake { session } => {
                    if let Some(n) = self.members.get(&session).copied() {
                        let mut s = Collect::default();
                        self.relay.member_returned(now, &n, &mut s);
                        self.apply(now, s);
                    }
                }
                _ => {}
            }
            self.events.push_back(Ev::Ep(ev));
        }
        did
    }

    fn tx_step(&mut self, now: u64) -> bool {
        let mut did = false;
        let mut buf = vec![0u8; 2048];
        while let Some(t) = self.host.ep.poll_transmit(now, &mut buf) {
            did = true;
            self.tx_log.push((now, t.remote, t.len));
            if let Some((_, slot)) = relay_parts(&t.remote) {
                let Some(node) = self.slots.get(usize::from(slot)).copied() else {
                    continue;
                };
                let mut s = Collect::default();
                let _ = self.relay.send_local(now, &node, 0, &buf[..t.len], &mut s);
                self.apply(now, s);
            } else {
                self.out.datagrams.push_back((t.local, t.remote, buf[..t.len].to_vec()));
            }
        }
        did
    }

    fn apply(&mut self, now: Time, s: Collect) {
        for e in s.0 {
            match e {
                Eff::Carrier(to, plain) => {
                    if matches!(
                        vinc_connect::carrier::Frame::decode(&plain),
                        Ok(vinc_connect::carrier::Frame::DnsReply { .. })
                    ) {
                        self.dns_carrier += 1;
                    }
                    self.write_frame(to, &plain);
                }
                Eff::Udp(UdpTarget::Reply(a), d) => {
                    if matches!(
                        vinc_connect::relay::datagram::Datagram::decode(&d),
                        Ok(vinc_connect::relay::datagram::Datagram::DnsReply { .. })
                    ) {
                        self.dns_udp += 1;
                    }
                    self.out.datagrams.push_back((self.addr, a, d));
                }
                Eff::Udp(UdpTarget::Member(n), d) => {
                    if let Some(a) = self.member_addr(&n) {
                        self.out.datagrams.push_back((self.addr, a, d));
                    }
                }
                Eff::Local(from, packet) => {
                    let slot = self.slot(&from);
                    let mut p = packet;
                    self.host
                        .ep
                        .handle_datagram(now, self.addr, relay_addr(false, 0, slot), &mut p);
                }
                Eff::Close(node, session) => {
                    if let Some(sid) = self.by_node.get(&node).copied()
                        && self.streams.get(&sid).and_then(|r| r.session) == Some(session)
                    {
                        self.out.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
                        self.streams.remove(&sid);
                        self.by_node.remove(&node);
                    }
                }
                Eff::Wake(n) => {
                    self.wakes.push((now, n));
                    self.events.push_back(Ev::Wake(n));
                }
                Eff::Trace(t) => {
                    if let Trace::Pulse { node } = t
                        && let Some((sid, _)) = self.members.iter().find(|(_, n)| **n == node)
                    {
                        let _ = self.host.command(
                            now,
                            Command::Pulse {
                                session: *sid,
                                sent: true,
                            },
                        );
                    }
                    self.traces.push((now, t));
                    self.events.push_back(Ev::Trace(t));
                }
            }
        }
    }

    fn write_frame(&mut self, to: NodeId, plain: &[u8]) {
        let Some(sid) = self.by_node.get(&to).copied() else {
            return;
        };
        let Some(rs) = self.streams.get_mut(&sid) else { return };
        let mut out = vec![0u8; MAX_FRAME_LEN + 64];
        let Ok(n) = rs.carrier.seal_bytes(&self.host.prov, plain, &mut out) else {
            return;
        };
        out.truncate(n);
        let data = wrap(rs, &out);
        self.out.ops.push_back((
            StreamOp::Write {
                stream: sid,
                len: data.len(),
                send_at: None,
            },
            data,
        ));
    }

    fn flush_handshake(&mut self, sid: StreamId) {
        let Some(rs) = self.streams.get_mut(&sid) else { return };
        let mut buf = vec![0u8; 32 * 1024];
        loop {
            let n = rs.carrier.transmit(&mut buf);
            if n == 0 {
                break;
            }
            let data = wrap(rs, &buf[..n]);
            self.out.ops.push_back((
                StreamOp::Write {
                    stream: sid,
                    len: data.len(),
                    send_at: None,
                },
                data,
            ));
        }
    }

    /// Read what the carrier of `sid` has buffered.
    fn drain(&mut self, now: Time, sid: StreamId) {
        for _ in 0..1024 {
            let mut sink = Collect::default();
            let step = {
                let Some(rs) = self.streams.get_mut(&sid) else { return };
                let prov = self.host.prov;
                let mut env = Env {
                    provider: &prov,
                    now,
                    drbg: &mut self.host.drbg,
                };
                match rs.carrier.poll(&mut env, &mut self.stores) {
                    Ok(Poll::Idle) => Step::Idle,
                    Ok(Poll::Handshake) => Step::Flush,
                    Ok(Poll::KeyRequest) => {
                        let soft = SoftKeys {
                            signer: Some((KeyHandle(1), &self.host.kp)),
                            prekeys: None,
                        };
                        let ok = rs.carrier.answer_soft(&mut env, &soft).is_ok();
                        if ok { Step::Flush } else { Step::Dead }
                    }
                    Ok(Poll::Open(peer)) => Step::Open(peer),
                    Ok(Poll::Frame(f)) => {
                        if let (Some(node), Some(sess)) = (rs.node, rs.session) {
                            let _ = self.relay.carrier_frame(now, &node, sess, &f, &mut sink);
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
                    if let Ok(sess) = self.relay.carrier_opened(now, peer, &mut s) {
                        if let Some(rs) = self.streams.get_mut(&sid) {
                            rs.node = Some(peer);
                            rs.session = Some(sess);
                        }
                        if let Some(old) = self.by_node.insert(peer, sid)
                            && old != sid
                        {
                            self.streams.remove(&old);
                            self.out.ops.push_back((StreamOp::Close { stream: old }, Vec::new()));
                        }
                        self.carriers_opened.push((now, peer));
                    }
                    self.apply(now, s);
                }
                Step::Dead => {
                    self.out.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
                    self.drop_stream(now, sid);
                    return;
                }
            }
        }
    }

    fn drop_stream(&mut self, now: Time, sid: StreamId) {
        if let Some(rs) = self.streams.remove(&sid)
            && let (Some(node), Some(sess)) = (rs.node, rs.session)
        {
            if self.by_node.get(&node) == Some(&sid) {
                self.by_node.remove(&node);
            }
            let mut s = Collect::default();
            self.relay.carrier_closed(now, &node, sess, &mut s);
            self.apply(now, s);
        }
    }

    // ---- the simulator's node contract ----

    pub fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        if data.first().is_some_and(|b| *b < 0x40) {
            let member = self.member_at(&remote);
            let mut s = Collect::default();
            let _ = self.relay.datagram(now, remote, member.as_ref(), data, &mut s);
            self.apply(now, s);
        } else {
            if let Some(n) = self.member_at(&remote) {
                let _ = self.relay.udp_heard(&n, now);
            }
            self.host.ep.handle_datagram(now, local, remote, data);
        }
        self.pump(now);
    }

    pub fn poll_transmit(&mut self, buf: &mut [u8]) -> Option<vinc_sim::Transmit> {
        let (local, remote, d) = self.out.datagrams.pop_front()?;
        buf[..d.len()].copy_from_slice(&d);
        Some(vinc_sim::Transmit {
            local,
            remote,
            len: d.len(),
            send_at: None,
        })
    }

    pub fn poll_timeout(&self) -> Option<Time> {
        [self.host.ep.poll_timeout(), self.relay.next_deadline()]
            .into_iter()
            .flatten()
            .min()
    }

    pub fn handle_timeout(&mut self, now: Time) {
        self.host.ep.handle_timeout(now);
        if self.relay.next_deadline().is_some_and(|d| d <= now) {
            let mut s = Collect::default();
            self.relay.handle_timeout(now, &mut s);
            self.apply(now, s);
        }
        self.pump(now);
    }

    pub fn poll_stream(&mut self, buf: &mut [u8]) -> Option<StreamOp> {
        let (op, data) = self.out.ops.pop_front()?;
        buf[..data.len()].copy_from_slice(&data);
        Some(op)
    }

    pub fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        self.events.push_back(Ev::Stream(event));
        match event {
            StreamEvent::Opened { stream, .. } => {
                self.scid += 1;
                let scid = ConnId::new(&self.scid.to_be_bytes()).unwrap();
                let cfg = session::responder_config(self.host.identity, scid).unwrap();
                self.streams.insert(
                    stream,
                    RStream {
                        carrier: Box::new(ProtectedCarrier::accept(cfg)),
                        node: None,
                        session: None,
                        ws: None,
                        sniffed: false,
                    },
                );
            }
            StreamEvent::Closed { stream } | StreamEvent::Failed { stream } => self.drop_stream(now, stream),
            StreamEvent::Pending { .. } => {}
        }
        self.pump(now);
    }

    pub fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        self.records += 1;
        let Some(rs) = self.streams.get_mut(&stream) else {
            return;
        };
        if !rs.sniffed {
            rs.sniffed = true;
            // A WebSocket frame starts 0x82 (final binary); a handshake unit starts with a length below 0x8000.
            if data.first() == Some(&0x82) {
                rs.ws = Some(Decoder::new(WsRole::Client));
                self.carriers_ws += 1;
            }
        }
        let mut payloads: Vec<Vec<u8>> = Vec::new();
        if let Some(dec) = rs.ws.as_mut() {
            let mut rest: &mut [u8] = data;
            while let Ok(Some((frame, used))) = dec.decode(rest) {
                if let WsFrame::Data(p) = frame {
                    payloads.push(p.to_vec());
                }
                let (_, tail) = std::mem::take(&mut rest).split_at_mut(used);
                rest = tail;
            }
        } else {
            payloads.push(data.to_vec());
        }
        for p in payloads {
            let mut rest: &[u8] = &p;
            for _ in 0..64 {
                let Some(rs) = self.streams.get_mut(&stream) else {
                    return;
                };
                let n = rs.carrier.receive(rest);
                rest = &rest[n..];
                self.drain(now, stream);
                if rest.is_empty() || n == 0 {
                    break;
                }
            }
        }
        self.pump(now);
    }

    pub fn session_stats(&self, s: SessionId) -> Option<vinc_core::SessionStats> {
        match self.host.ep.query(Query::Stats(s)) {
            vinc_core::Answer::Stats(st) => Some(st),
            _ => None,
        }
    }

    pub fn open_carrier(&self, node: &NodeId) -> bool {
        self.by_node.contains_key(node)
    }
}

enum Step {
    Idle,
    Flush,
    Frame,
    Open(NodeId),
    Dead,
}

fn wrap(rs: &RStream, bytes: &[u8]) -> Vec<u8> {
    if rs.ws.is_some() {
        let mut f = vec![0u8; bytes.len() + 16];
        let n = ws::encode(Opcode::Binary, bytes, None, &mut f).unwrap();
        f.truncate(n);
        f
    } else {
        bytes.to_vec()
    }
}
