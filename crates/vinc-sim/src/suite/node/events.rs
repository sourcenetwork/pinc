//! What the node reports: endpoint events, membership and broadcast, turned into the layers' events and the recorder's
//! records, and the [`Host`] the layers act through.
//!
//! Invariants: a session the node closed on its own (a revoked or unknown peer) is hidden from the layers for its
//! whole life; a hub-protocol session never reaches the layers because no layer owns its protocol name; no borrow of
//! the recorder is held across a call into a layer; every access check is answered once, after the world's latency.

use vinc_core::{Answer, Command, Event, Query, Role, SessionId, Value};
use vinc_node::{NodeEvent as NEv, ValuesRequest};
use vinc_values::span::Span;
use vinc_transport::stream::RecvStatus;

use super::NodeEvent;
use super::core::{Check, Core, Known, LOCAL_BASE, Sess};
use crate::suite::crypto::MsgId;
use crate::suite::proto::host::{Host, LayerEvent, Layers};
use crate::suite::rec::MemberEvent;

const CLOSE_DENIED: u64 = 3;

impl Core {
    /// Handle every event the node and the last commands produced. Returns whether there was any.
    pub(super) fn service<L: Layers>(&mut self, layers: &mut L) -> bool {
        let mut any = self.hub_members();
        while let Some(ev) = self.node.as_mut().and_then(|n| n.poll_event()) {
            any = true;
            match ev {
                NEv::Endpoint(e) => self.on_event(layers, e),
                NEv::Member(m) => self.on_member(layers, &m),
                NEv::Message { origin, body, .. } => {
                    if self.deliver() {
                        let origin = self.shared.index_of_bytes(&origin);
                        let local = self.now;
                        layers.event(local, self, LayerEvent::Message { origin, body: &body });
                    }
                }
                NEv::BroadcastAcpCheck { id, origin, .. } => {
                    let principal = self.shared.index_of_bytes(&origin);
                    let (allow, _) = self.shared.rec.borrow_mut().acp_decide(self.now, self.idx, principal);
                    let due = self.now + self.shared.world.acp_latency_ns;
                    self.acp.push_back((due, Check::Broadcast(id), allow));
                }
                NEv::ValueReadable { fetch, off, len } => {
                    self.record_commits();
                    if self.deliver() {
                        let local = self.now;
                        layers.event(local, self, LayerEvent::ValueReadable { fetch, off, len });
                    }
                }
                NEv::ValueComplete { fetch } => {
                    self.record_commits();
                    if self.deliver() {
                        let local = self.now;
                        layers.event(local, self, LayerEvent::ValueComplete { fetch });
                    }
                }
                NEv::ValueFailed { fetch, .. } => {
                    self.record_commits();
                    if self.deliver() {
                        let local = self.now;
                        layers.event(local, self, LayerEvent::ValueFailed { fetch });
                    }
                }
                NEv::ReconcileDone {
                    round,
                    missing_here,
                    missing_there,
                    ..
                } => {
                    if self.deliver() {
                        let local = self.now;
                        let ev = LayerEvent::ReconcileDone {
                            round,
                            missing_here: &missing_here,
                            missing_there: &missing_there,
                        };
                        layers.event(local, self, ev);
                    }
                }
                NEv::ReconcileFailed { round, .. } => {
                    if self.deliver() {
                        let local = self.now;
                        layers.event(local, self, LayerEvent::ReconcileFailed { round });
                    }
                }
                NEv::Connect(n) => {
                    if self.notices.len() == 40 {
                        self.notices.pop_front();
                    }
                    self.notices.push_back(format!("t{} {n:?}", self.now));
                }
                NEv::PublishAcked { .. }
                | NEv::PublishGaveUp { .. }
                | NEv::GapRepaired { .. }
                | NEv::Fallback { .. }
                | NEv::Restored { .. }
                | NEv::Lost { .. }
                | NEv::DtnReceived { .. }
                | NEv::DtnCustody { .. }
                | NEv::DtnHandedOff { .. }
                | NEv::DtnDelivered { .. }
                | NEv::DtnExpired { .. } => {}
            }
            self.hub_members();
        }
        self.note_watched_trace();
        any
    }

    /// Keep the node's own decisions of a watched node as ndjson lines, with the node and the true time.
    fn note_watched_trace(&mut self) {
        if !self.shared.is_watched(self.idx) {
            return;
        }
        while let Some(item) = self.node.as_mut().and_then(|n| n.poll_trace()) {
            if matches!(item.body, vinc_node::Body::Node(_)) {
                let mut line = String::new();
                if item.write_ndjson(&mut line).is_ok() {
                    self.shared.note_trace(format!("n{} true{} {line}", self.idx, self.now));
                }
            } else if super::in_trace_window(self.now) {
                self.shared.note_trace(format!("n{} true{} {:?}", self.idx, self.now, item.body));
            }
        }
    }

    /// Tell the recorder what the node's value store gained since the last call, and flag bytes that are not the
    /// value's body.
    fn record_commits(&mut self) {
        let Some(store) = self.shared.values_of(self.idx) else { return };
        let commits = store.take_commits();
        let mut rec = self.shared.rec.borrow_mut();
        for c in commits {
            rec.value_bytes_written(self.now, self.idx, c.id.0, c.off, c.len, c.new);
        }
        drop(rec);
        if store.bad_writes() > 0 {
            self.violation("G-INT", "the node stored bytes that are not the value's body");
        }
    }

    fn on_member<L: Layers>(&mut self, layers: &mut L, m: &vinc_membership::Event) {
        use vinc_membership::Event as M;
        let ix = |s: &Self, id: &[u8; 32]| s.shared.index_of_bytes(id);
        let ev = match *m {
            M::MemberJoined { member } => MemberEvent::Joined(ix(self, &member)),
            M::MemberSuspected { member } => MemberEvent::Suspected(ix(self, &member)),
            M::MemberConfirmedDown { member } => MemberEvent::ConfirmedDown(ix(self, &member)),
            M::MemberLeft { member } => MemberEvent::Left(ix(self, &member)),
            M::MemberRevoked { member } => MemberEvent::Revoked(ix(self, &member)),
            M::AddressChanged { member } => MemberEvent::AddressChanged(ix(self, &member)),
            M::StackChanged { member, version } => MemberEvent::StackChanged {
                member: ix(self, &member),
                version: u64::from(version),
            },
            M::ViewChanged { epoch, .. } => MemberEvent::ViewChanged { epoch },
            M::Lost { .. } => return,
        };
        if self.deliver() {
            let local = self.now;
            layers.event(local, self, LayerEvent::Member(ev));
        }
    }

    fn known(&self, session: SessionId) -> Known {
        match self.sessions.get(&session) {
            Some(s) if s.hidden => Known::Hidden,
            Some(s) => Known::Visible(s.peer),
            None => Known::Unknown,
        }
    }

    fn visible(&mut self, session: SessionId, what: &str) -> Option<usize> {
        match self.known(session) {
            Known::Visible(p) => Some(p),
            Known::Hidden => None,
            Known::Unknown => {
                self.violation(
                    "G-SPEC",
                    &format!("the endpoint named a session the node never opened ({what})"),
                );
                None
            }
        }
    }

    fn on_event<L: Layers>(&mut self, layers: &mut L, ev: Event) {
        match ev {
            Event::KeyRequest { session } => self.answer_keys(session),
            Event::AcpCheck { check, node, .. } => {
                let principal = self.shared.index_of(&node);
                let (allow, _) = self.shared.rec.borrow_mut().acp_decide(self.now, self.idx, principal);
                self.acp.push_back((
                    self.now + self.shared.world.acp_latency_ns,
                    Check::Endpoint(check),
                    allow,
                ));
            }
            Event::Connected {
                session,
                node,
                alpn,
                resumed,
            } => self.on_open(layers, session, node, alpn, true, resumed),
            Event::Incoming { session, node, alpn } => self.on_open(layers, session, node, alpn, false, false),
            Event::ConnectFailed { node, alpn, reason } => {
                if let Some(peer) = self.shared.index_of(&node) {
                    self.events.push_back(NodeEvent::ConnectFailed {
                        peer,
                        reason: Some(reason),
                    });
                    if self.deliver() {
                        let (local, bytes) = (self.now, alpn.as_bytes());
                        layers.event(local, self, LayerEvent::ConnectFailed { peer, alpn: bytes });
                    }
                }
            }
            Event::Closed { session, .. } => match self.sessions.remove(&session) {
                Some(s) if !s.hidden => {
                    self.events.push_back(NodeEvent::Closed { peer: s.peer });
                    if self.deliver() {
                        let local = self.now;
                        layers.event(local, self, LayerEvent::Closed { session });
                    }
                }
                Some(_) => {}
                None => self.violation("G-SPEC", "the endpoint named a session the node never opened (closed)"),
            },
            Event::StreamOpened { session, stream } => {
                if self.visible(session, "stream opened").is_some() && self.deliver() {
                    let local = self.now;
                    layers.event(local, self, LayerEvent::StreamOpened { session, stream });
                }
            }
            Event::StreamReadable { session, stream } => {
                if self.visible(session, "stream readable").is_some() {
                    self.read_stream(layers, session, stream);
                }
            }
            Event::StreamWritable { session, stream } => {
                if self.visible(session, "stream writable").is_some() && self.deliver() {
                    let local = self.now;
                    layers.event(local, self, LayerEvent::StreamWritable { session, stream });
                }
            }
            Event::StreamReset { session, stream, .. } => {
                if self.visible(session, "stream reset").is_some() && self.deliver() {
                    let local = self.now;
                    layers.event(local, self, LayerEvent::StreamReset { session, stream });
                }
            }
            Event::DatagramReceived { .. }
            | Event::OpenReady { .. }
            | Event::PathChanged { .. }
            | Event::PeerAsleep { .. }
            | Event::PeerAwake { .. }
            | Event::ReachOut { .. }
            | Event::StreamStopped { .. }
            | Event::TicketsReceived { .. } => {}
        }
    }

    fn on_open<L: Layers>(
        &mut self,
        layers: &mut L,
        session: SessionId,
        node: vinc_crypto::NodeId,
        alpn: vinc_security::Alpn,
        dialed: bool,
        resumed: bool,
    ) {
        let peer = self.shared.index_of(&node);
        let hide = peer.is_none_or(|p| self.revoked.contains(&p));
        self.sessions.insert(
            session,
            Sess {
                peer: peer.unwrap_or(usize::MAX),
                hidden: hide,
            },
        );
        let Some(peer) = peer.filter(|_| !hide) else {
            let _ = self.cmd(Command::Close {
                session,
                error: CLOSE_DENIED,
            });
            if dialed && let Some(peer) = peer {
                self.events.push_back(NodeEvent::ConnectFailed { peer, reason: None });
                if self.deliver() {
                    let local = self.now;
                    layers.event(
                        local,
                        self,
                        LayerEvent::ConnectFailed {
                            peer,
                            alpn: alpn.as_bytes(),
                        },
                    );
                }
            }
            return;
        };
        let (local, bytes) = (self.now, alpn.as_bytes());
        if dialed {
            self.events.push_back(NodeEvent::Connected { peer, resumed });
            if self.deliver() {
                layers.event(
                    local,
                    self,
                    LayerEvent::Connected {
                        session,
                        peer,
                        alpn: bytes,
                    },
                );
            }
        } else {
            self.events.push_back(NodeEvent::Incoming { peer });
            if self.deliver() {
                layers.event(
                    local,
                    self,
                    LayerEvent::Incoming {
                        session,
                        peer,
                        alpn: bytes,
                    },
                );
            }
        }
    }

    /// Read everything readable on a stream, consume it, and hand it to the layers in one piece.
    fn read_stream<L: Layers>(&mut self, layers: &mut L, session: SessionId, stream: u64) {
        let mut buf = std::mem::take(&mut self.scratch);
        buf.clear();
        let mut fin = false;
        loop {
            let n = match self
                .node
                .as_ref()
                .map(|n| n.endpoint().query(Query::Read { session, stream }))
            {
                Some(Answer::Chunk(c)) if !c.is_empty() => {
                    buf.extend_from_slice(c);
                    c.len()
                }
                _ => break,
            };
            match self.cmd(Command::Consume { session, stream, n }) {
                Ok(v) => fin |= v == Value::Recv(RecvStatus::Finished),
                Err(_) => break,
            }
        }
        if !fin && let Ok(v) = self.cmd(Command::Consume { session, stream, n: 0 }) {
            fin = v == Value::Recv(RecvStatus::Finished);
        }
        if self.deliver() && (!buf.is_empty() || fin) {
            let local = self.now;
            layers.event(
                local,
                self,
                LayerEvent::StreamData {
                    session,
                    stream,
                    data: &buf,
                    fin,
                },
            );
        }
        self.scratch = buf;
    }

    /// Answer the key request of `session` with the node's software keys.
    fn answer_keys(&mut self, session: SessionId) {
        let keys = super::carrier::Keys {
            reg: self.shared.registry,
            idx: self.idx,
            prov: self.provider(),
            kp: &self.kp,
            prekeys: self.prekeys.as_ref(),
        };
        let Some(node) = self.node.as_mut() else { return };
        let Answer::KeyRequest(req) = node.endpoint().query(Query::KeyRequest(session)) else {
            return;
        };
        let owned = keys.answer(&mut self.drbg, self.local, &req);
        let _ = self.cmd(Command::KeyResponse {
            session,
            response: owned.response(),
        });
    }

    /// The oracle revoked `peer`: end its sessions now and refuse it from here on.
    pub(super) fn revoke(&mut self, peer: usize) {
        self.revoked.insert(peer);
        if let (Some(id), Some(node)) = (self.shared.node_id(peer), self.node.as_mut())
            && node.revoke(self.local, &id.bytes).is_err()
        {
            self.violation("G-SPEC", "the node could not record a revocation");
        }
        let open: Vec<SessionId> = self
            .sessions
            .iter()
            .filter(|(_, s)| s.peer == peer && !s.hidden)
            .map(|(id, _)| *id)
            .collect();
        for session in open {
            let _ = self.cmd(Command::Close {
                session,
                error: CLOSE_DENIED,
            });
        }
        self.events.push_back(NodeEvent::Revoked { peer });
    }
}

impl Host for Core {
    fn idx(&self) -> usize {
        self.idx
    }

    fn registry(&self) -> &'static crate::suite::crypto::Registry {
        self.shared.registry
    }

    fn connect(&mut self, peer: usize, alpn: &'static [u8]) -> bool {
        let shared = std::rc::Rc::clone(&self.shared);
        let Some(node) = shared.node_id(peer) else { return false };
        if peer == self.idx || self.revoked.contains(&peer) {
            return false;
        }
        // The application dials by node id alone: the connectivity layer finds the way.
        let hints: &[std::net::SocketAddr] = &[];
        let local = self.local;
        self.node
            .as_mut()
            .is_some_and(|n| n.dial(local, node, alpn, Role::Other, hints).is_ok())
    }

    fn open_stream(&mut self, session: SessionId) -> Option<vinc_transport::stream::StreamId> {
        match self.cmd(Command::OpenStream { session, bidi: true }).ok()? {
            Value::Stream(id) => Some(id),
            _ => None,
        }
    }

    fn write(&mut self, session: SessionId, stream: vinc_transport::stream::StreamId, data: &[u8]) -> usize {
        match self.cmd(Command::Write { session, stream, data }) {
            Ok(Value::Written(n)) => n,
            _ => 0,
        }
    }

    fn finish(&mut self, session: SessionId, stream: vinc_transport::stream::StreamId) {
        let _ = self.cmd(Command::Finish { session, stream });
    }

    fn reset(&mut self, session: SessionId, stream: vinc_transport::stream::StreamId, code: u64) {
        let _ = self.cmd(Command::Reset {
            session,
            stream,
            error: code,
        });
    }

    fn close(&mut self, session: SessionId, code: u64) {
        let _ = self.cmd(Command::Close { session, error: code });
    }

    fn peer_of(&self, session: SessionId) -> Option<usize> {
        self.sessions.get(&session).filter(|s| !s.hidden).map(|s| s.peer)
    }

    fn subscribe(&mut self, topic: &[u8]) -> bool {
        let local = self.local;
        self.node.as_mut().is_some_and(|n| n.subscribe(local, topic).is_ok())
    }

    fn fetch(&mut self, value: MsgId, ranges: &[(u64, u64)], providers: &[usize], deadline: u64) -> Option<u32> {
        let shared = std::rc::Rc::clone(&self.shared);
        let v = shared.catalog.get(value)?;
        let ids: Vec<[u8; 32]> = providers
            .iter()
            .filter(|&&p| p != self.idx)
            .filter_map(|&p| shared.node_id(p).map(|id| id.bytes))
            .collect();
        let spans: Vec<Span> = ranges.iter().map(|&(off, len)| Span { off, len }).collect();
        let deadline = u64::try_from(i128::from(self.clock.local(deadline)) + i128::from(LOCAL_BASE)).ok();
        let local = self.local;
        let req = ValuesRequest {
            root: v.root,
            length: v.len,
            ranges: &spans,
            providers: &ids,
            deadline,
        };
        self.node.as_mut()?.values_fetch(local, &req).ok()
    }

    fn reconcile(&mut self, peer: usize, set_ref: &[u8]) -> Option<u32> {
        let id = self.shared.node_id(peer)?.bytes;
        let local = self.local;
        self.node.as_mut()?.sets_start(local, &id, set_ref).ok()
    }

    fn publish(&mut self, topic: &[u8], msg: &[u8]) -> bool {
        let local = self.local;
        let ok = self.node.as_mut().is_some_and(|n| n.publish(local, topic, msg).is_ok());
        if !ok {
            self.violation("G-SPEC", "the node refused a publish");
        }
        ok
    }
}
