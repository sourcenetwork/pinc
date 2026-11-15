//! The operations the handles run against the core: dials, accepts, streams, datagrams, sessions and the shutdown.
//!
//! Each returns [`Try::Done`] with its result or [`Try::Wait`] naming what it waits for; the facade future repeats it
//! when that changes, so every operation here is safe to repeat.

use std::collections::VecDeque;
use std::net::SocketAddr;
use std::rc::Rc;

use vinc_core::{Answer, Command, CommandError, IfaceEvent, NodeStats, Query, Role, SessionId, SessionStats, Value};
use vinc_crypto::NodeId;
use vinc_keystore::KeyStore;
use vinc_node::Ep as _;
use vinc_security::Alpn;
use vinc_transport::stream::{RecvStatus, StreamError, StreamId};

use super::gate::direction;
use super::{Admit, Core, Dial, GKey, Gate, Route, SHUTDOWN_GRACE, SKey, SessInfo, TRACKED, Try, Wait};
use crate::error::{Error, ErrorKind, Result};

impl<S: KeyStore, A: Admit> Core<S, A> {
    /// Whether the endpoint still takes new work, else why not.
    pub(crate) fn running(&self) -> Result<()> {
        if let Some(e) = self.stopped {
            return Err(e);
        }
        if self.shutdown.is_some() {
            return Err(Error::shutdown());
        }
        Ok(())
    }

    /// Start a dial to `node` for `alpn`; the answer comes through [`dial_poll`](Self::dial_poll).
    pub(crate) fn connect_start(
        &mut self,
        now: u64,
        node: NodeId,
        alpn: &[u8],
        addrs: &[SocketAddr],
    ) -> Result<SessionId> {
        self.running()?;
        if self.admit.is_revoked(&node) {
            return Err(Error::new(ErrorKind::Refused, "the peer is revoked"));
        }
        if self.sessions.len() >= self.limits.connections {
            return Err(Error::new(ErrorKind::Busy, "the connection table is full"));
        }
        let mut all = addrs.to_vec();
        for a in self.book.get(&node).into_iter().flatten() {
            if !all.contains(a) {
                all.push(*a);
            }
        }
        let key = Alpn::new(alpn).ok_or_else(|| Error::config("the protocol name is empty or too long"))?;
        // The endpoint keeps one answer per peer. A refusal it holds was given for other questions, so it must not
        // fail a dial the hook allows: it is dropped, and the session of this dial asks with its own question.
        let refused = matches!(
            self.node.endpoint().query(Query::Access(node)),
            Answer::Access { allow: false, until } if now < until
        );
        if refused && self.admit.admit(&node, alpn, direction(alpn, true)) {
            self.forget_access(&node.bytes);
        }
        match self.node.dial(now, node, alpn, Role::Other, &all) {
            Ok(session) => {
                // The first flight is queued: the future that started the dial sends it.
                self.dirty = true;
                let deadline = now.saturating_add(self.connect_timeout);
                self.deadlines.insert(deadline);
                self.dials.insert(
                    session,
                    Dial {
                        node,
                        alpn: key,
                        result: None,
                        deadline,
                    },
                );
                Ok(session)
            }
            Err(e) => Err(Error::command(e)),
        }
    }

    /// The state of a dial: its session once up, or why not, else a wait.
    pub(crate) fn dial_poll(&mut self, session: SessionId) -> Try<Result<Rc<SessInfo>>> {
        match self.dials.get(&session).map(|d| d.result.is_some()) {
            Some(true) => match self.dials.remove(&session).and_then(|d| d.result) {
                Some(r) => Try::Done(r),
                None => Try::Done(Err(Error::shutdown())),
            },
            Some(false) => Try::Wait(Wait::G(GKey::Dial(session))),
            None => Try::Done(Err(self.stopped.unwrap_or_else(Error::shutdown))),
        }
    }

    /// Give up a dial whose future was dropped: a session that came up meanwhile is closed.
    pub(crate) fn dial_cancel(&mut self, now: u64, session: SessionId) {
        if let Some(d) = self.dials.remove(&session)
            && let Some(Ok(info)) = d.result
            && self.sessions.contains_key(&info.id)
        {
            let id = info.id;
            let _ = self.cmd(now, || Command::Close { session: id, error: 0 });
        }
    }

    /// The next session on accept queue `route`, or `None` once the endpoint stopped, else a wait.
    pub(crate) fn accept_route(&mut self, route: usize) -> Try<Option<Rc<SessInfo>>> {
        if let Some(i) = self.routes.get_mut(route).and_then(|r| r.queue.pop_front()) {
            self.sync_backlog();
            return Try::Done(Some(i));
        }
        if self.stopped.is_some() {
            return Try::Done(None);
        }
        Try::Wait(Wait::G(GKey::Route(route)))
    }

    /// Send sessions for `alpn` to a queue of their own; returns its index.
    pub(crate) fn listen(&mut self, alpn: &[u8]) -> Result<usize> {
        if self.routes.iter().any(|r| r.alpn == alpn) || self.alpns.len() >= crate::mem::MAX_PROTOCOLS {
            return Err(Error::config("the protocol is already registered or too many are"));
        }
        if !self.node.endpoint_mut().register_alpn(alpn) {
            return Err(Error::config("the protocol name is empty, too long or one too many"));
        }
        self.routes.push(Route {
            alpn: alpn.to_vec(),
            queue: VecDeque::new(),
        });
        self.alpns.push(alpn.to_vec());
        Ok(self.routes.len() - 1)
    }

    pub(crate) fn open(&mut self, now: u64, info: &SessInfo, bidi: bool) -> Try<Result<StreamId>> {
        if !self.sessions.contains_key(&info.id) {
            return Try::Done(Err(info.gone()));
        }
        let session = info.id;
        let key = SKey::Open(bidi);
        if self.open_ahead(session, key) {
            return Try::Wait(Wait::S(session, key));
        }
        match self.cmd(now, || Command::OpenStream { session, bidi }) {
            Ok(Value::Stream(id)) => Try::Done(Ok(id)),
            Ok(_) => Try::Done(Err(Error::new(ErrorKind::Busy, "the stream did not open"))),
            // No stream credit or no room for the stream's window yet: wait for the connection's open-ready event.
            Err(CommandError::Stream(StreamError::StreamLimit | StreamError::Exhausted)) => {
                Try::Wait(Wait::S(session, key))
            }
            Err(e) => Try::Done(Err(Error::command(e))),
        }
    }

    pub(crate) fn accept_stream(&mut self, info: &SessInfo, bidi: bool) -> Try<Result<StreamId>> {
        let Some(s) = self.sessions.get_mut(&info.id) else {
            return Try::Done(Err(info.gone()));
        };
        let q = if bidi { &mut s.accept_bi } else { &mut s.accept_uni };
        match q.pop_front() {
            Some(id) => Try::Done(Ok(id)),
            None => Try::Wait(Wait::S(info.id, if bidi { SKey::AcceptBi } else { SKey::AcceptUni })),
        }
    }

    pub(crate) fn write(&mut self, now: u64, info: &SessInfo, stream: StreamId, data: &[u8]) -> Try<Result<usize>> {
        if let Some(e) = self.send_failure(info.id, stream) {
            return Try::Done(Err(e));
        }
        if !self.sessions.contains_key(&info.id) {
            return Try::Done(Err(info.gone()));
        }
        let session = info.id;
        match self.cmd(now, || Command::Write { session, stream, data }) {
            Ok(Value::Written(0)) if !data.is_empty() => Try::Wait(Wait::S(session, SKey::Write(stream))),
            Ok(Value::Written(n)) => Try::Done(Ok(n)),
            Ok(_) => Try::Done(Ok(0)),
            Err(CommandError::Stream(StreamError::Exhausted)) => Try::Wait(Wait::S(session, SKey::Write(stream))),
            Err(e) => Try::Done(Err(Error::command(e))),
        }
    }

    pub(crate) fn finish(&mut self, now: u64, info: &SessInfo, stream: StreamId) -> Result<()> {
        if let Some(e) = self.send_failure(info.id, stream) {
            return Err(e);
        }
        if !self.sessions.contains_key(&info.id) {
            return Err(info.gone());
        }
        let session = info.id;
        self.cmd(now, || Command::Finish { session, stream })
            .map(|_| ())
            .map_err(Error::command)
    }

    /// Make `body` the whole content of a stream nothing was written to: the endpoint sends from it and ends the
    /// stream after its last byte.
    pub(crate) fn send_body(&mut self, now: u64, info: &SessInfo, stream: StreamId, body: &crate::Body) -> Result<()> {
        if let Some(e) = self.send_failure(info.id, stream) {
            return Err(e);
        }
        if !self.sessions.contains_key(&info.id) {
            return Err(info.gone());
        }
        let session = info.id;
        self.cmd(now, || Command::WriteSource {
            session,
            stream,
            source: body.clone(),
            len: body.len() as u64,
        })
        .map(|_| ())
        .map_err(Error::command)
    }

    /// Abandon the send side of a stream, for `code`.
    /// Set how urgent `stream` is among the streams of its session: lower numbers are sent first.
    pub(crate) fn set_urgency(&mut self, now: u64, info: &SessInfo, stream: StreamId, urgency: u8) -> Result<()> {
        if !self.sessions.contains_key(&info.id) {
            return Err(info.gone());
        }
        let session = info.id;
        self.cmd(now, || Command::SetUrgency {
            session,
            stream,
            urgency,
        })
        .map(|_| ())
        .map_err(Error::command)
    }

    pub(crate) fn reset(&mut self, now: u64, info: &SessInfo, stream: StreamId, code: u64) {
        let session = info.id;
        let _ = self.cmd(now, || Command::Reset {
            session,
            stream,
            error: code,
        });
        self.send_failed(
            session,
            stream,
            Error::new(ErrorKind::Stopped(code), "the stream was reset"),
        );
        self.wake_s(session, SKey::Write(stream));
    }

    /// The send half of a stream is dropped: end it after the bytes written, and forget its failure.
    pub(crate) fn drop_send(&mut self, now: u64, info: &SessInfo, stream: StreamId, finished: bool) {
        let session = info.id;
        if !finished && self.send_failure(session, stream).is_none() {
            let _ = self.cmd(now, || Command::Finish { session, stream });
        }
        if let Some(s) = self.sessions.get_mut(&session) {
            s.send_fail.retain(|(i, _)| *i != stream);
        }
    }

    /// Read what a stream has into `buf`: how many bytes, and how the stream ended if this read saw its end.
    pub(crate) fn read(
        &mut self,
        now: u64,
        info: &SessInfo,
        stream: StreamId,
        buf: &mut [u8],
    ) -> Try<Result<(usize, Option<Result<()>>)>> {
        if !self.sessions.contains_key(&info.id) {
            return Try::Done(Err(info.gone()));
        }
        if buf.is_empty() {
            return Try::Done(Ok((0, None)));
        }
        self.read_with(now, info, stream, |c| {
            let n = c.len().min(buf.len());
            if let (Some(d), Some(s)) = (buf.get_mut(..n), c.get(..n)) {
                d.copy_from_slice(s);
            }
            n
        })
    }

    /// Lend what a stream has next to `take`, which says how many of the bytes it used: that many are consumed.
    /// Answers as [`read`](Self::read). `take` is not called while the stream has nothing.
    pub(crate) fn read_with(
        &mut self,
        now: u64,
        info: &SessInfo,
        stream: StreamId,
        mut take: impl FnMut(&[u8]) -> usize,
    ) -> Try<Result<(usize, Option<Result<()>>)>> {
        if !self.sessions.contains_key(&info.id) {
            return Try::Done(Err(info.gone()));
        }
        let session = info.id;
        let (n, offered) = match self.node.endpoint().query(Query::Read { session, stream }) {
            Answer::Chunk(c) if !c.is_empty() => (take(c).min(c.len()), true),
            _ => (0, false),
        };
        let status = match self.cmd(now, || Command::Consume { session, stream, n }) {
            Ok(Value::Recv(st)) => st,
            Ok(_) => RecvStatus::Open,
            Err(e) => return Try::Done(Err(Error::command(e))),
        };
        let end = match status {
            RecvStatus::Open => None,
            RecvStatus::Finished => Some(Ok(())),
            RecvStatus::Reset(e) => Some(Err(Error::new(ErrorKind::Reset(e), "the peer reset the stream"))),
        };
        if n > 0 {
            self.wake_open(session);
            Try::Done(Ok((n, end)))
        } else if end.is_some() || offered {
            // The end, or bytes the taker left where they are: waiting would be for nothing.
            Try::Done(Ok((0, end)))
        } else {
            Try::Wait(Wait::S(session, SKey::Read(stream)))
        }
    }

    /// Stop reading a stream: tell the peer, and throw away what still arrives.
    pub(crate) fn stop_recv(&mut self, now: u64, info: &SessInfo, stream: StreamId, code: u64) {
        let session = info.id;
        let _ = self.cmd(now, || Command::StopSending {
            session,
            stream,
            error: code,
        });
        self.drop_recv(now, info, stream);
    }

    /// The receive half of a stream is dropped before its end: throw away what arrives until the stream ends.
    pub(crate) fn drop_recv(&mut self, now: u64, info: &SessInfo, stream: StreamId) {
        if let Some(s) = self.sessions.get_mut(&info.id)
            && s.discard.len() < TRACKED
            && !s.discard.contains(&stream)
        {
            s.discard.push(stream);
        }
        self.discard_if_dropped(now, info.id, stream);
    }

    pub(crate) fn send_datagram(&mut self, now: u64, info: &SessInfo, data: &[u8]) -> Result<()> {
        if !self.sessions.contains_key(&info.id) {
            return Err(info.gone());
        }
        let session = info.id;
        self.cmd(now, || Command::SendDatagram { session, data })
            .map(|_| ())
            .map_err(Error::command)
    }

    pub(crate) fn read_datagram(&mut self, info: &SessInfo, out: &mut [u8]) -> Try<Result<usize>> {
        if !self.sessions.contains_key(&info.id) {
            return Try::Done(Err(info.gone()));
        }
        match self.node.endpoint_mut().read_datagram(info.id, out) {
            Ok(Some(n)) => Try::Done(Ok(n)),
            Ok(None) => Try::Wait(Wait::S(info.id, SKey::Datagram)),
            Err(e) => Try::Done(Err(Error::command(e))),
        }
    }

    pub(crate) fn stats(&self, info: &SessInfo) -> Result<SessionStats> {
        match self.node.endpoint().query(Query::Stats(info.id)) {
            Answer::Stats(s) if self.sessions.contains_key(&info.id) => Ok(s),
            _ => Err(info.gone()),
        }
    }

    pub(crate) fn close_session(&mut self, now: u64, session: SessionId, code: u64) {
        if self.sessions.contains_key(&session) {
            let _ = self.cmd(now, || Command::Close { session, error: code });
        }
    }

    /// Whether the peer was heard on the session, the reason the session ended first, else a wait.
    pub(crate) fn answered(&self, info: &SessInfo) -> Try<Result<()>> {
        if info.answered.get() {
            Try::Done(Ok(()))
        } else if self.sessions.contains_key(&info.id) {
            Try::Wait(Wait::S(info.id, SKey::Answered))
        } else {
            Try::Done(Err(info.gone()))
        }
    }

    /// Whether the session is gone (its reason), else a wait.
    pub(crate) fn closed(&self, info: &SessInfo) -> Try<Error> {
        if self.sessions.contains_key(&info.id) {
            Try::Wait(Wait::S(info.id, SKey::Closed))
        } else {
            Try::Done(info.gone())
        }
    }

    /// The access hook, for the handles to ask without the core.
    pub(crate) fn hook(&self) -> Rc<Gate<A>> {
        Rc::clone(&self.admit)
    }

    pub(crate) fn peers(&self) -> Vec<NodeId> {
        let mut v: Vec<NodeId> = self.sessions.values().map(|s| s.info.node).collect();
        v.sort_by_key(|n| n.bytes);
        v.dedup();
        v
    }

    pub(crate) fn close_peer(&mut self, now: u64, node: &NodeId) {
        self.close_sessions(now, node, 0);
    }

    fn close_sessions(&mut self, now: u64, node: &NodeId, error: u64) {
        let all: Vec<SessionId> = self
            .sessions
            .iter()
            .filter(|(_, r)| r.info.node == *node)
            .map(|(s, _)| *s)
            .collect();
        for session in all {
            let _ = self.cmd(now, || Command::Close { session, error });
        }
    }

    /// Bar `node` and end every session with it, with the code [`DENIED`].
    pub(crate) fn revoke(&mut self, now: u64, node: &NodeId) -> Result<()> {
        if !self.admit.bar(node) {
            return Err(Error::new(ErrorKind::Busy, "too many peers are revoked"));
        }
        self.known.forget(&node.bytes);
        self.node
            .revoke(now, &node.bytes)
            .map_err(|_| Error::new(ErrorKind::Busy, "too many peers are revoked"))?;
        self.dirty = true;
        Ok(())
    }

    pub(crate) fn unrevoke(&mut self, node: &[u8; 32]) {
        self.known.forget(node);
        self.node.unrevoke(node);
    }

    /// Drop the endpoint's cached access answer for `node`: its next session asks the gate again.
    pub(crate) fn forget_access(&mut self, node: &[u8; 32]) {
        self.known.forget(node);
        self.node.forget_access(node);
    }

    /// Remember an address of `node`; false if the book is full of other nodes or the node has eight already.
    pub(crate) fn add_address(&mut self, node: NodeId, addr: SocketAddr) -> bool {
        if !self.book.contains_key(&node) && self.book.len() >= super::state::BOOK_MAX {
            return false;
        }
        let v = self.book.entry(node).or_default();
        if v.contains(&addr) {
            return true;
        }
        if v.len() >= super::state::ADDRS_MAX {
            return false;
        }
        v.push(addr);
        true
    }

    pub(crate) fn network_change(&mut self, now: u64) {
        for id in self.ifaces.clone() {
            self.node.endpoint_mut().iface_event(now, id, IfaceEvent::Down);
            self.node.endpoint_mut().iface_event(now, id, IfaceEvent::Up);
        }
        self.node.address_changed(now);
        self.dirty = true;
    }

    pub(crate) fn suspend(&mut self, now: u64, wall_ms: u64) {
        self.node.suspend(now, wall_ms);
        self.dirty = true;
    }

    pub(crate) fn resume(&mut self, now: u64, moved: bool) {
        self.node.resume(now, moved);
        self.dirty = true;
    }

    /// The relay the node is homed on now.
    pub(crate) fn home_relay(&self) -> Option<NodeId> {
        let c = self.node.connectivity();
        c.home().and_then(|h| c.relay_cfg(h)).map(|r| r.id)
    }

    pub(crate) fn node_stats(&self) -> NodeStats {
        self.node.endpoint().node_stats()
    }

    pub(crate) fn seal(&mut self, plain: &[u8]) -> Result<Vec<u8>> {
        self.with_identity(|i| i.seal(plain))
    }

    pub(crate) fn unseal(&mut self, sealed: &[u8]) -> Result<Vec<u8>> {
        self.with_identity(|i| i.unseal(sealed))
    }

    pub(crate) fn sign(&mut self, data: &[u8]) -> Result<Vec<u8>> {
        if let Some(e) = self.stopped {
            return Err(e);
        }
        self.with_identity(|i| i.sign(data))
    }

    /// Begin the shutdown: every session closes, and the endpoint stops when they are gone or the grace ran out.
    pub(crate) fn begin_shutdown(&mut self, now: u64) {
        if self.shutdown.is_none() && self.stopped.is_none() {
            self.shutdown = Some(now.saturating_add(SHUTDOWN_GRACE));
            self.node.leave(now);
            self.node.stop_port_mapping(now);
            self.dirty = true;
        }
    }

    pub(super) fn check_finished(&mut self, now: u64) {
        let Some(at) = self.shutdown else { return };
        // A UPnP mapping is deleted over HTTP: the driving future carries it while the grace runs.
        if (self.node.endpoint().node_stats().sessions > 0 || !self.node.port_mapping_done()) && now < at {
            return;
        }
        self.stop(Error::shutdown());
    }

    /// Whether the endpoint stopped, else a wait for the shutdown.
    pub(crate) fn shutdown_poll(&self) -> Try<()> {
        if self.stopped.is_some() {
            Try::Done(())
        } else {
            Try::Wait(Wait::G(GKey::Shutdown))
        }
    }

    /// Whether the endpoint stopped, else a wait that only a stop ends.
    pub(crate) fn idle_poll(&self) -> Try<()> {
        if self.stopped.is_some() {
            Try::Done(())
        } else {
            Try::Wait(Wait::G(GKey::Idle))
        }
    }

    // ---- relays and their carriers ----

    /// The next request of the connectivity layer for a carrier.
    pub(crate) fn carrier_io(&mut self) -> Option<vinc_connect::client::Io> {
        self.node.poll_io()
    }

    /// The carrier of `relay` is open.
    pub(crate) fn carrier_opened(&mut self, now: u64, relay: usize) {
        self.node.stream_opened(now, relay);
        self.dirty = true;
    }

    /// The carrier of `relay` closed or could not be opened.
    pub(crate) fn carrier_closed(&mut self, now: u64, relay: usize) {
        self.node.stream_closed(now, relay);
        self.dirty = true;
    }

    /// Bytes arrived on the carrier of `relay`; how many the node took.
    pub(crate) fn carrier_in(&mut self, now: u64, relay: usize, bytes: &[u8]) -> usize {
        self.dirty = true;
        self.node.stream_data(now, relay, bytes)
    }

    /// The next bytes the node wants on the carrier of `relay`.
    pub(crate) fn carrier_out(&mut self, relay: usize, buf: &mut [u8]) -> usize {
        self.node.poll_stream(relay, buf)
    }

    /// The next UDP datagram the connectivity layer wants sent: its address and length in `buf`.
    pub(crate) fn poll_udp(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        self.node.poll_udp(buf)
    }

    /// Random bytes from the identity's source; zeros if it fails (a mask or a nonce nothing depends on).
    pub(crate) fn random(&mut self, out: &mut [u8]) {
        let _ = self.with_identity(|i| i.random(out));
    }

    /// Wake the future that drives, if there is one.
    pub(crate) fn wake_driver(&mut self) {
        if let Some(t) = self.driver {
            self.standby.notify(t);
        }
    }

    // ---- records and lookups ----

    /// Give up the dials whose deadline passed: they fail with a timeout and their session is closed.
    pub(super) fn expire_dials(&mut self, now: u64) {
        let due: Vec<SessionId> = self
            .dials
            .iter()
            .filter(|(_, d)| d.result.is_none() && d.deadline <= now)
            .map(|(s, _)| *s)
            .collect();
        for session in due {
            self.fail_dial(
                now,
                session,
                Error::new(ErrorKind::TimedOut, "the peer did not answer in time"),
            );
        }
    }

    /// End the dial of `session` with `err` and close its session.
    fn fail_dial(&mut self, now: u64, session: SessionId, err: Error) {
        self.dial_done(session, Err(err));
        let _ = self.cmd(now, || Command::Close { session, error: 0 });
    }

    /// The addresses this node can be reached at besides the one it is bound to: those the relays reported.
    pub(crate) fn candidates(&self) -> Vec<SocketAddr> {
        let any = SocketAddr::new(std::net::Ipv4Addr::UNSPECIFIED.into(), 0);
        let mut c = [any; vinc_connect::record::MAX_ADDRS];
        let n = self.node.connectivity().candidates(&mut c);
        c.get(..n).unwrap_or_default().to_vec()
    }

    /// Put `hints` in the record the relays hold for this node.
    pub(crate) fn set_hints(&mut self, now: u64, hints: &[u8]) {
        if self.node.set_hints(now, hints) {
            self.dirty = true;
            self.wake_driver();
        }
    }

    /// Ask the relays for the record of `peer`.
    pub(crate) fn lookup_start(&mut self, now: u64, peer: &NodeId) {
        self.node.lookup(now, peer);
        self.dirty = true;
    }

    /// A notice of the connectivity layer: an answer to a lookup wakes the futures that wait for one. A dial to a peer
    /// no relay knows yet is not ended by the answer, since the peer may publish a moment later: its deadline ends it.
    pub(super) fn on_notice(&mut self, n: &vinc_connect::client::Notice) {
        use vinc_connect::client::Notice;
        match n {
            Notice::Found(_) => {}
            Notice::Missing(p) | Notice::BadRecord(p) => {
                if self.lookup_failed.len() >= 16 {
                    self.lookup_failed.pop_front();
                }
                self.lookup_failed.push_back(*p);
            }
            _ => return,
        }
        self.wake_g(GKey::Lookup);
    }

    /// The verified record a relay found for `peer`, or that it has none, or a timeout at `deadline`, else a wait.
    pub(crate) fn lookup_poll(
        &mut self,
        peer: &NodeId,
        deadline: u64,
        now: u64,
    ) -> Try<Result<Option<crate::records::PeerRecord>>> {
        if let Some(f) = self.node.connectivity().found(peer) {
            return Try::Done(Ok(Some(crate::records::PeerRecord {
                node: *peer,
                seq: f.seq,
                addrs: f.addrs().collect(),
                hints: f.hints().to_vec(),
            })));
        }
        if let Some(at) = self.lookup_failed.iter().position(|p| p == peer) {
            self.lookup_failed.remove(at);
            return Try::Done(Ok(None));
        }
        if now >= deadline {
            return Try::Done(Err(Error::new(
                ErrorKind::TimedOut,
                "the relays did not answer in time",
            )));
        }
        self.deadlines.insert(deadline);
        Try::Wait(Wait::G(GKey::Lookup))
    }
}
