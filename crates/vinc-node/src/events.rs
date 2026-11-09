//! Endpoint events: which belong to the hub stream, and what the node does with each.
//!
//! The connectivity client sees every event first. Then the events of sessions that speak the hub protocol drive the
//! hub stream: a session coming up opens the write stream and tells membership; bytes become frames; a close tells
//! membership, backs the dial off and, at a hub, may adopt the member's older live session. Every other event is the
//! application's and passes through unchanged.
//!
//! Invariants: a hub-protocol session produces no stream event for the application (its lifecycle events pass); a frame is parsed only from bytes of a session
//! of its peer; a stream that breaks the framing is reset and forgotten, never guessed at.

use vinc_core::{Command, EndReason, Event, PathState, Role, SessionId};
use vinc_membership::NodeId;
use vinc_membership::session::LEAVE_CODE;
use vinc_transport::conn::CloseReason as TransportClose;
use vinc_transport::stream::StreamId;

use crate::config::{DENIED, Nanos, REDIAL_SOON, SESSION_LIVED, SURVIVOR, SURVIVOR_HAVE, Store, TABLE_MAX};
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::io::{Link, Sess};
use crate::node::Node;
use crate::trace::{NodeTrace, tag};

/// The close code a session ended with, 0 when it ended without one (or by our own close).
const fn close_code(r: EndReason) -> u64 {
    match r {
        EndReason::Transport(TransportClose::Peer { error } | TransportClose::Violation { error }) => error,
        _ => 0,
    }
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: vinc_crypto::Provider + Clone,
    St: Store,
    A: crate::apps::Apps<P>,
    E::Src: crate::apps::ServeSource<A::Values>,
{
    pub(crate) fn events_step(&mut self, now: Nanos) -> bool {
        let mut did = false;
        loop {
            let ev = if let Some(e) = self.conn.poll_event() {
                e
            } else if let Some(e) = self.io.evq.pop_front() {
                e
            } else if let Some(e) = self.io.ep.poll_event() {
                e
            } else {
                break;
            };
            did = true;
            self.on_event(now, ev);
        }
        did
    }

    fn on_event(&mut self, now: Nanos, ev: Event) {
        self.conn.observe(now, &mut self.io.ep, &ev);
        if let Some(layer) = self.event_layer(&ev) {
            self.on_layer_event(now, layer, ev);
            return;
        }
        let alpn = self.io.alpn;
        match ev {
            Event::Connected {
                session, node, alpn: a, ..
            } if a.as_bytes() == alpn => {
                self.hub_connected(now, session, &node);
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            Event::Incoming { session, node, alpn: a } if a.as_bytes() == alpn => {
                self.hub_incoming(now, session, &node);
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            Event::ConnectFailed { node, alpn: a, reason } if a.as_bytes() == alpn => {
                self.hub_connect_failed(&node.bytes, reason == vinc_core::ConnectFailure::Denied);
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            Event::Closed { session, reason } if self.io.sess.contains_key(&session) => {
                self.hub_closed(now, session, reason);
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            Event::StreamOpened { session, stream } if self.io.sess.contains_key(&session) => {
                self.hub_stream_opened(session, stream);
            }
            Event::StreamReadable { session, stream } if self.io.sess.contains_key(&session) => {
                self.hub_readable(now, session, stream);
            }
            Event::StreamWritable { session, stream } if self.io.sess.contains_key(&session) => {
                self.io.flush(session, stream);
            }
            Event::StreamReset { session, stream, .. } if self.io.sess.contains_key(&session) => {
                self.io.drop_strm(session, stream);
            }
            Event::AcpCheck { check, node, .. } if self.io.revoked.contains(&node.bytes) => {
                // A revoked peer is refused here; the application never hears of the check.
                let _ = self.io.cmd(Command::AcpAnswer { check, allow: false });
            }
            Event::PathChanged {
                session,
                state: PathState::Validated,
                ..
            } => {
                // The answer to a path probe is transport evidence that the peer is alive.
                if let Some(e) = self.io.rx_seen.get_mut(&session) {
                    e.1 = now;
                }
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            other => self.io.emit(NodeEvent::Endpoint(other)),
        }
    }

    // ---------------------------------------------------------------- sessions

    /// Make `session` the current session of `peer`.
    fn attach(&mut self, now: Nanos, session: SessionId, peer: NodeId, incoming: bool) {
        if self.io.sess.len() < TABLE_MAX {
            self.io.sess.insert(session, Sess { peer, incoming });
        }
        if self.io.links.len() < TABLE_MAX || self.io.links.contains_key(&peer) {
            self.io.links.insert(
                peer,
                Link {
                    conn: Some(session),
                    out: None,
                    fan: None,
                    opened: now,
                },
            );
        }
        self.io.trace(NodeTrace::SessionUp {
            peer: tag(&peer),
            incoming: u64::from(incoming),
        });
    }

    /// Our dial of `node` reached a session.
    fn hub_connected(&mut self, now: Nanos, session: SessionId, node: &vinc_crypto::NodeId) {
        let peer = node.bytes;
        self.io.learn_alg(node);
        self.io.connecting.remove(&peer);
        if let Some(cur) = self.io.links.get(&peer).and_then(|l| l.conn) {
            // The peer dialed us at the same time. Both ends keep the session the lower id dialed.
            if self.io.me < peer && self.io.sess.get(&cur).is_some_and(|s| s.incoming) {
                self.close_duplicate(now, cur, &peer);
            } else {
                self.close_duplicate(now, session, &peer);
                return;
            }
        }
        self.attach(now, session, peer, false);
        if let Some(s) = self.io.open_stream(session) {
            if let Some(l) = self.io.links.get_mut(&peer) {
                l.out = Some(s);
            }
            self.io.flush_queue(&peer, session, s);
        }
        let (m, mut h) = self.mem_host();
        m.session_up(&mut h, now, &peer, false);
    }

    /// A peer dialed us.
    fn hub_incoming(&mut self, now: Nanos, session: SessionId, node: &vinc_crypto::NodeId) {
        let peer = node.bytes;
        self.io.learn_alg(node);
        let role = if self.io.is_hub_id(&peer) {
            Role::Hub
        } else {
            Role::Member
        };
        let _ = self.io.cmd(Command::SetRole { session, role });
        if self.io.links.get(&peer).and_then(|l| l.conn) == Some(session) {
            return;
        }
        if let Some(l) = self.io.links.get(&peer).copied()
            && let Some(cur) = l.conn
        {
            if self.io.is_hub_id(&peer) && self.io.sess.get(&cur).is_some_and(|s| !s.incoming) {
                // Both hubs dialed at once. Both ends keep the session the lower id dialed.
                if self.io.me < peer {
                    self.close_duplicate(now, session, &peer);
                    return;
                }
                self.close_duplicate(now, cur, &peer);
            }
            // The newest session of a peer supersedes the old one (it restarted or rebound): what was queued for the
            // old write stream is dropped; the old session stays readable until it closes.
            self.forget_writers(&l);
        }
        self.io.connecting.remove(&peer);
        self.attach(now, session, peer, true);
        let (m, mut h) = self.mem_host();
        m.session_up(&mut h, now, &peer, true);
    }

    /// Close a session that duplicates the one in use. It is remembered as a hub-protocol session so its close is
    /// recognised, and it never becomes the peer's current session.
    fn close_duplicate(&mut self, _now: Nanos, session: SessionId, peer: &NodeId) {
        if self.io.sess.len() < TABLE_MAX && !self.io.sess.contains_key(&session) {
            self.io.sess.insert(
                session,
                Sess {
                    peer: *peer,
                    incoming: false,
                },
            );
        }
        let _ = self.io.cmd(Command::Close { session, error: 0 });
        self.io.trace(NodeTrace::DuplicateClosed { peer: tag(peer) });
    }

    /// Drop what a link's write streams still hold.
    fn forget_writers(&mut self, l: &Link) {
        let Some(conn) = l.conn else { return };
        for s in [l.out, l.fan].into_iter().flatten() {
            if let Some(st) = self.io.strm.get_mut(&(conn, s)) {
                st.outb.clear();
                st.off = 0;
            }
        }
    }

    fn hub_connect_failed(&mut self, peer: &NodeId, denied: bool) {
        self.io.connecting.remove(peer);
        self.io.drop_queue(peer);
        if denied {
            self.io.deny_back(peer);
        } else {
            self.io.backoff(peer);
        }
    }

    fn hub_closed(&mut self, now: Nanos, session: SessionId, reason: EndReason) {
        let Some(s) = self.io.sess.remove(&session) else {
            return;
        };
        self.io.drop_session_streams(session);
        self.io.rx_seen.remove(&session);
        let peer = s.peer;
        let code = close_code(reason);
        let Some(link) = self.io.links.get(&peer).copied().filter(|l| l.conn == Some(session)) else {
            return;
        };
        if self.io.is_hub
            && !self.io.is_hub_id(&peer)
            && code != LEAVE_CODE
            && let Some(alt) = self.survivor(now, &peer, session)
        {
            self.adopt(now, &peer, alt);
            return;
        }
        self.io.links.remove(&peer);
        self.io.trace(NodeTrace::SessionDown { peer: tag(&peer), code });
        let (m, mut h) = self.mem_host();
        m.session_down(&mut h, now, &peer, code);
        let hub = self.io.is_hub_id(&peer);
        if code == DENIED && hub && !self.io.is_hub {
            self.io.deny_back(&peer);
        } else if now.saturating_sub(link.opened) < SESSION_LIVED {
            self.io.backoff(&peer);
        } else {
            self.io.failed.remove(&peer);
        }
        if hub && !self.io.is_hub {
            self.next_duty = self.next_duty.min(now.saturating_add(REDIAL_SOON));
        }
    }

    /// The newest other session of `peer` that was heard within [`SURVIVOR`].
    fn survivor(&self, now: Nanos, peer: &NodeId, closed: SessionId) -> Option<SessionId> {
        self.io
            .sess
            .iter()
            .filter(|(sid, s)| s.peer == *peer && **sid != closed)
            .filter(|(sid, _)| {
                self.io
                    .ep
                    .stats(**sid)
                    .is_some_and(|st| now.saturating_sub(st.heard) < SURVIVOR)
            })
            .map(|(sid, _)| *sid)
            .next_back()
    }

    /// A hub makes `alt` the session of member `peer`: a fresh write stream, the view snapshot, and the ids of the
    /// recent log, since whatever went out on the closed session may be lost.
    pub(crate) fn adopt(&mut self, now: Nanos, peer: &NodeId, alt: SessionId) {
        let old = self.io.links.get(peer).copied();
        if let Some(l) = old {
            self.forget_writers(&l);
        }
        self.io.links.insert(
            *peer,
            Link {
                conn: Some(alt),
                out: None,
                fan: None,
                opened: old.map_or(now, |l| l.opened),
            },
        );
        if let Some(s) = self.io.open_stream(alt) {
            if let Some(l) = self.io.links.get_mut(peer) {
                l.out = Some(s);
            }
            self.io.flush_queue(peer, alt, s);
        }
        self.io.trace(NodeTrace::Adopted { peer: tag(peer) });
        let (m, mut h) = self.mem_host();
        m.snapshot_to(&mut h, now, peer);
        let (t, mut b) = self.bc_host();
        t.have_to(&mut b, now, peer, SURVIVOR_HAVE);
    }

    // ---------------------------------------------------------------- streams

    /// The peer opened a stream. If we have no write stream for it yet, answer on this one.
    fn hub_stream_opened(&mut self, session: SessionId, stream: StreamId) {
        let Some(peer) = self.io.sess.get(&session).map(|s| s.peer) else {
            return;
        };
        self.io.register_stream(session, stream);
        let Some(l) = self
            .io
            .links
            .get_mut(&peer)
            .filter(|l| l.conn == Some(session) && l.out.is_none())
        else {
            return;
        };
        l.out = Some(stream);
        self.io.flush_queue(&peer, session, stream);
    }

    /// Bytes arrived on a hub stream: collect them, parse the whole frames and hand them to membership.
    fn hub_readable(&mut self, now: Nanos, session: SessionId, stream: StreamId) {
        let Some(peer) = self.io.sess.get(&session).map(|s| s.peer) else {
            return;
        };
        self.io.register_stream(session, stream);
        // The hub follows the session a member writes on: answer on it.
        if self.io.is_hub && !self.io.is_hub_id(&peer) && self.io.links.get(&peer).and_then(|l| l.conn) != Some(session)
        {
            self.adopt(now, &peer, session);
        }
        let limit = self.io.max_frame.saturating_add(4);
        let mut broken = false;
        loop {
            let io = &mut self.io;
            let Some(chunk) = io.ep.read_chunk(session, stream).filter(|c| !c.is_empty()) else {
                break;
            };
            let n = chunk.len();
            let Some(st) = io.strm.get_mut(&(session, stream)) else {
                broken = true;
                break;
            };
            if st.inb.len().saturating_add(n) > limit.saturating_add(1 << 16) {
                broken = true;
                break;
            }
            st.inb.extend_from_slice(chunk);
            if io.cmd(Command::Consume { session, stream, n }).is_err() {
                break;
            }
        }
        if !broken {
            broken = !self.parse_stream(now, session, stream, &peer);
        }
        if broken {
            let _ = self.io.cmd(Command::Reset {
                session,
                stream,
                error: 1,
            });
            self.io.drop_strm(session, stream);
            self.io.trace(NodeTrace::StreamReset { peer: tag(&peer) });
        }
    }

    /// Hand the whole frames in the stream's buffer to membership. False if the framing broke.
    fn parse_stream(&mut self, now: Nanos, session: SessionId, stream: StreamId, peer: &NodeId) -> bool {
        let Some(mut buf) = self
            .io
            .strm
            .get_mut(&(session, stream))
            .map(|s| core::mem::take(&mut s.inb))
        else {
            return true;
        };
        let (m, mut h) = self.mem_host();
        let r = m.on_bytes(&mut h, now, peer, &buf);
        let ok = match r {
            Ok(used) => {
                buf.drain(..used);
                true
            }
            Err(_) => false,
        };
        if let Some(st) = self.io.strm.get_mut(&(session, stream)) {
            st.inb = buf;
        }
        ok
    }
}
