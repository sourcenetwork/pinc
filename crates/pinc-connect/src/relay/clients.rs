//! Carrier sessions keyed by node id, their byte and time limits, and the frames they send.
//!
//! The host reports each protected carrier whose handshake authenticated a node ([`Relay::carrier_opened`]) and each
//! decoded frame ([`Relay::carrier_frame`]). A node has at most one session; a newer one replaces the older, and
//! calls about the older one are ignored (the session id says which is current).
//!
//! Invariants:
//! - A session exists only for an authenticated node; its frames count against the node's byte window
//!   ([`super::Quota`]) and a frame over the window is dropped and traced, never queued.
//! - A session older than the quota's time limit is closed by the sweep.
//! - When a carrier closes the node becomes "gone" with the time; if its sleep notice came within
//!   [`super::rule::SLEEP_WIN_NS`] before, the close is a suspension, not a crash ([`NodeState::Gone`]).
//! - Aliases are per session and direction and reset with the session.

use pinc_crypto::NodeId;

use super::route::Pkt;
use super::{CloseReason, Effect, Reject, Relay, Route, Sink, Trace, route, rule};
use crate::carrier::alias::AliasTable;
use crate::carrier::frame::Frame;

/// Names one carrier session of a node; a newer session has a higher id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SessionId(pub u64);

#[derive(Debug)]
pub(crate) struct Client {
    pub(crate) id: SessionId,
    pub(crate) opened: u64,
    pub(crate) last_rx: u64,
    window_start: u64,
    window_bytes: u64,
    pub(crate) tx: AliasTable,
    rx: AliasTable,
}

/// What the relay knows about a node's carrier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeState {
    /// A carrier session is open.
    Open,
    /// The carrier closed at `since`; `asleep` says a sleep notice preceded the close.
    Gone {
        /// When the carrier closed.
        since: u64,
        /// Whether the close is a suspension.
        asleep: bool,
    },
    /// Nothing is known.
    Unknown,
}

impl<const C: usize, const R: usize, const MN: usize, const MB: usize> Relay<C, R, MN, MB> {
    /// What the relay knows about `node`'s carrier.
    pub fn node_state(&self, node: &NodeId) -> NodeState {
        if self.clients.contains(node) {
            return NodeState::Open;
        }
        match self.gone.get(node) {
            Some(&since) => NodeState::Gone {
                since,
                asleep: self
                    .sleeping
                    .get(node)
                    .is_some_and(|s| s.at >= since.saturating_sub(rule::SLEEP_WIN_NS)),
            },
            None => NodeState::Unknown,
        }
    }

    /// How many carrier sessions are open.
    pub const fn sessions(&self) -> usize {
        self.clients.len()
    }

    /// A carrier whose handshake authenticated `node` is open. Returns the session id to pass to later calls.
    /// Anything the mailbox holds for the node is delivered on the new carrier.
    ///
    /// # Errors
    /// [`Reject::SessionsFull`] if there is no room: the host closes the carrier.
    pub fn carrier_opened<S: Sink>(&mut self, now: u64, node: NodeId, sink: &mut S) -> Result<SessionId, Reject> {
        let id = SessionId(self.next_session);
        if let Some(old) = self.clients.get(&node).map(|c| c.id) {
            sink.emit(Effect::Close {
                node,
                session: old,
                reason: CloseReason::Replaced,
            });
        }
        let client = Client {
            id,
            opened: now,
            last_rx: now,
            window_start: now,
            window_bytes: 0,
            tx: AliasTable::new(),
            rx: AliasTable::new(),
        };
        if self.clients.insert(node, client).is_err() {
            return Err(self.reject(sink, Reject::SessionsFull, Some(node)));
        }
        self.next_session += 1;
        self.gone.remove(&node);
        self.sleeping.remove(&node);
        sink.emit(Effect::Trace(Trace::CarrierOpened { node, session: id }));
        self.deliver_held(now, &node, sink);
        Ok(id)
    }

    /// The carrier of `session` closed. Ignored if the node has a newer session.
    pub fn carrier_closed<S: Sink>(&mut self, now: u64, node: &NodeId, session: SessionId, sink: &mut S) {
        if self.clients.get(node).map(|c| c.id) != Some(session) {
            return;
        }
        self.clients.remove(node);
        let _ = self.gone.insert(*node, now);
        let asleep = matches!(self.node_state(node), NodeState::Gone { asleep: true, .. });
        sink.emit(Effect::Trace(Trace::CarrierClosed { node: *node, asleep }));
    }

    /// A frame arrived on the carrier of `session`, which authenticated `node`.
    ///
    /// # Errors
    /// The [`Reject`] reason; the input is dropped and traced, the session stays up.
    pub fn carrier_frame<S: Sink>(
        &mut self,
        now: u64,
        node: &NodeId,
        session: SessionId,
        frame: &Frame<'_>,
        sink: &mut S,
    ) -> Result<(), Reject> {
        match self.clients.get_mut(node) {
            Some(c) if c.id == session => c.last_rx = now,
            _ => return Err(self.reject(sink, Reject::StaleSession, Some(*node))),
        }
        if let Frame::Batch(batch) = frame {
            let mut first = Ok(());
            for sub in batch.frames() {
                let r = self.client_frame(now, node, &sub, sink);
                first = first.and(r);
            }
            return first;
        }
        self.client_frame(now, node, frame, sink)
    }

    fn charge<S: Sink>(&mut self, now: u64, node: &NodeId, bytes: usize, sink: &mut S) -> Result<(), Reject> {
        let quota = self.cfg.quota;
        let Some(c) = self.clients.get_mut(node) else {
            return Err(Reject::StaleSession);
        };
        if now.saturating_sub(c.window_start) >= quota.window_ns {
            c.window_start = now;
            c.window_bytes = 0;
        }
        let next = c.window_bytes.saturating_add(bytes as u64);
        if next > quota.bytes {
            self.stats.quota_drops += 1;
            sink.emit(Effect::Trace(Trace::QuotaExceeded { node: *node }));
            return Err(Reject::Quota);
        }
        c.window_bytes = next;
        Ok(())
    }

    fn client_frame<S: Sink>(
        &mut self,
        now: u64,
        node: &NodeId,
        frame: &Frame<'_>,
        sink: &mut S,
    ) -> Result<(), Reject> {
        let weight = frame.packet().map_or(0, <[u8]>::len)
            + match frame {
                Frame::Publish { record } | Frame::Sleep { notice: record } => record.len(),
                _ => 0,
            };
        if weight > 0 {
            self.charge(now, node, weight, sink)?;
        }
        match *frame {
            Frame::Send { dst, flag, packet } => self.route_from_client(now, node, &dst, flag, packet, sink),
            Frame::SendNew {
                dst,
                alias,
                flag,
                packet,
            } => {
                if let Some(c) = self.clients.get_mut(node) {
                    c.rx.learn(alias, dst);
                }
                self.route_from_client(now, node, &dst, flag, packet, sink)
            }
            Frame::SendAlias { alias, flag, packet } => {
                let dst = self.clients.get(node).and_then(|c| c.rx.resolve(alias));
                match dst {
                    Some(dst) => self.route_from_client(now, node, &dst, flag, packet, sink),
                    None => Err(self.reject(sink, Reject::UnknownAlias, Some(*node))),
                }
            }
            Frame::SelfSend { packet } => {
                self.local(node, packet, sink);
                Ok(())
            }
            Frame::Publish { record } => self.publish(now, node, record, sink),
            Frame::Ping => {
                sink.emit(Effect::Trace(Trace::Pulse { node: *node }));
                sink.emit(Effect::Carrier {
                    to: *node,
                    frame: Frame::Pong,
                });
                Ok(())
            }
            Frame::Pong => Ok(()),
            Frame::DnsQuery { peer } => {
                let max = crate::carrier::frame::MAX_FRAME_LEN;
                let answer = self.answer(now, &peer, max, sink);
                sink.emit(Effect::Carrier {
                    to: *node,
                    frame: Frame::DnsReply { peer, answer },
                });
                Ok(())
            }
            Frame::Sleep { notice } => self.sleep_notice(now, notice, Some(node), sink),
            Frame::Recv { .. }
            | Frame::RecvNew { .. }
            | Frame::RecvAlias { .. }
            | Frame::SelfRecv { .. }
            | Frame::DnsReply { .. }
            | Frame::Forward { .. }
            | Frame::Sync { .. }
            | Frame::Batch(_) => Err(self.reject(sink, Reject::UnexpectedFrame, Some(*node))),
        }
    }

    fn route_from_client<S: Sink>(
        &mut self,
        now: u64,
        node: &NodeId,
        dst: &NodeId,
        flag: u8,
        packet: &[u8],
        sink: &mut S,
    ) -> Result<(), Reject> {
        let pkt = Pkt {
            src: node,
            dst,
            flag,
            packet,
        };
        self.route(now, &pkt, route::Origin::Client, sink)
    }

    pub(crate) fn local<S: Sink>(&mut self, from: &NodeId, packet: &[u8], sink: &mut S) {
        self.stats.local += 1;
        sink.emit(Effect::Trace(Trace::Routed {
            src: *from,
            dst: self.cfg.me,
            route: Route::Local,
            bytes: packet.len(),
        }));
        sink.emit(Effect::Local { from: *from, packet });
    }

    /// A frame arrived from `from`, the peer relay of an authenticated relay-to-relay session.
    ///
    /// # Errors
    /// [`Reject::Unauthenticated`] if `from` is not an authenticated peer relay, [`Reject::UnexpectedFrame`] for a
    /// frame relays do not exchange, or the reason a forward or replication was refused.
    pub fn peer_frame<S: Sink>(
        &mut self,
        now: u64,
        from: &NodeId,
        frame: &Frame<'_>,
        sink: &mut S,
    ) -> Result<(), Reject> {
        if !self.is_peer(from) {
            return Err(self.reject(sink, Reject::Unauthenticated, Some(*from)));
        }
        match *frame {
            Frame::Forward { src, dst, flag, packet } => {
                if !self.clients.contains(&src) {
                    self.fwd_back.put(src, super::FwdBack { relay: *from, at: now });
                    sink.emit(Effect::Trace(Trace::FwdBackLearned { node: src, via: *from }));
                }
                let pkt = Pkt {
                    src: &src,
                    dst: &dst,
                    flag,
                    packet,
                };
                self.route(now, &pkt, route::Origin::Peer, sink)
            }
            Frame::Sync { record } => self.replica(now, record, sink),
            Frame::Ping => {
                sink.emit(Effect::PeerRelay {
                    to: *from,
                    frame: Frame::Pong,
                });
                Ok(())
            }
            Frame::Pong => Ok(()),
            Frame::Batch(batch) => {
                let mut first = Ok(());
                for sub in batch.frames() {
                    let r = self.peer_frame(now, from, &sub, sink);
                    first = first.and(r);
                }
                first
            }
            _ => Err(self.reject(sink, Reject::UnexpectedFrame, Some(*from))),
        }
    }

    /// Sweep the tables and run the timers; call it when [`Relay::next_deadline`] is reached.
    pub fn handle_timeout<S: Sink>(&mut self, now: u64, sink: &mut S) {
        self.republish_due(now, sink);
        if now >= self.next_ping {
            self.next_ping = now.saturating_add(rule::CLIENT_PING_NS);
            for (node, _) in self.clients.iter() {
                sink.emit(Effect::Carrier {
                    to: *node,
                    frame: Frame::Ping,
                });
            }
        }
        if now.saturating_sub(self.last_sweep) < rule::SWEEP_NS {
            return;
        }
        self.last_sweep = now;
        let limit = self.cfg.quota.session_ns;
        let Self { clients, gone, .. } = self;
        clients.retain(|node, c| {
            if now.saturating_sub(c.opened) < limit {
                return true;
            }
            let _ = gone.insert(*node, now);
            sink.emit(Effect::Trace(Trace::SessionExpired { node: *node }));
            sink.emit(Effect::Close {
                node: *node,
                session: c.id,
                reason: CloseReason::SessionTime,
            });
            false
        });
        self.gone.retain(|_, at| now.saturating_sub(*at) < rule::GONE_TTL_NS);
        self.sleeping
            .retain(|_, s| now.saturating_sub(s.at) < rule::GONE_TTL_NS);
        self.records.sweep(now);
        self.mailbox.sweep(now);
    }

    /// The next time [`Relay::handle_timeout`] has work, or `None` if nothing is scheduled.
    pub fn next_deadline(&self) -> Option<u64> {
        let sweep = self.last_sweep.saturating_add(rule::SWEEP_NS).min(self.next_ping);
        Some(self.next_publish.map_or(sweep, |p| sweep.min(p)))
    }
}
