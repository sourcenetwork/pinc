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
//! - A close is always recorded: when the gone table (capacity `C`, entries kept [`super::rule::GONE_TTL_NS`]) is full,
//!   the entry with the oldest time makes room. So when more than `C` nodes close within that time the oldest closes
//!   are forgotten first, and a forgotten node is [`NodeState::Unknown`] (its later sleep notice is refused until it
//!   opens a carrier again).
//! - Aliases are per session and direction and reset with the session.

use pinc_crypto::NodeId;

use super::route::Pkt;
use super::{CloseReason, Effect, Reject, Relay, Route, Sink, Table, Trace, live, route, rule};
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

/// Record that `node` closed at `now`. A full table first drops its entry with the oldest time (a node already in it
/// only has its time refreshed), so the close is never lost and the table never holds more than `C` entries.
///
/// Cost: at most one pass over `C` entries, only when the table is full; no allocation. A node without the relay
/// role has no table. An entry is 48 bytes (a 33-byte node id padded, and a `u64` time); `C` is 1024 on every node
/// that carries the relay role, an ordinary node and a node deployed from the relay binary alike.
fn record_gone<const C: usize>(gone: &mut Table<u64, C>, node: NodeId, now: u64) {
    if gone.is_full() && !gone.contains(&node) {
        let oldest = gone.iter().min_by_key(|(_, at)| **at).map(|(k, _)| *k);
        if let Some(oldest) = oldest {
            gone.remove(&oldest);
        }
    }
    // Room was made above, so the insert cannot fail; an `Err` would only mean a full table, which the pass cleared.
    let _ = gone.insert(node, now);
}

const _: () = assert!(core::mem::size_of::<(NodeId, u64)>() <= 48, "a gone entry is 48 bytes");

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
        let slept = self.sleeping.remove(&node).is_some();
        sink.emit(Effect::Trace(Trace::CarrierOpened { node, session: id }));
        if slept {
            sink.emit(Effect::Trace(Trace::SleepEnded { node }));
        }
        self.deliver_held(now, &node, sink);
        Ok(id)
    }

    /// The carrier of `session` closed. Ignored if the node has a newer session.
    pub fn carrier_closed<S: Sink>(&mut self, now: u64, node: &NodeId, session: SessionId, sink: &mut S) {
        if self.clients.get(node).map(|c| c.id) != Some(session) {
            return;
        }
        self.clients.remove(node);
        record_gone(&mut self.gone, *node, now);
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
            record_gone(gone, *node, now);
            sink.emit(Effect::Trace(Trace::SessionExpired { node: *node }));
            sink.emit(Effect::Close {
                node: *node,
                session: c.id,
                reason: CloseReason::SessionTime,
            });
            false
        });
        self.gone.retain(|_, at| now.saturating_sub(*at) < rule::GONE_TTL_NS);
        // a mark ends with the mail held under it: the mark's life is the mailbox's maximum age
        let max_age = self.cfg.mailbox_max_age_ns;
        let Self { sleeping, mailbox, .. } = self;
        sleeping.retain(|node, s| {
            let keep = live(now, s, max_age);
            if !keep {
                mailbox.clear(node);
            }
            keep
        });
        self.records.sweep(now);
        self.mailbox.sweep(now);
    }

    /// The next time [`Relay::handle_timeout`] has work, or `None` if nothing is scheduled.
    pub fn next_deadline(&self) -> Option<u64> {
        let sweep = self.last_sweep.saturating_add(rule::SWEEP_NS).min(self.next_ping);
        Some(self.next_publish.map_or(sweep, |p| sweep.min(p)))
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use pinc_crypto::IdentityAlg;

    use super::*;
    use crate::relay::Config;

    const SEC: u64 = 1_000_000_000;

    struct Null;

    impl Sink for Null {
        fn emit(&mut self, _: Effect<'_>) {}
    }

    fn node(tag: u8) -> NodeId {
        NodeId {
            alg: IdentityAlg::Ed25519,
            bytes: [tag; 32],
        }
    }

    fn relay() -> Relay<2, 2, 2, 64> {
        Relay::new(Config::new(node(99), 7))
    }

    fn open_close(r: &mut Relay<2, 2, 2, 64>, tag: u8, open_at: u64, close_at: u64) {
        let sid = r.carrier_opened(open_at, node(tag), &mut Null).unwrap();
        r.carrier_closed(close_at, &node(tag), sid, &mut Null);
    }

    #[test]
    fn a_close_after_a_full_table_drops_the_oldest_and_keeps_the_newest() {
        let mut r = relay();
        open_close(&mut r, 1, 0, SEC);
        open_close(&mut r, 2, 0, 2 * SEC);
        open_close(&mut r, 3, 0, 3 * SEC);
        assert_eq!(r.gone.len(), 2);
        assert_eq!(r.node_state(&node(1)), NodeState::Unknown);
        assert_eq!(
            r.node_state(&node(2)),
            NodeState::Gone {
                since: 2 * SEC,
                asleep: false
            }
        );
        assert_eq!(
            r.node_state(&node(3)),
            NodeState::Gone {
                since: 3 * SEC,
                asleep: false
            }
        );
    }

    #[test]
    fn a_tie_for_the_oldest_close_goes_to_the_first_in_slot_order() {
        let mut r = relay();
        open_close(&mut r, 1, 0, SEC);
        open_close(&mut r, 2, 0, SEC);
        let first = *r.gone.iter().next().map(|(k, _)| k).unwrap();
        let other = if first == node(1) { node(2) } else { node(1) };
        open_close(&mut r, 3, 0, 2 * SEC);
        assert_eq!(r.gone.len(), 2);
        assert_eq!(r.node_state(&first), NodeState::Unknown);
        assert_eq!(
            r.node_state(&other),
            NodeState::Gone {
                since: SEC,
                asleep: false
            }
        );
        assert!(matches!(r.node_state(&node(3)), NodeState::Gone { .. }));
    }

    #[test]
    fn a_close_of_a_node_already_in_a_full_table_refreshes_it_and_evicts_nobody() {
        let mut r = relay();
        open_close(&mut r, 1, 0, SEC);
        open_close(&mut r, 2, 0, 2 * SEC);
        open_close(&mut r, 1, 3 * SEC, 4 * SEC);
        assert_eq!(r.gone.len(), 2);
        assert_eq!(
            r.node_state(&node(1)),
            NodeState::Gone {
                since: 4 * SEC,
                asleep: false
            }
        );
        assert_eq!(
            r.node_state(&node(2)),
            NodeState::Gone {
                since: 2 * SEC,
                asleep: false
            }
        );
    }

    #[test]
    fn a_session_expiry_after_a_full_table_drops_the_oldest_and_keeps_the_newest() {
        let mut r = relay();
        open_close(&mut r, 1, 0, SEC);
        open_close(&mut r, 2, 0, 2 * SEC);
        let limit = 100 * SEC;
        r.cfg.quota.session_ns = limit;
        let _ = r.carrier_opened(0, node(3), &mut Null).unwrap();
        r.handle_timeout(limit, &mut Null);
        assert_eq!(r.sessions(), 0);
        assert_eq!(r.gone.len(), 2);
        assert_eq!(r.node_state(&node(1)), NodeState::Unknown);
        assert_eq!(
            r.node_state(&node(2)),
            NodeState::Gone {
                since: 2 * SEC,
                asleep: false
            }
        );
        assert_eq!(
            r.node_state(&node(3)),
            NodeState::Gone {
                since: limit,
                asleep: false
            }
        );
    }
}
