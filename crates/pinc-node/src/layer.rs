//! The layers above broadcast and the sessions they ride.
//!
//! Values, reconcile and delay-tolerant delivery each speak their own protocol id, so each has sessions of its own
//! with a peer, separate from the hub stream. A session of a layer is dialed on demand by the layer that needs it
//! (the node finds the way through the connectivity client) and accepted when a peer dials the layer's protocol id,
//! which the node registers only for a layer the host enabled.
//!
//! Invariants: a session belongs to exactly one layer, found by its protocol id; the tables are bounded by
//! [`TABLE_MAX`](crate::config); a peer that is revoked has no session of any layer.

use pinc_core::{Command, Event, Role, SessionId};
use pinc_membership::NodeId;

use crate::apps::Apps;
use crate::config::{DTN_ALPN, Nanos, SESSION_LIVED, SETS_ALPN, Store, TABLE_MAX, VALUES_ALPN};
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::node::Node;
use crate::trace::{NodeTrace, tag};

/// A layer with a protocol id of its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Layer {
    /// Verified streaming of values.
    Values,
    /// Set reconciliation.
    Sets,
    /// Delay-tolerant delivery.
    Dtn,
}

impl Layer {
    /// The protocol id of the layer.
    pub const fn alpn(self) -> &'static [u8] {
        match self {
            Self::Values => VALUES_ALPN,
            Self::Sets => SETS_ALPN,
            Self::Dtn => DTN_ALPN,
        }
    }

    /// The layer a protocol id belongs to.
    pub fn of_alpn(alpn: &[u8]) -> Option<Self> {
        [Self::Values, Self::Sets, Self::Dtn]
            .into_iter()
            .find(|l| l.alpn() == alpn)
    }

    const fn code(self) -> u64 {
        match self {
            Self::Values => 1,
            Self::Sets => 2,
            Self::Dtn => 3,
        }
    }
}

/// A session of a layer.
#[derive(Debug, Clone, Copy)]
pub(crate) struct LSess {
    pub(crate) layer: Layer,
    pub(crate) peer: NodeId,
    /// The peer dialed us.
    pub(crate) incoming: bool,
    /// When the session came up.
    pub(crate) opened: Nanos,
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: pinc_crypto::Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: crate::apps::ServeSource<A::Values>,
{
    /// The layer an endpoint event belongs to: by protocol id for a session coming up or a dial failing, by the
    /// session for everything else.
    pub(crate) fn event_layer(&self, ev: &Event) -> Option<Layer> {
        match ev {
            Event::Connected { alpn, .. } | Event::Incoming { alpn, .. } | Event::ConnectFailed { alpn, .. } => {
                Layer::of_alpn(alpn.as_bytes())
            }
            Event::Closed { session, .. }
            | Event::StreamOpened { session, .. }
            | Event::StreamReadable { session, .. }
            | Event::StreamWritable { session, .. }
            | Event::StreamReset { session, .. }
            | Event::StreamStopped { session, .. }
            | Event::OpenReady { session }
            | Event::DatagramReceived { session } => self.io.lsess.get(session).map(|s| s.layer),
            _ => None,
        }
    }

    /// Handle an endpoint event of a layer's session. Lifecycle events also reach the application; nothing else of a
    /// layer's session does.
    pub(crate) fn on_layer_event(&mut self, now: Nanos, layer: Layer, ev: Event) {
        match ev {
            Event::Connected { session, node, .. } => {
                self.io.learn_alg(&node);
                self.layer_up(now, layer, session, node.bytes, false);
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            Event::Incoming { session, node, .. } => {
                self.io.learn_alg(&node);
                self.layer_up(now, layer, session, node.bytes, true);
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            Event::ConnectFailed { node, .. } => {
                self.layer_failed(now, layer, &node.bytes);
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            Event::Closed { session, .. } => {
                self.layer_closed(now, session);
                self.io.emit(NodeEvent::Endpoint(ev));
            }
            Event::StreamOpened { session, stream } => match layer {
                Layer::Values => self.values_stream_opened(now, session, stream),
                Layer::Sets => self.sets_stream_opened(session, stream),
                Layer::Dtn => self.dtn_stream_opened(session, stream),
            },
            Event::StreamReadable { session, stream } => match layer {
                Layer::Values => self.values_readable(now, session, stream),
                Layer::Sets => self.sets_readable(now, session, stream),
                Layer::Dtn => self.dtn_readable(now, session, stream),
            },
            Event::StreamWritable { session, stream } => self.io.flush(session, stream),
            Event::StreamReset { session, stream, error } | Event::StreamStopped { session, stream, error } => {
                self.io.drop_strm(session, stream);
                match layer {
                    Layer::Values => self.values_stream_gone(now, session, stream, error),
                    Layer::Sets => self.sets_stream_gone(now, session, stream, error),
                    Layer::Dtn => self.dtn_stream_gone(session, stream),
                }
            }
            // A layer opens its streams on its own ticks and has no use for datagrams.
            Event::OpenReady { .. } | Event::DatagramReceived { .. } => {}
            other => self.io.emit(NodeEvent::Endpoint(other)),
        }
    }

    /// Whether the layer runs on this node.
    pub(crate) const fn layer_on(&self, layer: Layer) -> bool {
        match layer {
            Layer::Values => self.vals.is_some(),
            Layer::Sets => self.recs.is_some(),
            Layer::Dtn => self.dtn.is_some(),
        }
    }

    /// Dial `peer` for `layer`, unless a session or a dial exists. The delay-tolerant layer also waits out a backoff,
    /// which a membership event about the peer clears; values and reconcile redial by their own rules. A dial the node
    /// refuses is reported to the layer.
    pub(crate) fn dial_layer(&mut self, now: Nanos, layer: Layer, peer: &NodeId) {
        let key = (layer, *peer);
        let io = &self.io;
        if io.lout.contains_key(&key) || io.lconn.contains(&key) {
            return;
        }
        if self.leaving || io.revoked.contains(peer) {
            self.layer_lost(now, layer, peer, true);
            return;
        }
        if layer == Layer::Dtn
            && let Some(d) = self.dtn.as_deref_mut()
            && io.dtn_skip(now, peer, &mut d.redial_at)
        {
            return;
        }
        if io.lconn.len() >= TABLE_MAX {
            // No room to record the dial: sending it would let the next call send it again.
            self.layer_lost(now, layer, peer, false);
            return;
        }
        let id = io.full_id(peer);
        if self
            .conn
            .dial(now, &mut self.io.ep, id, layer.alpn(), Role::Other, &[])
            .is_ok()
        {
            self.io.lconn.insert(key);
            self.io.trace(NodeTrace::LayerDial {
                layer: layer.code(),
                peer: tag(peer),
            });
        } else {
            self.layer_failed(now, layer, peer);
        }
    }

    /// A session of `layer` came up: dialed by us (`incoming` false) or by `peer`.
    pub(crate) fn layer_up(&mut self, now: Nanos, layer: Layer, session: SessionId, peer: NodeId, incoming: bool) {
        self.io.lconn.remove(&(layer, peer));
        if !self.layer_on(layer) || self.io.revoked.contains(&peer) || self.leaving {
            self.io.shed(session);
            if !incoming {
                self.layer_lost(now, layer, &peer, true);
            }
            return;
        }
        if self.io.lsess.len() >= TABLE_MAX {
            self.io.shed(session);
            if !incoming {
                self.layer_lost(now, layer, &peer, false);
            }
            return;
        }
        if !incoming && self.io.lout.contains_key(&(layer, peer)) {
            // Both ends dialed at once, or the dial was asked for twice: one session of ours per layer and peer.
            self.io.shed(session);
            self.io.trace(NodeTrace::DuplicateClosed { peer: tag(&peer) });
            return;
        }
        self.io.lsess.insert(
            session,
            LSess {
                layer,
                peer,
                incoming,
                opened: now,
            },
        );
        if !incoming {
            self.io.lout.insert((layer, peer), session);
        }
        self.io.trace(NodeTrace::LayerUp {
            layer: layer.code(),
            peer: tag(&peer),
            incoming: u64::from(incoming),
        });
        match layer {
            Layer::Values => self.values_up(now, session, &peer, incoming),
            Layer::Sets => self.sets_up(now, session, &peer, incoming),
            Layer::Dtn => self.dtn_up(now, session, &peer, incoming),
        }
    }

    /// A dial of `layer` to `peer` ends with no session: refused for good (`cancel`: the node leaves or the peer is
    /// revoked, so a reconcile round ends cancelled) or failed (the layer retries by its own rules).
    fn layer_lost(&mut self, now: Nanos, layer: Layer, peer: &NodeId, cancel: bool) {
        if cancel && layer == Layer::Sets {
            self.io.lconn.remove(&(layer, *peer));
            self.sets_cancelled(peer);
        } else {
            self.layer_failed(now, layer, peer);
        }
    }

    /// A dial of `layer` failed or was refused: the layer learns of it, and a delay-tolerant redial waits.
    pub(crate) fn layer_failed(&mut self, now: Nanos, layer: Layer, peer: &NodeId) {
        self.io.lconn.remove(&(layer, *peer));
        match layer {
            Layer::Values => self.values_failed(now, peer),
            Layer::Sets => self.sets_failed(now, peer),
            Layer::Dtn => {
                let at = self.io.dtn_failed(now, peer);
                if let Some(d) = self.dtn.as_deref_mut() {
                    d.redial_at = crate::dtn::sooner(d.redial_at, at);
                }
            }
        }
    }

    /// A session of `layer` ended.
    pub(crate) fn layer_closed(&mut self, now: Nanos, session: SessionId) {
        let Some(s) = self.io.lsess.remove(&session) else {
            return;
        };
        self.io.drop_session_streams(session);
        let key = (s.layer, s.peer);
        let ours = self.io.lout.get(&key) == Some(&session);
        if ours {
            self.io.lout.remove(&key);
            if now.saturating_sub(s.opened) >= SESSION_LIVED {
                self.io.lfailed.remove(&key);
            }
        }
        self.io.trace(NodeTrace::LayerDown {
            layer: s.layer.code(),
            peer: tag(&s.peer),
        });
        match s.layer {
            Layer::Values => self.values_down(now, session, &s.peer, ours),
            Layer::Sets => self.sets_down(now, session, &s.peer),
            Layer::Dtn => self.dtn_down(now, session, &s.peer),
        }
    }

    /// The session of `layer` to `peer` that writes should use: the one we dialed, else the lowest incoming.
    pub(crate) fn layer_session(&self, layer: Layer, peer: &NodeId) -> Option<SessionId> {
        self.io.lout.get(&(layer, *peer)).copied().or_else(|| {
            self.io
                .lsess
                .iter()
                .find(|(_, s)| s.layer == layer && s.peer == *peer)
                .map(|(sid, _)| *sid)
        })
    }

    /// Close every session of `layer` with `peer` (a peer out of contact).
    pub(crate) fn close_layer_sessions(&mut self, layer: Layer, peer: &NodeId) {
        let sessions: alloc::vec::Vec<SessionId> = self
            .io
            .lsess
            .iter()
            .filter(|(_, s)| s.layer == layer && s.peer == *peer)
            .map(|(sid, _)| *sid)
            .collect();
        for session in sessions {
            let _ = self.io.cmd(Command::Close { session, error: 0 });
        }
    }
}
