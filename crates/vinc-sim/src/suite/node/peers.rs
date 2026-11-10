//! The relay mesh of the hubs: a protected carrier between every pair of hubs, carrying the relays' own frames
//! (forwarded packets, record replicas, pings) so that a node whose relay is not the relay of the node it looks for is
//! still found and reached.
//!
//! The hub with the lower world index dials the other over a simulated TCP stream with the peer protocol name; the
//! other end tells the carrier from a client's by that name. An open carrier makes the other hub a peer relay of this
//! one, and its frames go to the relay's peer entry instead of the client entry. A carrier that ends is dialed again
//! after a short wait.
//!
//! Invariants: only a node the world lists as a relay becomes a peer relay; at most one carrier per peer relay is
//! kept (the newest); a peer relay is removed from the relay when its carrier ends.

use std::net::SocketAddr;

use vinc_connect::carrier::session::{PEER_ALPN, ProtectedCarrier};
use vinc_crypto::NodeId;
use vinc_security::{ConnId, CreditRecord, Env, InitiatorParams};

use super::core::Core;
use super::relay::RStream;
use crate::{StreamId, StreamKind, StreamOp};

/// How long a peer relay waits before it is dialed again.
const REDIAL: u64 = 3_000_000_000;

/// A peer relay this relay dials.
pub(super) struct PeerOut {
    pub(super) id: NodeId,
    pub(super) tcp: SocketAddr,
    pub(super) stream: Option<StreamId>,
    pub(super) retry_at: u64,
}

impl Core {
    /// Lists the peer relays this hub dials: the other hubs with a higher world index.
    pub(super) fn hub_peers_init(&mut self) {
        let now = self.local;
        let idx = self.idx;
        let outs: Vec<PeerOut> = self
            .shared
            .relays()
            .iter()
            .filter(|r| self.shared.index_of(&r.id).is_some_and(|i| i > idx))
            .filter_map(|r| {
                Some(PeerOut {
                    id: r.id,
                    tcp: r.tcp?,
                    stream: None,
                    retry_at: now,
                })
            })
            .collect();
        if let Some(h) = self.hub.as_mut() {
            h.peers_out = outs;
        }
    }

    /// Opens the streams to the peer relays that are due.
    pub(super) fn hub_dial_peers(&mut self) {
        let now = self.local;
        let Some(from) = self.stream_local() else { return };
        let mut due = Vec::new();
        if let Some(h) = self.hub.as_mut() {
            for p in h
                .peers_out
                .iter_mut()
                .filter(|p| p.stream.is_none() && p.retry_at <= now)
            {
                p.retry_at = now.saturating_add(REDIAL);
                due.push(p.tcp);
            }
        }
        for tcp in due {
            let op = StreamOp::Connect {
                local: from,
                remote: tcp,
                kind: StreamKind::Tcp,
                simultaneous: false,
            };
            self.wire.ops.push_back((op, Vec::new()));
            self.wire.connects.push_back((super::carrier::Dial::Peer, tcp));
        }
    }

    /// The simulator accepted the dial of a peer relay and named the stream.
    pub(super) fn hub_peer_pending(&mut self, stream: StreamId, remote: SocketAddr) {
        if let Some(h) = self.hub.as_mut()
            && let Some(p) = h.peers_out.iter_mut().find(|p| p.tcp == remote && p.stream.is_none())
        {
            p.stream = Some(stream);
        }
    }

    /// Whether `stream` is a stream this hub dialed to a peer relay.
    pub(super) fn hub_is_peer_dial(&self, stream: StreamId) -> bool {
        self.hub
            .as_ref()
            .is_some_and(|h| h.peers_out.iter().any(|p| p.stream == Some(stream)))
    }

    /// The stream to a peer relay is open: start the handshake.
    pub(super) fn hub_peer_dialed(&mut self, stream: StreamId) {
        let (now, prov) = (self.local, self.provider());
        let Some(prekey) = self.prekey_info.clone() else { return };
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(id) = hub.peers_out.iter().find(|p| p.stream == Some(stream)).map(|p| p.id) else {
            return;
        };
        hub.scid += 1;
        let Some(scid) = ConnId::new(&hub.scid.to_be_bytes()) else {
            return;
        };
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut self.hub_drbg,
        };
        let params = InitiatorParams {
            peer: id,
            alpn: PEER_ALPN,
            scid,
            identity: &self.identity,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: None,
            credit: CreditRecord::NONE,
        };
        if let Ok(c) = ProtectedCarrier::dial(&mut env, params) {
            hub.streams.insert(stream, RStream::new(Box::new(c), true));
            self.flush_handshake(stream);
        } else {
            self.wire.ops.push_back((StreamOp::Close { stream }, Vec::new()));
            self.hub_closed(stream);
        }
    }

    /// A carrier to or from a peer relay completed its handshake.
    pub(super) fn hub_peer_open(&mut self, sid: StreamId, peer: NodeId) {
        let trusted = self.shared.relays().iter().any(|r| r.id == peer);
        let Some(hub) = self.hub.as_mut() else { return };
        if !trusted {
            // Only the relays the world lists may join the mesh.
            hub.streams.remove(&sid);
            self.wire.ops.push_back((StreamOp::Close { stream: sid }, Vec::new()));
            return;
        }
        if let Some(rs) = hub.streams.get_mut(&sid) {
            rs.node = Some(peer);
            rs.peer = true;
        }
        hub.relay.add_peer(peer);
        let old = hub.peer_by_node.insert(peer.bytes, sid).filter(|o| *o != sid);
        if let Some(old) = old {
            hub.streams.remove(&old);
            self.wire.ops.push_back((StreamOp::Close { stream: old }, Vec::new()));
        }
    }

    /// A stream ended: if it joined a peer relay, forget the peer and plan the next dial.
    pub(super) fn hub_peer_closed(&mut self, sid: StreamId) {
        let now = self.local;
        let Some(hub) = self.hub.as_mut() else { return };
        for p in hub.peers_out.iter_mut().filter(|p| p.stream == Some(sid)) {
            p.stream = None;
            p.retry_at = now.saturating_add(REDIAL);
        }
        let Some(node) = hub.streams.get(&sid).filter(|r| r.peer).and_then(|r| r.node) else {
            return;
        };
        if hub.peer_by_node.get(&node.bytes) == Some(&sid) {
            hub.peer_by_node.remove(&node.bytes);
            hub.relay.remove_peer(&node);
        }
    }

    /// Writes a relay frame on the carrier of peer relay `to`.
    pub(super) fn write_peer(&mut self, to: &NodeId, plain: &[u8]) {
        let prov = self.provider();
        let Some(hub) = self.hub.as_mut() else { return };
        let Some(sid) = hub.peer_by_node.get(&to.bytes).copied() else {
            return;
        };
        let Some(rs) = hub.streams.get_mut(&sid) else { return };
        let mut out = vec![0u8; vinc_connect::carrier::MAX_FRAME_LEN + 64];
        let Ok(n) = rs.carrier.seal_bytes(&prov, plain, &mut out) else {
            return;
        };
        out.truncate(n);
        self.write_op(sid, out);
    }
}
