//! The relay mesh of a core: which peers to dial, the carriers it dials, and a peer's carrier opening and ending (see
//! [`super::super::peers`]).

use alloc::boxed::Box;
use alloc::vec::Vec;

use vinc_connect::carrier::ProtectedCarrier;
use vinc_connect::carrier::session::PEER_ALPN;
use vinc_crypto::{NodeId, Software};
use vinc_keystore::KeyStore;
use vinc_security::{ConnId, CreditRecord, Env, InitiatorParams};

use super::Core;
use crate::carrier::CarrierKind;
use crate::relay::conn::Conn;
use crate::relay::peers::{Link, Peer, REDIAL_NS, Slot, dials};
use crate::relay::stats::{Closed, Event};
use crate::relay::store::node_key;

/// The peers a relay lists, without itself.
pub(super) fn slots(me: &NodeId, peers: &[Peer], now: u64) -> Vec<Slot> {
    let mut out: Vec<Slot> = Vec::new();
    for p in peers.iter().filter(|p| p.id != *me) {
        if !out.iter().any(|s| s.peer.id == p.id) {
            out.push(Slot {
                peer: *p,
                link: Link::Idle(now),
            });
        }
    }
    out
}

impl<S, K: KeyStore> Core<S, K> {
    /// Whether `node` is listed as a peer relay.
    pub(super) fn is_listed(&self, node: &NodeId) -> bool {
        self.peers.iter().any(|s| s.peer.id == *node)
    }

    /// The next peer to dial, if one is due: the host opens a stream of the returned kind to it and calls
    /// [`Core::dialed`] or [`Core::dial_failed`].
    pub(crate) fn next_dial(&mut self, now: u64) -> Option<(usize, Peer, CarrierKind)> {
        if self.stopping {
            return None;
        }
        let me = self.identity.node_id();
        let i = self.peers.iter().position(|s| {
            matches!(s.link, Link::Idle(at) if at <= now) && dials(&me, &s.peer.id) && s.peer.kind().is_some()
        })?;
        let s = self.peers.get_mut(i)?;
        s.link = Link::Opening;
        let kind = s.peer.kind()?;
        Some((i, s.peer, kind))
    }

    /// The host opened a stream to peer `i`: start the handshake on it. A stream that cannot be used is given back.
    pub(crate) fn dialed(&mut self, i: usize, stream: S, kind: CarrierKind, now: u64) -> Result<usize, S> {
        let Some(peer) = self.peers.get(i).map(|s| s.peer).filter(|_| !self.stopping) else {
            return Err(stream);
        };
        if self.prekeys.due(now) {
            let Ok(info) = self.prekeys.rotate(now) else {
                self.dial_failed(i, now);
                return Err(stream);
            };
            self.dial_prekey = info;
        }
        self.scid += 1;
        let Some(scid) = ConnId::new(&self.scid.to_be_bytes()) else {
            self.dial_failed(i, now);
            return Err(stream);
        };
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        let dialed = ProtectedCarrier::dial(
            &mut env,
            InitiatorParams {
                peer: peer.id,
                alpn: PEER_ALPN,
                scid,
                identity: &self.local,
                prekey: &self.dial_prekey,
                peer_has_prekey: false,
                ticket: None,
                credit: CreditRecord::NONE,
            },
        );
        let Ok(carrier) = dialed else {
            self.dial_failed(i, now);
            return Err(stream);
        };
        let mut conn = Conn::new(
            stream,
            kind,
            Box::new(carrier),
            now.saturating_add(self.limits.handshake_ns),
        );
        conn.last_rx = now;
        conn.dialer = true;
        conn.dial = Some(i);
        conn.dec = vinc_connect::carrier::ws::Decoder::new(vinc_connect::carrier::ws::Role::Server);
        if let Some(s) = self.peers.get_mut(i) {
            s.link = Link::Open;
        }
        self.handshaking += 1;
        let slot = self.place(conn);
        self.transmit_handshake(slot);
        Ok(slot)
    }

    /// The host could not open a stream to peer `i`: dial it again later.
    pub(crate) fn dial_failed(&mut self, i: usize, now: u64) {
        self.counters.peer_dial_failures += 1;
        if let Some(s) = self.peers.get_mut(i) {
            s.link = Link::Idle(now.saturating_add(REDIAL_NS));
        }
    }

    /// When the next peer is due to be dialed.
    pub(super) fn next_dial_at(&self) -> u64 {
        let me = self.identity.node_id();
        self.peers
            .iter()
            .filter(|s| dials(&me, &s.peer.id) && s.peer.kind().is_some())
            .filter_map(|s| match s.link {
                Link::Idle(at) => Some(at),
                _ => None,
            })
            .min()
            .unwrap_or(u64::MAX)
    }

    /// A carrier that dialed or asked for the peer protocol finished its handshake as `peer`.
    pub(super) fn peer_open(&mut self, slot: usize, peer: NodeId, kind: CarrierKind) {
        if !self.is_listed(&peer) {
            self.dying(slot, Closed::Untrusted);
            return;
        }
        if let Some(c) = self.conn(slot) {
            c.node = Some(peer);
            c.peer = true;
        }
        self.handshaking -= 1;
        if let Some(old) = self.by_node.insert(node_key(&peer), slot).filter(|o| *o != slot) {
            self.dying(old, Closed::Replaced);
        }
        self.sm.add_peer(peer);
        if let Some(s) = self.peers.iter_mut().find(|s| s.peer.id == peer) {
            s.link = Link::Open;
        }
        self.counters.carriers_opened += 1;
        self.event(Event::CarrierUp { node: peer, kind });
    }

    /// A peer's stream ended: the machine forgets the peer if this was its current carrier, and a stream this relay
    /// dials is dialed again later.
    pub(super) fn peer_closed(&mut self, slot: usize, node: Option<NodeId>, dial: Option<usize>, now: u64) {
        if let Some(n) = node {
            let key = node_key(&n);
            if self.by_node.get(&key) == Some(&slot) {
                self.by_node.remove(&key);
                self.sm.remove_peer(&n);
            }
        }
        if let Some(s) = dial.and_then(|i| self.peers.get_mut(i)) {
            s.link = Link::Idle(now.saturating_add(REDIAL_NS));
        }
    }
}
