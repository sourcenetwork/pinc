//! The node's side of the connectivity client: what a host tells the node about its interfaces, its prekey, its
//! addresses and its relays' carrier streams, and what the client asks of the host in return.
//!
//! The client itself (`vinc-connect`) is a state machine; the host moves the bytes of the carrier streams, answers the
//! key operations and signs. Every call here hands one such input to the client and lets the node's layers react.
//!
//! Invariants: a call that changes the client takes the time of the call or clears the node's stored deadline, so
//! [`Node::poll_timeout`] never answers from before it.

use core::net::SocketAddr;

use vinc_connect::client::Io as CarrierIo;
use vinc_connect::record::MAX_ADDRS;
use vinc_core::{IfaceEvent, IfaceId};
use vinc_crypto::Provider;
use vinc_security::{Env, KeyRequest, KeyResponse, PrekeyInfo};

use crate::apps::{Apps, ServeSource};
use crate::config::{Nanos, Store};
use crate::ep::Ep;
use crate::node::{Due, Node};

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// Add an interface to the endpoint; `None` when its table is full. A host calls it for an interface that appears
    /// after the node started, and tells the node about the new address with [`Node::set_local`].
    pub fn add_iface(&mut self, local: SocketAddr) -> Option<IfaceId> {
        self.deadline.set(Due::Stale);
        self.io.ep.add_iface(local)
    }

    /// An interface of the endpoint came up, went down or changed its address.
    pub fn iface_event(&mut self, now: Nanos, id: IfaceId, ev: IfaceEvent) {
        self.begin(now);
        self.io.ep.iface_event(now, id, ev);
        self.settle(now);
    }

    /// Use `prekey` in the carrier handshakes that start from now on (the endpoint's own prekey rotates).
    pub fn set_prekey(&mut self, prekey: PrekeyInfo) {
        self.deadline.set(Due::Stale);
        self.conn.set_prekey(prekey);
    }

    /// Turn the beacons of local discovery on or off (they are on by default).
    pub fn set_local_discovery(&mut self, on: bool) {
        self.deadline.set(Due::Stale);
        self.conn.set_local_discovery(on);
    }

    /// Pin the relay at table position `relay` as the home relay, over one with a lower round trip
    /// (`Connectivity::pin_home`).
    pub fn pin_home(&mut self, relay: usize) {
        self.deadline.set(Due::Stale);
        self.conn.pin_home(relay);
    }

    /// Set the node's own addresses.
    pub fn set_local(&mut self, addrs: &[SocketAddr]) {
        self.deadline.set(Due::Stale);
        self.local_addrs = [None; MAX_ADDRS];
        for (d, a) in self.local_addrs.iter_mut().zip(addrs) {
            *d = Some(*a);
        }
        self.conn.set_local(addrs);
    }

    /// The next request for a carrier stream.
    pub fn poll_io(&mut self) -> Option<CarrierIo> {
        self.deadline.set(Due::Stale);
        self.conn.poll_io()
    }

    /// The carrier stream of `relay` is open.
    pub fn stream_opened(&mut self, now: Nanos, relay: usize) {
        self.begin(now);
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.stream_opened(now, &mut env, relay);
        self.settle(now);
    }

    /// The carrier stream of `relay` closed.
    pub fn stream_closed(&mut self, now: Nanos, relay: usize) {
        self.begin(now);
        self.conn.stream_closed(now, relay);
        self.settle(now);
    }

    /// Bytes arrived on the carrier stream of `relay`; returns how many were used.
    pub fn stream_data(&mut self, now: Nanos, relay: usize, bytes: &[u8]) -> usize {
        self.begin(now);
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg: &mut self.drbg,
        };
        let n = self.conn.stream_data(now, &mut env, relay, bytes);
        self.settle(now);
        n
    }

    /// The next bytes to write on the carrier stream of `relay`.
    pub fn poll_stream(&mut self, relay: usize, buf: &mut [u8]) -> usize {
        self.deadline.set(Due::Stale);
        self.conn.poll_stream(relay, buf)
    }

    /// The next UDP datagram of the connectivity layer (a relay probe, a lookup, a beacon).
    pub fn poll_udp(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        self.deadline.set(Due::Stale);
        self.pm_poll_udp(buf).or_else(|| self.conn.poll_udp(buf))
    }

    /// As [`Self::poll_udp`], with the local address the datagram must leave from, when it has to leave from one.
    pub fn poll_udp_from(&mut self, buf: &mut [u8]) -> Option<(Option<SocketAddr>, SocketAddr, usize)> {
        self.deadline.set(Due::Stale);
        self.pm_poll_udp(buf)
            .map(|(to, n)| (None, to, n))
            .or_else(|| self.conn.poll_udp_from(buf))
    }

    /// A key operation the carrier handshake of `relay` waits for.
    pub fn key_request(&self, relay: usize) -> Option<KeyRequest<'_>> {
        self.conn.key_request(relay)
    }

    /// The answer to [`Node::key_request`].
    pub fn key_response(&mut self, now: Nanos, relay: usize, resp: KeyResponse<'_>) {
        self.begin(now);
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.key_response(now, &mut env, relay, resp);
        self.settle(now);
    }

    /// A signature the connectivity layer waits for (its record, a sleep notice or a beacon).
    pub fn sign_request(&self) -> Option<KeyRequest<'_>> {
        self.conn.sign_request()
    }

    /// The answer to [`Node::sign_request`].
    pub fn sign_response(&mut self, now: Nanos, resp: KeyResponse<'_>) {
        self.begin(now);
        self.conn.sign_response(now, resp);
        self.settle(now);
    }

    /// Put `hints` (at most 64 bytes) in this node's record and publish it again. False if they are too long.
    pub fn set_hints(&mut self, now: Nanos, hints: &[u8]) -> bool {
        self.begin(now);
        let ok = self.conn.set_hints(hints);
        self.settle(now);
        ok
    }

    /// Raise the sequence number of the last record to `seq`, as read with `Connectivity::record_seq`.
    pub fn restore_record_seq(&mut self, seq: u64) {
        self.conn.restore_record_seq(seq);
    }

    /// Ask the relays for `peer`'s record.
    pub fn lookup(&mut self, now: Nanos, peer: &vinc_crypto::NodeId) {
        self.begin(now);
        self.conn.lookup(now, peer);
        self.settle(now);
    }

    /// A beacon of local discovery arrived.
    pub fn handle_beacon(&mut self, now: Nanos, bytes: &[u8]) -> Option<vinc_crypto::NodeId> {
        self.begin(now);
        let r = self.conn.handle_beacon(now, bytes);
        self.settle(now);
        r
    }

    /// The node is suspended (the app froze or the device sleeps).
    pub fn suspend(&mut self, now: Nanos, wall_ms: u64) {
        self.begin(now);
        self.io.set_wall(wall_ms);
        self.conn.suspend_all(now, &mut self.io.ep, wall_ms);
        self.settle(now);
    }

    /// The node runs again; `moved` says the address changed meanwhile.
    pub fn resume(&mut self, now: Nanos, moved: bool) {
        self.begin(now);
        self.conn.resume_all(now, &mut self.io.ep, moved);
        if moved {
            self.mem.address_changed(now);
        }
        self.settle(now);
    }
}
