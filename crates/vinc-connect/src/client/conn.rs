//! The connectivity state of a node: its relay carriers, address discovery, lookups and the queues the host drains.
//!
//! [`Connectivity`] is SANS-IO. The host feeds it time, UDP datagrams, stream events and stream bytes, and key
//! answers; it hands back UDP datagrams, stream bytes, stream requests, packets for the endpoint and notices. The
//! parts that need the `vinc-core` endpoint (dialing, first flights, hole punching, the hub tunnel) are in
//! the drive module; this file is everything that does not.
//!
//! Relay paths. A packet to or from a peer through a relay has no UDP address; the endpoint names the path with a
//! synthetic address ([`vinc_core::relay_addr`]), one per (relay, peer) pair. The host sends what the endpoint
//! transmits to such an address with `Connectivity::route`, and gives the endpoint what
//! [`Connectivity::poll_inbound`] yields.
//!
//! Carriers. For each relay a [`Link`] keeps the timing and a [`ProtectedCarrier`] the secured stream. The fallback
//! order is UDP, then TCP, then WebSocket: a failed dial changes the stream kind for the next one. A frame sent
//! while the carrier is not open waits in a bounded queue (the oldest is dropped when it is full; recovery resends
//! it). A key operation of a carrier handshake is raised exactly as the endpoint raises its own
//! ([`Connectivity::key_request`], [`Connectivity::key_response`]).
//!
//! Batching. Frames queued on a carrier back to back join one batch (at most 64 frames and 16 KiB) that is sealed as a
//! single record when the host asks for the carrier's bytes ([`Connectivity::poll_stream`]) or the batch is full. A
//! long-header packet (a handshake packet of the transport) closes the batch and is sealed alone.
//!
//! Failover. A relay whose carrier dials never opened, or whose probes went unanswered on a node that hears UDP,
//! three times in a row is unhealthy; the home moves to the healthy relay with the lowest round trip and the record is
//! published there.
//!
//! Invariants: every table and queue is bounded and nothing allocates; a stream is open only for a relay whose link
//! is not `Down`; sealed bytes leave a carrier in the order they were sealed.

use core::net::SocketAddr;

use vinc_core::{SessionId, relay_addr, relay_parts};
use vinc_crypto::{NodeId, Provider};
use vinc_security::{Env, LocalIdentity, PrekeyInfo};

use super::link::{Link, Shared, State};
use super::lookup::{Ask, Found, LookupError, Lookups};
use super::netcheck::{self, Netcheck, Observed};
use super::tunnel::Splices;
use crate::carrier::frame::{BatchState, DnsAnswer, MAX_FRAME_LEN, MAX_PACKET_LEN};
use crate::carrier::session::ProtectedCarrier;
use crate::carrier::{AliasTable, Frame};
use crate::local::Duty;
use crate::record::{MAX_ADDRS, Reach};
use crate::relay::datagram::Datagram;

/// The size of a carrier's write buffer.
pub const OUT_LEN: usize = 24 * 1024;
/// UDP datagrams waiting to leave.
pub const UDP_QUEUE: usize = 16;
/// Packets waiting for the endpoint.
pub const INBOUND: usize = 16;
/// Found records kept for the dials that waited for them.
pub const FOUND: usize = 8;
/// How long a found record without addresses is believed.
pub const FOUND_TTL: u64 = 30_000_000_000;
/// Notices waiting for the host.
pub const NOTICES: usize = 16;
/// Stream requests waiting for the host.
pub const IO_QUEUE: usize = 16;
/// Sessions the layer follows.
pub const SESSIONS: usize = 32;
/// Sessions that wait for one peer's address.
pub const WAITERS: usize = 4;
/// Local-discovery candidates kept.
pub const LOCAL_PEERS: usize = 8;
/// Outstanding lookups.
pub const LOOKUPS: usize = 16;

/// A stream kind a carrier runs over.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// Plain TCP.
    Tcp,
    /// WebSocket over TCP.
    Ws,
}

/// Where to reach a relay.
#[derive(Debug, Clone, Copy)]
pub struct RelayCfg {
    /// The relay's node id.
    pub id: NodeId,
    /// Its UDP address (address discovery, lookups, the hub session).
    pub udp: Option<SocketAddr>,
    /// Its TCP carrier address (port 443 by default).
    pub tcp: Option<SocketAddr>,
    /// Its WebSocket carrier address (port 443 by default).
    pub ws: Option<SocketAddr>,
}

/// How the connectivity layer starts.
#[derive(Debug, Clone, Copy)]
#[allow(
    clippy::struct_excessive_bools,
    reason = "independent facts about the node, not a state"
)]
pub struct Config<const R: usize> {
    /// This node.
    pub me: NodeId,
    /// This node's identity, for carrier handshakes.
    pub identity: LocalIdentity,
    /// The relays, at most `R`.
    pub relays: [Option<RelayCfg>; R],
    /// The node is a phone.
    pub phone: bool,
    /// The process just restarted.
    pub restarted: bool,
    /// The time the node started.
    pub start: u64,
    /// The synthetic relay addresses are IPv6 (the node has no IPv4 interface).
    pub v6: bool,
    /// Learn the keepalive interval from silent carrier deaths (KEEP_LEARN).
    pub keep_learn: bool,
}

/// A request for the host's streams.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Io {
    /// Open a stream of `kind` to `to` for the carrier of `relay`; report [`Connectivity::stream_opened`] or
    /// [`Connectivity::stream_closed`].
    Open {
        /// The relay's table position.
        relay: usize,
        /// The kind of stream.
        kind: Kind,
        /// The address.
        to: SocketAddr,
    },
    /// Close the stream of `relay`.
    Close {
        /// The relay's table position.
        relay: usize,
    },
}

/// Something the host may want to know.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Notice {
    /// The home relay changed.
    Home(usize),
    /// The reachability class changed; the node's record is republished.
    Class(Reach),
    /// The carrier of this relay opened.
    CarrierUp(usize),
    /// The carrier of this relay closed.
    CarrierDown(usize),
    /// A lookup found the record of a peer.
    Found(NodeId),
    /// A relay holds no record for this peer.
    Missing(NodeId),
    /// A relay answered with a record that did not verify.
    BadRecord(NodeId),
    /// The host's key refused to sign something the layer asked for (a record, a sleep notice or a beacon).
    SignFailed,
}

#[allow(
    clippy::struct_excessive_bools,
    reason = "independent facts about the carrier, not a state"
)]
pub(super) struct Rly<P: Provider> {
    pub(super) cfg: Option<RelayCfg>,
    pub(super) link: Link,
    pub(super) carrier: Option<ProtectedCarrier<P>>,
    pub(super) kind: Kind,
    pub(super) generation: u64,
    pub(super) out: [u8; OUT_LEN],
    pub(super) out_len: usize,
    pub(super) bbuf: [u8; MAX_FRAME_LEN],
    pub(super) bst: BatchState,
    pub(super) q: super::queue::HeldQueue,
    pub(super) keyreq: bool,
    pub(super) ta: AliasTable,
    pub(super) ra: AliasTable,
    pub(super) rides: bool,
    /// The last time a session packet was written to this carrier (a ridden check, CHECK_RIDE).
    pub(super) etx: Option<u64>,
    /// A PONG arrived that the sessions riding this carrier have not yet been told about (CARRIER_PULSE).
    pub(super) pong: bool,
    /// The carrier re-opened after an earlier life and the sessions riding it are still to be pinged.
    pub(super) reverify: bool,
    /// The carrier opened on a very slow node and its held packets wait for the endpoint's view before they go out.
    pub(super) drain_due: bool,
}

#[derive(Clone, Copy)]
pub(super) struct UdpItem {
    pub(super) to: SocketAddr,
    pub(super) len: usize,
    pub(super) data: [u8; MAX_PACKET_LEN],
}

#[derive(Clone, Copy)]
pub(super) struct Inbound {
    pub(super) from: SocketAddr,
    pub(super) len: usize,
    pub(super) data: [u8; MAX_PACKET_LEN],
}

/// The connectivity layer of one node, with `R` relays and `PEERS` peers named on relay paths.
pub struct Connectivity<P: Provider, const R: usize, const PEERS: usize> {
    pub(super) me: NodeId,
    pub(super) identity: LocalIdentity,
    pub(super) prov: P,
    pub(super) prekey: PrekeyInfo,
    pub(super) v6: bool,
    pub(super) start: u64,
    pub(super) rly: [Rly<P>; R],
    pub(super) shared: Shared,
    pub(super) net: Netcheck<R>,
    pub(super) lookups: Lookups<LOOKUPS>,
    pub(super) found: [Option<(NodeId, Found, u64)>; FOUND],
    pub(super) found_next: usize,
    pub(super) peers: [Option<NodeId>; PEERS],
    pub(super) peers_next: usize,
    pub(super) splices: Splices<32, R>,
    pub(super) class: Option<Reach>,
    pub(super) udp_any: bool,
    pub(super) local: [Option<SocketAddr>; MAX_ADDRS],
    pub(super) mapped: [Option<SocketAddr>; 2],
    pub(super) udp_q: [Option<UdpItem>; UDP_QUEUE],
    pub(super) inbound: [Option<Inbound>; INBOUND],
    pub(super) io: [Option<Io>; IO_QUEUE],
    pub(super) notices: [Option<Notice>; NOTICES],
    pub(super) duty: Duty,
    pub(super) next_publish: u64,
    pub(super) next_probe: u64,
    pub(super) scid: u64,
    pub(super) sess: [Option<super::drive::Sess>; SESSIONS],
    pub(super) pending: super::dial::Pending<SessionId, LOOKUPS, WAITERS>,
    pub(super) first_dial: Option<u64>,
    pub(super) found_q: [Option<NodeId>; 4],
    pub(super) beacons: [Option<super::drive::LocalPeer>; LOCAL_PEERS],
    pub(super) node_rtt: u64,
    /// The node's peak handshake round trip.
    pub(super) node_tgr: u64,
    pub(super) sign: super::signing::Signing,
    pub(super) evq: [Option<vinc_core::Event>; 16],
    /// The latest time any call carried.
    pub(super) clock: u64,
    /// Packets dropped because a queue was full.
    pub dropped: u64,
}

impl<P: Provider, const R: usize, const PEERS: usize> core::fmt::Debug for Connectivity<P, R, PEERS> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Connectivity")
            .field("class", &self.class)
            .field("home", &self.net.home())
            .finish_non_exhaustive()
    }
}

pub(super) fn push<T: Copy, const N: usize>(q: &mut [Option<T>; N], v: T) -> bool {
    match q.iter_mut().find(|s| s.is_none()) {
        Some(s) => {
            *s = Some(v);
            true
        }
        None => false,
    }
}

pub(super) fn pop<T: Copy, const N: usize>(q: &mut [Option<T>; N]) -> Option<T> {
    let first = q.iter().position(Option::is_some)?;
    let v = q.get_mut(first)?.take();
    q.get_mut(first..)?.rotate_left(1);
    v
}

impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
    /// A layer with no carrier open and no probe sent.
    pub fn new(cfg: Config<R>, prekey: PrekeyInfo, prov: P, seed: u64) -> Self {
        let mut shared = Shared {
            phone: cfg.phone,
            restarted: cfg.restarted,
            keep_learn: cfg.keep_learn,
            ..Shared::default()
        };
        shared.keep_fail = None;
        Self {
            me: cfg.me,
            identity: cfg.identity,
            prov,
            prekey,
            v6: cfg.v6,
            start: cfg.start,
            rly: core::array::from_fn(|i| Rly {
                cfg: cfg.relays.get(i).copied().flatten(),
                link: Link::new(),
                carrier: None,
                kind: Kind::Tcp,
                generation: 0,
                out: [0; OUT_LEN],
                out_len: 0,
                bbuf: [0; MAX_FRAME_LEN],
                bst: BatchState::new(),
                q: super::queue::HeldQueue::new(),
                keyreq: false,
                ta: AliasTable::new(),
                ra: AliasTable::new(),
                rides: false,
                etx: None,
                pong: false,
                reverify: false,
                drain_due: false,
            }),
            shared,
            net: Netcheck::new(),
            lookups: Lookups::new(),
            found: [None; FOUND],
            found_next: 0,
            peers: [None; PEERS],
            peers_next: 0,
            splices: Splices::new(),
            class: None,
            udp_any: false,
            local: [None; MAX_ADDRS],
            mapped: [None; 2],
            udp_q: [None; UDP_QUEUE],
            inbound: [None; INBOUND],
            io: [None; IO_QUEUE],
            notices: [None; NOTICES],
            duty: Duty::new(cfg.start),
            next_publish: 0,
            next_probe: cfg.start,
            scid: seed,
            sess: [None; SESSIONS],
            pending: super::dial::Pending::new(),
            first_dial: None,
            found_q: [None; 4],
            beacons: [None; LOCAL_PEERS],
            node_rtt: 0,
            node_tgr: 0,
            sign: super::signing::Signing::new(),
            evq: [None; 16],
            clock: cfg.start,
            dropped: 0,
        }
    }

    // ---- tables ----

    /// The relay with node id `id`.
    pub fn relay_of(&self, id: &NodeId) -> Option<usize> {
        self.rly.iter().position(|r| r.cfg.is_some_and(|c| c.id == *id))
    }

    /// The configuration of relay `i`.
    pub fn relay_cfg(&self, i: usize) -> Option<RelayCfg> {
        self.rly.get(i).and_then(|r| r.cfg)
    }

    fn relay_by_udp(&self, a: &SocketAddr) -> Option<usize> {
        self.rly.iter().position(|r| r.cfg.is_some_and(|c| c.udp == Some(*a)))
    }

    /// The position of `peer` in the table of peers named on relay paths, assigning one if needed.
    pub fn peer_slot(&mut self, peer: &NodeId) -> u16 {
        if let Some(i) = self.peers.iter().position(|p| p.as_ref() == Some(peer)) {
            return u16::try_from(i).unwrap_or(0);
        }
        let i = self.peers_next % PEERS.max(1);
        self.peers_next = (i + 1) % PEERS.max(1);
        if let Some(s) = self.peers.get_mut(i) {
            *s = Some(*peer);
        }
        u16::try_from(i).unwrap_or(0)
    }

    /// The synthetic address of the path through `relay` to `peer`.
    pub fn path_addr(&mut self, relay: usize, peer: &NodeId) -> SocketAddr {
        let slot = self.peer_slot(peer);
        relay_addr(self.v6, u8::try_from(relay).unwrap_or(0), slot)
    }

    /// The relay and peer a synthetic address names.
    pub fn path_parts(&self, a: &SocketAddr) -> Option<(usize, NodeId)> {
        let (r, p) = relay_parts(a)?;
        let peer = self.peers.get(usize::from(p)).copied().flatten()?;
        (usize::from(r) < R).then_some((usize::from(r), peer))
    }

    // ---- observation ----

    /// The reachability class the observations give, once they say anything.
    pub const fn class(&self) -> Option<Reach> {
        self.class
    }

    /// The home relay.
    pub const fn home(&self) -> Option<usize> {
        self.net.home()
    }

    /// Whether a UDP datagram was ever heard.
    pub const fn udp_heard(&self) -> bool {
        self.udp_any
    }

    /// The state of the carrier of `relay`.
    pub fn carrier_state(&self, relay: usize) -> State {
        self.rly.get(relay).map_or(State::Down, |r| r.link.state())
    }

    /// The generation of the carrier stream of `relay`: it changes when the carrier is reset.
    pub fn generation(&self, relay: usize) -> u64 {
        self.rly.get(relay).map_or(0, |r| r.generation)
    }

    /// The shared carrier state (the learned lease, the phone flag).
    pub const fn shared(&self) -> &Shared {
        &self.shared
    }

    /// Set the node's own addresses (the candidates it offers a peer, and what a record lists).
    pub fn set_local(&mut self, addrs: &[SocketAddr]) {
        self.local = [None; MAX_ADDRS];
        for (d, a) in self.local.iter_mut().zip(addrs) {
            *d = Some(*a);
        }
    }

    /// Set the external addresses of port mappings the host holds.
    pub fn set_mapped(&mut self, addrs: &[SocketAddr]) {
        self.mapped = [None; 2];
        for (d, a) in self.mapped.iter_mut().zip(addrs) {
            *d = Some(*a);
        }
    }

    /// The candidates this node offers a peer: reflexive addresses first, then local ones, at most 8.
    pub fn candidates(&self, out: &mut [SocketAddr; MAX_ADDRS]) -> usize {
        let mut n = self.net.reflexive_into(out);
        for a in self.local.iter().flatten() {
            if n < MAX_ADDRS
                && !out.get(..n).unwrap_or_default().contains(a)
                && let Some(d) = out.get_mut(n)
            {
                *d = *a;
                n += 1;
            }
        }
        n
    }

    pub(super) fn rtt(&self) -> u64 {
        self.net.best_rtt()
    }

    pub(super) fn notice(&mut self, n: Notice) {
        if !push(&mut self.notices, n) {
            self.dropped += 1;
        }
    }

    /// The next notice.
    pub fn poll_notice(&mut self) -> Option<Notice> {
        pop(&mut self.notices)
    }

    pub(super) fn update_class(&mut self, now: u64) {
        let mut local = [self.me_addr(); MAX_ADDRS];
        let mut nl = 0;
        for (d, a) in local.iter_mut().zip(self.local.iter().flatten()) {
            *d = *a;
            nl += 1;
        }
        let mut refl = [self.me_addr(); MAX_ADDRS];
        let nr = self.net.reflexive_into(&mut refl);
        let mut mapped = [self.me_addr(); 2];
        let mut nm = 0;
        for (d, a) in mapped.iter_mut().zip(self.mapped.iter().flatten()) {
            *d = *a;
            nm += 1;
        }
        let o = Observed {
            local: local.get(..nl).unwrap_or_default(),
            reflexive: refl.get(..nr).unwrap_or_default(),
            mapped: mapped.get(..nm).unwrap_or_default(),
            udp_heard: self.udp_any,
            since_probe: self.net.first_probe().map_or(0, |t| now.saturating_sub(t)),
            watchdog: super::link::dial_wait(self.rtt()),
        };
        let class = netcheck::classify(&o);
        if class != self.class
            && let Some(c) = class
        {
            self.class = Some(c);
            self.notice(Notice::Class(c));
            self.next_publish = now;
        }
    }

    const fn me_addr(&self) -> SocketAddr {
        SocketAddr::new(core::net::IpAddr::V4(core::net::Ipv4Addr::UNSPECIFIED), 0)
    }

    // ---- UDP ----

    pub(super) fn enqueue_udp_pub(&mut self, to: SocketAddr, d: &Datagram<'_>) -> bool {
        self.enqueue_udp(to, d)
    }

    pub(super) fn enqueue_raw(&mut self, to: SocketAddr, bytes: &[u8]) {
        let mut item = UdpItem {
            to,
            len: bytes.len(),
            data: [0; MAX_PACKET_LEN],
        };
        if let Some(d) = item.data.get_mut(..bytes.len()) {
            d.copy_from_slice(bytes);
            if !push(&mut self.udp_q, item) {
                self.dropped += 1;
            }
        }
    }

    fn enqueue_udp(&mut self, to: SocketAddr, d: &Datagram<'_>) -> bool {
        let mut item = UdpItem {
            to,
            len: 0,
            data: [0; MAX_PACKET_LEN],
        };
        let Ok(n) = d.encode(&mut item.data) else { return false };
        item.len = n;
        if push(&mut self.udp_q, item) {
            true
        } else {
            self.dropped += 1;
            false
        }
    }

    /// The next UDP datagram to send: copies it into `buf` and returns where to and how long.
    pub fn poll_udp(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        let item = pop(&mut self.udp_q)?;
        let dst = buf.get_mut(..item.len)?;
        dst.copy_from_slice(item.data.get(..item.len)?);
        Some((item.to, item.len))
    }

    /// A UDP datagram from `from` arrived. Returns true if it was a relay control datagram (handled here); false
    /// means it belongs to the endpoint. `data[0] >= 0x40` is always a transport packet.
    pub fn handle_udp(&mut self, now: u64, from: SocketAddr, data: &[u8]) -> bool {
        self.clock = self.clock.max(now);
        if data.first().is_none_or(|b| *b >= 0x40) {
            return false;
        }
        let Some(relay) = self.relay_by_udp(&from) else {
            return false;
        };
        let Ok(d) = Datagram::decode(data) else { return true };
        self.udp_any = true;
        self.shared.restarted = false;
        match d {
            Datagram::Qadr { nonce, addr } => {
                let before = self.net.home();
                if self.net.answered(now, relay, nonce, addr).is_some() {
                    self.after_answer(now, before);
                }
            }
            Datagram::DnsReply { peer, answer } => self.dns_answer(&peer, &answer),
            Datagram::Spl { src, flag: _, packet } => {
                self.splices.seen(now, u8::try_from(relay).unwrap_or(0), src, from);
                let virt = self.path_addr(relay, &src);
                self.deliver(virt, packet);
            }
            Datagram::Qad { .. } | Datagram::DnsQuery { .. } | Datagram::Sleep { .. } | Datagram::Spu { .. } => {}
        }
        true
    }

    fn after_answer(&mut self, now: u64, before: Option<usize>) {
        self.update_class(now);
        let home = self.net.home();
        if home != before {
            if let Some(h) = home {
                self.notice(Notice::Home(h));
                // The home carrier is dialed as soon as the home is known.
                let ctx = self.ctx(h);
                let act = self
                    .rly
                    .get_mut(h)
                    .and_then(|r| r.link.want_dial(now, &mut self.shared, &ctx));
                if let Some(a) = act {
                    self.act_pub(now, h, a);
                }
            }
            self.next_publish = now;
        }
    }

    pub(super) fn dns_answer_pub(&mut self, peer: &NodeId, answer: &DnsAnswer<'_>) {
        self.dns_answer(peer, answer);
    }

    fn dns_answer(&mut self, peer: &NodeId, answer: &DnsAnswer<'_>) {
        match super::lookup::verify(peer, answer) {
            Ok(Some(f)) => {
                self.lookups.answered(peer);
                let slot = self.found_next % FOUND;
                self.found_next = (slot + 1) % FOUND;
                if let Some(s) = self.found.get_mut(slot) {
                    *s = Some((*peer, f, self.clock));
                }
                let _ = push(&mut self.found_q, *peer);
                self.notice(Notice::Found(*peer));
            }
            Ok(None) => {
                self.lookups.answered(peer);
                // The wait of a pending dial is over: its first flight already went through the home relay.
                let _ = push(&mut self.found_q, *peer);
                self.notice(Notice::Missing(*peer));
            }
            Err(LookupError::TooLarge) => self.lookups.too_large(peer),
            Err(_) => {
                self.lookups.answered(peer);
                let _ = push(&mut self.found_q, *peer);
                self.notice(Notice::BadRecord(*peer));
            }
        }
    }

    /// The verified record found for `peer`, if a lookup produced one.
    pub fn found(&self, peer: &NodeId) -> Option<Found> {
        self.found
            .iter()
            .flatten()
            .find(|(p, _, _)| p == peer)
            .map(|(_, f, _)| *f)
    }

    /// The record found for `peer` unless it is stale: older than [`FOUND_TTL`] and listing no address (such a
    /// record only names a relay, and the relay may have changed).
    pub fn found_fresh(&self, now: u64, peer: &NodeId) -> Option<Found> {
        self.found
            .iter()
            .flatten()
            .find(|(p, _, _)| p == peer)
            .filter(|(_, f, at)| now.saturating_sub(*at) < FOUND_TTL || f.addrs().next().is_some())
            .map(|(_, f, _)| *f)
    }

    /// Forget the found record of `peer` (it was used).
    pub fn forget_found(&mut self, peer: &NodeId) {
        for s in &mut self.found {
            if s.as_ref().is_some_and(|(p, _, _)| p == peer) {
                *s = None;
            }
        }
    }

    /// Hand a packet that came from a relay to the endpoint's queue.
    pub(super) fn deliver(&mut self, from: SocketAddr, packet: &[u8]) {
        let mut item = Inbound {
            from,
            len: packet.len(),
            data: [0; MAX_PACKET_LEN],
        };
        let Some(dst) = item.data.get_mut(..packet.len()) else {
            return;
        };
        dst.copy_from_slice(packet);
        if !push(&mut self.inbound, item) {
            self.dropped += 1;
        }
    }

    /// The next packet for the endpoint: its synthetic source address, copied into `buf`.
    pub fn poll_inbound(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        let item = pop(&mut self.inbound)?;
        let dst = buf.get_mut(..item.len)?;
        dst.copy_from_slice(item.data.get(..item.len)?);
        Some((item.from, item.len))
    }

    // ---- address discovery and lookups ----

    /// Send a QAD probe to every relay with a UDP address.
    pub fn probe_all(&mut self, now: u64, env: &mut Env<'_, P>) {
        for i in 0..R {
            let Some(udp) = self.rly.get(i).and_then(|r| r.cfg).and_then(|c| c.udp) else {
                continue;
            };
            let Ok(nonce) = env.random::<8>() else { continue };
            if self.enqueue_udp(udp, &Datagram::Qad { nonce }) {
                self.net.probe_sent(now, i, nonce, self.udp_any);
            }
        }
    }

    /// How many lookups are outstanding.
    pub fn lookups_outstanding(&self) -> usize {
        self.lookups.len()
    }

    /// Ask for `peer`'s record. Picks UDP or the carrier by the rules of [`Lookups::ask`].
    pub fn lookup(&mut self, now: u64, peer: &NodeId) {
        let Some(home) = self
            .net
            .home()
            .or_else(|| self.rly.iter().position(|r| r.cfg.is_some()))
        else {
            return;
        };
        let carrier_open = self.rly.get(home).is_some_and(|r| r.link.is_open());
        // A thin node (reference round trip of the node: its handshake figures or its best address-discovery round
        // trip) repeats a query only after twice that.
        let rtt = self.node_rtt.max(self.net.best_rtt());
        let thin = (rtt >= super::dial::TG_SLOW).then_some(rtt);
        match self.lookups.ask(now, peer, self.udp_any, carrier_open, thin) {
            Ask::Skip | Ask::Later => {}
            Ask::Carrier => {
                self.frame_to(now, home, &Frame::DnsQuery { peer: *peer });
            }
            Ask::Udp { others } => {
                for i in 0..R {
                    if i != home && !others {
                        continue;
                    }
                    if let Some(udp) = self.rly.get(i).and_then(|r| r.cfg).and_then(|c| c.udp) {
                        self.enqueue_udp(udp, &Datagram::DnsQuery { peer: *peer });
                    }
                }
            }
        }
    }
}
