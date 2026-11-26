//! The reference model of the relay role's rules.
#![allow(unused_imports)]

use std::collections::{BTreeMap, BTreeSet};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};

use ephyra::prelude::*;
use pinc_connect::carrier::{BatchBuilder, DnsAnswer, Frame, MAX_FRAME_LEN, MAX_PACKET_LEN, Offer};
use pinc_connect::record::{self, Reach, Record, RecordFields};
use pinc_connect::relay::datagram::{Datagram, MAX_DNS_DATAGRAM, MAX_TUNNEL_DATAGRAM};
use pinc_connect::relay::sleep::{self, Notice, SKEW_MS};
use pinc_connect::relay::table::{Cache, Table};
use pinc_connect::relay::{
    CloseReason, Config, Effect, NodeState, Quota, RecordOrigin, Reject, Relay, Route, SessionId, Sink, Trace,
    UdpTarget, rule,
};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};

use super::*;

// ---------------------------------------------------------------------------------------------------------------
// The effects the relay emits, kept as owned values and normalised

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Fx {
    /// A packet delivered on a carrier (RECV, RECV_NEW or RECV_ALIAS with the alias resolved).
    Recv { to: K, src: K, flag: u8, body: Vec<u8> },
    /// The relay's own endpoint to a node on its carrier.
    SelfRecv { to: K, body: Vec<u8> },
    /// A packet down a member's UDP session.
    Spl { to: K, src: K, flag: u8, body: Vec<u8> },
    /// A packet to a peer relay.
    Forward { to: K, src: K, dst: K, flag: u8, body: Vec<u8> },
    /// A packet for the relay's own endpoint.
    Local { from: K, body: Vec<u8> },
    /// Any other frame on a carrier, encoded.
    CarrierCtl { to: K, frame: Vec<u8> },
    /// Any other frame to a peer relay, encoded.
    PeerCtl { to: K, frame: Vec<u8> },
    /// A datagram back to an address.
    Reply { to: SocketAddr, dgram: Vec<u8> },
    /// Any other datagram to a member.
    MemberDgram { to: K, dgram: Vec<u8> },
    Close { node: K, session: u64, replaced: bool },
}

pub enum Raw {
    Carrier(NodeId, Vec<u8>),
    Peer(NodeId, Vec<u8>),
    Udp(UdpTarget, Vec<u8>),
    Local(NodeId, Vec<u8>),
    Close(NodeId, SessionId, CloseReason),
    Wake(NodeId),
    Trace(Trace),
    /// A frame or datagram the relay emitted that does not encode.
    Unencodable(String),
}

#[derive(Default)]
pub struct Collect {
    pub got: Vec<Raw>,
    pub not_ready: BTreeSet<K>,
}

impl Sink for Collect {
    fn emit(&mut self, effect: Effect<'_>) {
        let mut buf = vec![0u8; MAX_FRAME_LEN];
        let raw = match effect {
            Effect::Carrier { to, frame } => match frame.encode(&mut buf) {
                Ok(n) => Raw::Carrier(to, buf[..n].to_vec()),
                Err(e) => Raw::Unencodable(format!("{frame:?}: {e:?}")),
            },
            Effect::PeerRelay { to, frame } => match frame.encode(&mut buf) {
                Ok(n) => Raw::Peer(to, buf[..n].to_vec()),
                Err(e) => Raw::Unencodable(format!("{frame:?}: {e:?}")),
            },
            Effect::Udp { to, datagram } => match datagram.encode(&mut buf) {
                Ok(n) => Raw::Udp(to, buf[..n].to_vec()),
                Err(e) => Raw::Unencodable(format!("{datagram:?}: {e:?}")),
            },
            Effect::Local { from, packet } => Raw::Local(from, packet.to_vec()),
            Effect::Close { node, session, reason } => Raw::Close(node, session, reason),
            Effect::Wake { node } => Raw::Wake(node),
            Effect::Trace(t) => Raw::Trace(t),
        };
        self.got.push(raw);
    }

    fn tunnel_ready(&self, node: &NodeId) -> bool {
        !self.not_ready.contains(&k(node))
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The reference model

pub struct Sess {
    pub id: u64,
    pub opened: u64,
    pub last_rx: u64,
    pub window_start: u64,
    pub window_bytes: u64,
    /// The relay's receive aliases of this session (node to relay).
    pub rx: [Option<K>; 32],
    /// The node's view of the relay's aliases (relay to node), learnt from the frames delivered.
    pub seen: [Option<K>; 32],
}

#[derive(Clone, Copy)]
pub struct Sleeper {
    pub at: u64,
}

pub struct StoredRec {
    pub seq: u64,
    pub bytes: Vec<u8>,
    pub received: u64,
    pub home: K,
}

/// A packet the model expects routed into the mailbox: `(dst, src, flag, body)`.
pub type Mail = (K, K, u8, Vec<u8>);

/// What one sub-frame's handling returns: a result, or the mailbox's answer still to be read from the traces.
pub enum P {
    Done(Result<(), Reject>),
    Mail(usize),
}

#[derive(Default)]
pub struct Expect {
    pub fx: Vec<Fx>,
    pub rejected: Vec<(Reject, Option<K>)>,
    pub quota: Vec<K>,
    pub stored: Vec<(K, u64, RecordOrigin)>,
    pub mail: Vec<Mail>,
    /// The call may release held mail (and count one refused hand-over per member).
    pub releases: bool,
}

pub struct Model {
    pub cfg: Config,
    /// Model the table of gone nodes with the code's capacity (a full table forgets the close) instead of as the
    /// module doc states it.
    pub gone_cap: Option<usize>,
    pub now: u64,
    pub sessions: BTreeMap<K, Sess>,
    /// The sessions as the relay's table holds them, so the sweep visits them in the relay's order.
    pub order: Table<(), C>,
    pub next_session: u64,
    pub gone: BTreeMap<K, u64>,
    pub sleeping: BTreeMap<K, Sleeper>,
    pub udp: BTreeMap<K, u64>,
    pub peers: Vec<K>,
    pub fwd_back: BTreeMap<usize, (K, K, u64)>,
    pub fwd_slots: Cache<(), C>,
    pub records: BTreeMap<K, StoredRec>,
    pub last_sweep: u64,
    pub next_ping: u64,
    pub next_publish: Option<u64>,
    pub not_ready: BTreeSet<K>,
    /// Bodies the mailbox stored, per member, in arrival order, until handed over: `(arrival, src, flag, body)`.
    pub held: BTreeMap<K, Vec<(u64, K, u8, Vec<u8>)>>,
    pub held_seq: u64,
    pub notices: Vec<Vec<u8>>,
    pub rejected_seen: u64,
    pub quota_seen: u64,
}

impl Model {
    pub fn new(cfg: Config, gone_cap: Option<usize>) -> Self {
        Self {
            cfg,
            gone_cap,
            now: T0,
            sessions: BTreeMap::new(),
            order: Table::new(cfg.seed),
            next_session: 0,
            gone: BTreeMap::new(),
            sleeping: BTreeMap::new(),
            udp: BTreeMap::new(),
            peers: Vec::new(),
            fwd_back: BTreeMap::new(),
            fwd_slots: Cache::new(cfg.seed),
            records: BTreeMap::new(),
            last_sweep: 0,
            next_ping: 0,
            next_publish: None,
            not_ready: BTreeSet::new(),
            held: BTreeMap::new(),
            held_seq: 0,
            notices: Vec::new(),
            rejected_seen: 0,
            quota_seen: 0,
        }
    }

    pub fn me(&self) -> K {
        k(&self.cfg.me)
    }

    pub fn gone_insert(&mut self, n: K, at: u64) {
        let room = self.gone_cap.is_none_or(|cap| self.gone.len() < cap);
        if self.gone.contains_key(&n) || room {
            self.gone.insert(n, at);
        }
    }

    pub fn reject(&self, e: &mut Expect, r: Reject, n: Option<K>) -> P {
        e.rejected.push((r, n));
        P::Done(Err(r))
    }

    pub fn fresh_udp(&self, n: &K) -> bool {
        self.udp.get(n).is_some_and(|h| self.now.saturating_sub(*h) < rule::HUB_TUNNEL_FRESH_NS)
    }

    pub fn tunnel_ok(&self, dst: &K, len: usize) -> bool {
        self.fresh_udp(dst) && !self.not_ready.contains(dst) && len > 0 && 35 + len <= MAX_TUNNEL_DATAGRAM
    }

    pub fn fwd_get(&self, dst: &NodeId) -> Option<(K, u64)> {
        let b = self.fwd_slots.bucket_of(dst);
        self.fwd_back.get(&b).filter(|(n, _, _)| *n == k(dst)).map(|(_, via, at)| (*via, *at))
    }

    /// The routing rules of `relay::route`, in order.
    pub fn route(&mut self, e: &mut Expect, src: &NodeId, dst: &NodeId, flag: u8, packet: &[u8], from_peer: bool) -> P {
        let (s, d) = (k(src), k(dst));
        if d == self.me() {
            e.fx.push(Fx::Local { from: s, body: packet.to_vec() });
            return P::Done(Ok(()));
        }
        if let Some(sess) = self.sessions.get(&d) {
            let stale = self.now.saturating_sub(sess.last_rx) > rule::TUNNEL_STALE_NS;
            e.fx.push(Fx::Recv { to: d, src: s, flag, body: packet.to_vec() });
            if stale && self.tunnel_ok(&d, packet.len()) {
                e.fx.push(Fx::Spl { to: d, src: s, flag, body: packet.to_vec() });
            }
            return P::Done(Ok(()));
        }
        if self.tunnel_ok(&d, packet.len()) {
            e.fx.push(Fx::Spl { to: d, src: s, flag, body: packet.to_vec() });
            return P::Done(Ok(()));
        }
        if self.sleeping.contains_key(&d) {
            e.mail.push((d, s, flag, packet.to_vec()));
            return P::Mail(e.mail.len() - 1);
        }
        if from_peer {
            return self.reject(e, Reject::NoRoute, Some(s));
        }
        let me = self.me();
        let back = self
            .fwd_get(dst)
            .filter(|(via, at)| self.now.saturating_sub(*at) < rule::FWD_BACK_NS && *via != me)
            .map(|(via, _)| via);
        let home = back.or_else(|| self.records.get(&d).map(|r| r.home)).filter(|h| *h != me);
        let Some(home) = home else {
            return self.reject(e, Reject::NoRoute, Some(s));
        };
        if !self.peers.contains(&home) {
            return self.reject(e, Reject::NoPeerSession, Some(s));
        }
        e.fx.push(Fx::Forward { to: home, src: s, dst: d, flag, body: packet.to_vec() });
        P::Done(Ok(()))
    }

    pub fn lookup(&self, peer: &K) -> Option<&[u8]> {
        self.records
            .get(peer)
            .filter(|r| self.now.saturating_sub(r.received) < rule::RECORD_TTL_NS)
            .map(|r| r.bytes.as_slice())
    }

    pub fn answer<'a>(&'a self, peer: &K, max: usize) -> DnsAnswer<'a> {
        match self.lookup(peer) {
            None => DnsAnswer::Absent,
            Some(r) if r.len() > max => DnsAnswer::TooLarge,
            Some(r) => DnsAnswer::Record(r),
        }
    }

    /// `Relay::store`: verify, check the owner, then the sequence rule.
    pub fn store(&mut self, e: &mut Expect, bytes: &[u8], origin: RecordOrigin, owner: Option<K>) -> P {
        let rec = match Record::parse_verified(bytes) {
            Ok(r) => r,
            Err(err) => return self.reject(e, Reject::BadRecord(err), owner),
        };
        let node = k(&rec.node);
        if owner.is_some_and(|o| o != node) {
            return self.reject(e, Reject::WrongOwner, owner);
        }
        let now = self.now;
        if let Some(s) = self.records.get_mut(&node) {
            if rec.seq < s.seq || (rec.seq == s.seq && s.bytes != bytes) {
                return self.reject(e, Reject::StaleRecord, Some(node));
            }
            if rec.seq == s.seq {
                s.received = now;
                return P::Done(Ok(()));
            }
        } else if self.records.len() >= RS {
            return self.reject(e, Reject::StoreFull, Some(node));
        }
        self.records.insert(node, StoredRec { seq: rec.seq, bytes: bytes.to_vec(), received: now, home: k(&rec.home) });
        e.stored.push((node, rec.seq, origin));
        P::Done(Ok(()))
    }

    pub fn replicate(&self, e: &mut Expect, bytes: &[u8]) {
        for p in &self.peers {
            e.fx.push(Fx::PeerCtl { to: *p, frame: enc(&Frame::Sync { record: bytes }) });
        }
    }

    /// `Relay::sleep_notice`.
    pub fn sleep(&mut self, e: &mut Expect, bytes: &[u8], sender: Option<K>) -> P {
        let n = match Notice::parse(bytes) {
            Ok(n) => n,
            Err(err) => return self.reject(e, Reject::BadSleep(err), sender),
        };
        let node = k(&n.node);
        if sender.is_some_and(|s| s != node) {
            return self.reject(e, Reject::BadSleep(sleep::SleepError::WrongSender), Some(node));
        }
        if (self.now / MS).abs_diff(n.ts_ms) >= SKEW_MS {
            return self.reject(e, Reject::BadSleep(sleep::SleepError::Skew), Some(node));
        }
        if !self.sessions.contains_key(&node) && !self.gone.contains_key(&node) {
            return self.reject(e, Reject::BadSleep(sleep::SleepError::UnknownNode), Some(node));
        }
        if let Err(err) = n.verify(&self.cfg.me) {
            return self.reject(e, Reject::BadSleep(err), Some(node));
        }
        if !self.sleeping.contains_key(&node) && self.sleeping.len() >= C {
            return self.reject(e, Reject::SessionsFull, Some(node));
        }
        self.sleeping.insert(node, Sleeper { at: self.now });
        P::Done(Ok(()))
    }

    /// `Relay::client_frame` for one frame (not a batch) of an open, current session.
    pub fn client_frame(&mut self, e: &mut Expect, node: &NodeId, f: &Frame<'_>) -> P {
        let n = k(node);
        let weight = f.packet().map_or(0, <[u8]>::len)
            + match f {
                Frame::Publish { record } | Frame::Sleep { notice: record } => record.len(),
                _ => 0,
            };
        if weight > 0 {
            let q = self.cfg.quota;
            let now = self.now;
            let Some(s) = self.sessions.get_mut(&n) else { return P::Done(Err(Reject::StaleSession)) };
            if now.saturating_sub(s.window_start) >= q.window_ns {
                s.window_start = now;
                s.window_bytes = 0;
            }
            let next = s.window_bytes.saturating_add(weight as u64);
            if next > q.bytes {
                e.quota.push(n);
                return P::Done(Err(Reject::Quota));
            }
            s.window_bytes = next;
        }
        match *f {
            Frame::Send { dst, flag, packet } => self.route(e, node, &dst, flag, packet, false),
            Frame::SendNew { dst, alias, flag, packet } => {
                if let Some(slot) = self.sessions.get_mut(&n).and_then(|s| s.rx.get_mut(usize::from(alias))) {
                    *slot = Some(k(&dst));
                }
                self.route(e, node, &dst, flag, packet, false)
            },
            Frame::SendAlias { alias, flag, packet } => {
                let dst = self.sessions.get(&n).and_then(|s| s.rx.get(usize::from(alias)).copied().flatten());
                match dst {
                    Some(d) => self.route(e, node, &node_of(d), flag, packet, false),
                    None => self.reject(e, Reject::UnknownAlias, Some(n)),
                }
            },
            Frame::SelfSend { packet } => {
                e.fx.push(Fx::Local { from: n, body: packet.to_vec() });
                P::Done(Ok(()))
            },
            Frame::Publish { record } => {
                let p = self.store(e, record, RecordOrigin::Publish, Some(n));
                if matches!(p, P::Done(Ok(()))) {
                    self.replicate(e, record);
                }
                p
            },
            Frame::Ping => {
                e.fx.push(Fx::CarrierCtl { to: n, frame: enc(&Frame::Pong) });
                P::Done(Ok(()))
            },
            Frame::Pong => P::Done(Ok(())),
            Frame::DnsQuery { peer } => {
                let frame = enc(&Frame::DnsReply { peer, answer: self.answer(&k(&peer), MAX_FRAME_LEN) });
                e.fx.push(Fx::CarrierCtl { to: n, frame });
                P::Done(Ok(()))
            },
            Frame::Sleep { notice } => self.sleep(e, notice, Some(n)),
            _ => self.reject(e, Reject::UnexpectedFrame, Some(n)),
        }
    }

    pub fn peer_frame(&mut self, e: &mut Expect, from: &NodeId, f: &Frame<'_>) -> Vec<P> {
        let p = k(from);
        if !self.peers.contains(&p) {
            return vec![self.reject(e, Reject::Unauthenticated, Some(p))];
        }
        match *f {
            Frame::Forward { src, dst, flag, packet } => {
                if !self.sessions.contains_key(&k(&src)) {
                    let b = self.fwd_slots.bucket_of(&src);
                    self.fwd_back.insert(b, (k(&src), p, self.now));
                }
                vec![self.route(e, &src, &dst, flag, packet, true)]
            },
            Frame::Sync { record } => vec![self.store(e, record, RecordOrigin::Replica, None)],
            Frame::Ping => {
                e.fx.push(Fx::PeerCtl { to: p, frame: enc(&Frame::Pong) });
                vec![P::Done(Ok(()))]
            },
            Frame::Pong => vec![P::Done(Ok(()))],
            Frame::Batch(b) => b.frames().flat_map(|sub| self.peer_frame(e, from, &sub)).collect(),
            _ => vec![self.reject(e, Reject::UnexpectedFrame, Some(p))],
        }
    }

    pub fn stamp(&mut self, n: K) -> bool {
        if self.udp.contains_key(&n) || self.udp.len() < C {
            self.udp.insert(n, self.now);
            return true;
        }
        false
    }

    pub fn timeout(&mut self, e: &mut Expect) {
        let now = self.now;
        if self.next_publish.is_some_and(|t| now >= t) {
            self.next_publish = now.checked_add(rule::RECORD_REPUBLISH_NS);
            let me = self.me();
            if let Some(r) = self.records.get_mut(&me) {
                r.received = now;
                let bytes = r.bytes.clone();
                self.replicate(e, &bytes);
            }
        }
        if now >= self.next_ping {
            self.next_ping = now.saturating_add(rule::CLIENT_PING_NS);
            for n in self.sessions.keys() {
                e.fx.push(Fx::CarrierCtl { to: *n, frame: enc(&Frame::Ping) });
            }
        }
        if now.saturating_sub(self.last_sweep) < rule::SWEEP_NS {
            return;
        }
        self.last_sweep = now;
        let limit = self.cfg.quota.session_ns;
        let mut expired: Vec<K> = Vec::new();
        let Self { order, sessions, .. } = self;
        order.retain(|n, ()| {
            let keep = sessions.get(&k(n)).is_none_or(|s| now.saturating_sub(s.opened) < limit);
            if !keep && !expired.contains(&k(n)) {
                expired.push(k(n));
            }
            keep
        });
        for n in expired {
            let s = self.sessions.remove(&n).map_or(0, |s| s.id);
            self.gone_insert(n, now);
            e.fx.push(Fx::Close { node: n, session: s, replaced: false });
        }
        self.gone.retain(|_, at| now.saturating_sub(*at) < rule::GONE_TTL_NS);
        self.sleeping.retain(|_, s| now.saturating_sub(s.at) < rule::GONE_TTL_NS);
        self.records.retain(|_, r| now.saturating_sub(r.received) < rule::RECORD_TTL_NS);
    }

    pub fn next_deadline(&self) -> u64 {
        let sweep = self.last_sweep.saturating_add(rule::SWEEP_NS).min(self.next_ping);
        self.next_publish.map_or(sweep, |p| sweep.min(p))
    }

    pub fn state(&self, n: &K) -> NodeState {
        if self.sessions.contains_key(n) {
            return NodeState::Open;
        }
        match self.gone.get(n) {
            Some(&since) => NodeState::Gone {
                since,
                asleep: self.sleeping.get(n).is_some_and(|s| s.at >= since.saturating_sub(rule::SLEEP_WIN_NS)),
            },
            None => NodeState::Unknown,
        }
    }
}

pub fn node_of(key: K) -> NodeId {
    (0..u8::try_from(IDS).unwrap_or(11)).map(id).find(|n| k(n) == key).unwrap_or(NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: key.1,
    })
}

pub fn enc(f: &Frame<'_>) -> Vec<u8> {
    let mut b = vec![0u8; MAX_FRAME_LEN];
    let n = f.encode(&mut b).expect("a frame the model builds encodes");
    b.truncate(n);
    b
}

pub fn denc(d: &Datagram<'_>) -> Vec<u8> {
    let mut b = vec![0u8; MAX_FRAME_LEN];
    let n = d.encode(&mut b).expect("a datagram the model builds encodes");
    b.truncate(n);
    b
}

pub fn addr(i: u8) -> SocketAddr {
    match i {
        0 => SocketAddr::new(IpAddr::V4(Ipv4Addr::new(198, 51, 100, 7)), 40_000),
        1 => SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 9)), 1),
        2 => SocketAddr::new(IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1)), 65_535),
        _ => SocketAddr::new(IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 1, 2, 3, 4, 5, 6)), 443),
    }
}

