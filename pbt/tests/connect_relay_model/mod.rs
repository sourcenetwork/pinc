//! The relay role's reference model and its harness, for `connect_relay.rs`: the generated inputs (this file),
//! the model of the rules (`model.rs`) and the world that drives a relay beside the model and checks every step
//! (`world.rs`).
#![allow(dead_code, unused_imports)]

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

pub mod model;
pub mod world;



pub const SEC: u64 = 1_000_000_000;
pub const MS: u64 = 1_000_000;
/// The relay's clock at the start: a wall clock in nanoseconds, so sleep notices carry realistic milliseconds.
pub const T0: u64 = 1_700_000_000 * SEC;
pub const C: usize = 4;
pub const RS: usize = 3;
pub const MN: usize = 2;
pub const MB: usize = 1600;
pub type R = Relay<C, RS, MN, MB>;

/// Identities: 0..=5 attached nodes, 6 this relay, 7 and 8 peer relays the host may authenticate, 9 a relay it never
/// does, 10 another relay (a notice for it is useless here).
pub const CLIENTS: u8 = 6;
pub const ME: u8 = 6;
pub const IDS: usize = 11;
pub const OTHER_RELAY: u8 = 10;

thread_local! {
    pub static KEYS: Vec<Keypair> = (0..IDS)
        .map(|i| Keypair::from_seed(IdentityAlg::Ed25519, &[u8::try_from(i + 1).unwrap_or(1); 32]).expect("an Ed25519 seed"))
        .collect();
}

pub fn id(i: u8) -> NodeId {
    KEYS.with(|k| k[usize::from(i) % IDS].node_id())
}

pub type K = (u8, [u8; 32]);

pub fn k(n: &NodeId) -> K {
    (n.alg.tag(), n.bytes)
}

// ---------------------------------------------------------------------------------------------------------------
// Generated inputs

pub fn client() -> ephyra::BoxGen<u8> {
    gens::int(0u8..=CLIENTS - 1).boxed()
}

/// A destination: mostly an attached node, sometimes this relay, a peer relay, an unauthenticated relay or another.
pub fn target() -> ephyra::BoxGen<u8> {
    gens::frequency(vec![(5, client()), (2, gens::int(ME..=OTHER_RELAY).boxed())]).boxed()
}

pub fn peer() -> ephyra::BoxGen<u8> {
    gens::frequency(vec![(4, gens::int(7u8..=8).boxed()), (1, gens::constant(9u8).boxed())]).boxed()
}

/// Packet lengths, with the tunnel and mailbox edges: 1389 is the longest that fits a tunnel datagram.
pub fn plen() -> ephyra::BoxGen<u16> {
    let max = u16::try_from(MAX_PACKET_LEN).unwrap_or(1452);
    let tun = u16::try_from(MAX_TUNNEL_DATAGRAM - 35).unwrap_or(1389);
    gens::frequency(vec![
        (6, gens::int(9u16..=160).boxed()),
        (2, gens::int(1u16..=max).boxed()),
        (2, gens::pick_from(vec![1u16, 8, 9, tun, tun + 1, max - 1, max, 700, 760]).boxed()),
    ])
    .boxed()
}

pub fn alias() -> ephyra::BoxGen<u8> {
    gens::frequency(vec![(4, gens::int(0u8..=3).boxed()), (1, gens::int(0u8..=31).boxed())]).boxed()
}

pub fn dt() -> ephyra::BoxGen<u64> {
    gens::frequency(vec![
        (6, gens::pick_from(vec![0, MS, 999 * MS, SEC, 1500 * MS, 3 * SEC]).boxed()),
        (3, gens::pick_from(vec![10 * SEC, 15 * SEC + 1, 20 * SEC, 30 * SEC, 31 * SEC, 61 * SEC]).boxed()),
        (1, gens::pick_from(vec![600 * SEC, 1800 * SEC, rule::RECORD_TTL_NS, 86_400 * SEC]).boxed()),
        (1, gens::int(0u64..=700 * SEC).boxed()),
    ])
    .boxed()
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
pub struct RecSpec {
    #[ephyra(gen = gens::frequency(vec![(4, client()), (1, gens::int(ME..=OTHER_RELAY).boxed())]))]
    pub signer: u8,
    #[ephyra(gen = gens::frequency(vec![(3, gens::constant(ME).boxed()), (2, gens::int(7u8..=OTHER_RELAY).boxed()), (1, client())]))]
    pub home: u8,
    #[ephyra(gen = gens::int(0u8..=4))]
    pub seq: u8,
    #[ephyra(gen = gens::int(0u8..=3))]
    pub addrs: u8,
    #[ephyra(gen = gens::bool_with(0.12))]
    pub tamper: bool,
}

impl RecSpec {
    pub fn bytes(&self) -> Vec<u8> {
        signed_record(self.signer, self.home, u64::from(self.seq), self.addrs, self.tamper)
    }
}

pub fn signed_record(signer: u8, home: u8, seq: u64, addrs: u8, tamper: bool) -> Vec<u8> {
    let addrs: Vec<SocketAddr> =
        (0..addrs).map(|i| SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, signer, i)), 4000 + u16::from(i))).collect();
    let fields = RecordFields { home: id(home), seq, reach: Reach::Public, addrs: &addrs, hints: &[] };
    let mut out = vec![0u8; record::MAX_RECORD_LEN];
    let n = KEYS.with(|keys| record::sign(&keys[usize::from(signer)], &fields, &mut out)).expect("a record signs");
    out.truncate(n);
    if tamper && let Some(b) = out.last_mut() {
        *b ^= 1;
    }
    out
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
pub enum NoticeSpec {
    Fresh {
        #[ephyra(gen = gens::frequency(vec![(5, client()), (1, gens::int(ME..=OTHER_RELAY).boxed())]))]
        signer: u8,
        #[ephyra(gen = gens::bool_with(0.85))]
        for_me: bool,
        #[ephyra(gen = gens::frequency(vec![(4, gens::constant(0i64).boxed()), (2, gens::pick_from(vec![-1i64, 1, -9_999, 9_999, -10_000, 10_000, -500_000]).boxed())]))]
        skew_ms: i64,
        #[ephyra(gen = gens::bool_with(0.08))]
        tamper: bool,
    },
    /// Signed by the node the frame or datagram comes from, for this relay, on the relay's clock: what a suspending
    /// node sends.
    Mine,
    /// The bytes of an earlier notice of this run, sent again.
    Replay(#[ephyra(gen = gens::int(0u8..=7))] u8),
}

/// One edit of an encoding: what a hostile or broken sender could send in place of a valid one.
#[derive(Clone, Debug, ephyra::Arbitrary)]
pub struct Edit(
    #[ephyra(gen = gens::int(0u8..=4))] u8,
    #[ephyra(gen = gens::int(0u16..=1500))] u16,
    #[ephyra(gen = gens::int(0u8..=255))] u8,
);

pub fn apply(edits: &[Edit], mut b: Vec<u8>) -> Vec<u8> {
    for Edit(op, at, v) in edits {
        if b.is_empty() {
            b.push(*v);
            continue;
        }
        let at = usize::from(*at) % b.len();
        match op {
            0 => b[at] ^= 1 << (v % 8),
            1 => b[at] = *v,
            2 => b.truncate(at),
            3 => b.insert(at, *v),
            _ => b.push(*v),
        }
    }
    b
}

/// A frame a node sends on its carrier.
#[derive(Clone, Debug, ephyra::Arbitrary)]
pub enum CFrame {
    Ping,
    Pong,
    Send(#[ephyra(gen = target())] u8, #[ephyra(gen = gens::int(0u8..=255))] u8, #[ephyra(gen = plen())] u16),
    SendNew(#[ephyra(gen = target())] u8, #[ephyra(gen = alias())] u8, #[ephyra(gen = plen())] u16),
    SendAlias(#[ephyra(gen = alias())] u8, #[ephyra(gen = plen())] u16),
    SelfSend(#[ephyra(gen = plen())] u16),
    Publish(RecSpec),
    Dns(#[ephyra(gen = target())] u8),
    Sleep(NoticeSpec),
    /// A frame only a relay may send: RECV, RECV_NEW, RECV_ALIAS, SELFR, DNSR, FWD or SYNC.
    Forbidden(#[ephyra(gen = gens::int(0u8..=6))] u8, #[ephyra(gen = target())] u8, #[ephyra(gen = plen())] u16),
}

/// A frame a peer relay sends on its relay-to-relay session.
#[derive(Clone, Debug, ephyra::Arbitrary)]
pub enum PFrame {
    Ping,
    Pong,
    Forward(#[ephyra(gen = target())] u8, #[ephyra(gen = target())] u8, #[ephyra(gen = plen())] u16),
    Sync(RecSpec),
    /// A frame relays do not exchange: SEND, PUB, DNSQ, SELF or SLEEP.
    Forbidden(#[ephyra(gen = gens::int(0u8..=4))] u8, #[ephyra(gen = target())] u8, #[ephyra(gen = plen())] u16),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
pub enum DSpec {
    Qad(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64),
    Dns(#[ephyra(gen = target())] u8),
    Sleep(NoticeSpec),
    Spu(#[ephyra(gen = target())] u8, #[ephyra(gen = gens::int(0u8..=255))] u8, #[ephyra(gen = plen())] u16),
    /// QADR, DNSR or SPL: only a relay sends them.
    Unexpected(#[ephyra(gen = gens::int(0u8..=2))] u8, #[ephyra(gen = target())] u8),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
pub enum Op {
    Tick(#[ephyra(gen = dt())] u64, #[ephyra(gen = gens::bool_with(0.15))] bool),
    Open(#[ephyra(gen = client())] u8),
    Close(#[ephyra(gen = client())] u8, #[ephyra(gen = gens::bool_with(0.2))] bool),
    Frame(#[ephyra(gen = client())] u8, #[ephyra(gen = gens::bool_with(0.08))] bool, CFrame),
    Batch(#[ephyra(gen = client())] u8, #[ephyra(gen = gens::vec(ephyra::any::<CFrame>()).len(2..=5))] Vec<CFrame>),
    Mangled(#[ephyra(gen = client())] u8, CFrame, #[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(1..=3))] Vec<Edit>),
    Peer(#[ephyra(gen = peer())] u8, PFrame),
    PeerBatch(#[ephyra(gen = peer())] u8, #[ephyra(gen = gens::vec(ephyra::any::<PFrame>()).len(2..=4))] Vec<PFrame>),
    Dgram(#[ephyra(gen = gens::int(0u8..=3))] u8, #[ephyra(gen = gens::option(client()))] Option<u8>, DSpec),
    MangledDgram(
        #[ephyra(gen = gens::int(0u8..=3))] u8,
        #[ephyra(gen = gens::option(client()))] Option<u8>,
        DSpec,
        #[ephyra(gen = gens::vec(ephyra::any::<Edit>()).len(1..=3))] Vec<Edit>,
    ),
    Heard(#[ephyra(gen = client())] u8),
    UdpGone(#[ephyra(gen = client())] u8),
    Returned(#[ephyra(gen = client())] u8),
    Ready(#[ephyra(gen = client())] u8, #[ephyra(gen = gens::bool_with(0.7))] bool),
    AddPeer(#[ephyra(gen = gens::int(7u8..=8))] u8),
    RemovePeer(#[ephyra(gen = gens::int(7u8..=8))] u8),
    Local(#[ephyra(gen = target())] u8, #[ephyra(gen = plen())] u16),
    SetOwn(#[ephyra(gen = gens::int(0u8..=4))] u8),
    Restart,
    /// TETHER: the node sends its sleep notice (on its carrier or over UDP) and its carrier closes.
    Suspend(#[ephyra(gen = client())] u8, #[ephyra(gen = gens::bool_with(0.3))] bool),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
pub struct Setup {
    #[ephyra(gen = gens::pick_from(vec![400u64, 3000, 32 << 20]))]
    pub quota_bytes: u64,
    #[ephyra(gen = gens::pick_from(vec![SEC, 60 * SEC]))]
    pub window_ns: u64,
    #[ephyra(gen = gens::pick_from(vec![3 * SEC, 40 * SEC, 86_400 * SEC]))]
    pub session_ns: u64,
    #[ephyra(gen = gens::pick_from(vec![5 * SEC, 86_400 * SEC]))]
    pub mailbox_age_ns: u64,
    #[ephyra(gen = gens::int(0u64..=u64::MAX))]
    pub seed: u64,
}

pub fn case() -> impl Gen<Value = (Setup, Vec<Op>)> {
    (ephyra::any::<Setup>(), gens::vec(ephyra::any::<Op>()).len(1..=70))
}

