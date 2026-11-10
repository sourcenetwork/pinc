//! A deterministic in-memory network for connection tests.
//!
//! [`Link`] carries datagrams between two endpoints over one or more routes. Each direction of a route has its own
//! one-way delay, jitter, loss rate, duplication, reordering, datagram size limit and bandwidth cap, and draws its
//! randomness from a seeded [`SplitMix64`], so a run repeats exactly. A direction is a first-in, first-out queue:
//! jitter delays a datagram but never lets it overtake the one sent ahead of it (real paths reorder through
//! multipath, link aggregation or link-layer recovery, not through queue jitter). Reordering is explicit
//! ([`Params::reorder`]), or [`Params::unordered_jitter`] for a stress test of independent per-datagram delays.
//! [`Node`] wraps a connection with its provider, keys and a log of what happened; [`Net`] pumps two nodes on virtual
//! time until nothing is left to do or a deadline passes.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::needless_pass_by_value,
    clippy::trivially_copy_pass_by_ref,
    clippy::struct_excessive_bools,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::must_use_candidate,
    clippy::return_self_not_must_use,
    clippy::new_without_default
)]

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};

use vinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use vinc_crypto::{Aead, Capabilities, CryptoError, Drbg, IdentityAlg, Keypair, Provider, Secret, Software};
use vinc_security::{
    AlpnList, ClientTickets, Env, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys, SoftPrekeys,
    TicketBatch,
};
use vinc_transport::conn::{
    ClientParams, CloseReason, Config, Connection, Drop, Event, PathId, PathInfo, Resources, ServerParams, Transmit,
};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, RecvStatus, Streams};

use crate::SplitMix64;

/// [`Software`] with a chosen answer to "does AES-GCM run on hardware", so both AEADs are testable anywhere.
#[derive(Debug, Clone, Copy)]
pub struct Caps(pub Software, pub bool);

impl Provider for Caps {
    type AeadKey = <Software as Provider>::AeadKey;
    type HpKey = <Software as Provider>::HpKey;
    type X25519Secret = <Software as Provider>::X25519Secret;
    type KemEncapsKey = <Software as Provider>::KemEncapsKey;
    type KemDecapsKey = <Software as Provider>::KemDecapsKey;
    type KemCiphertext = <Software as Provider>::KemCiphertext;

    fn capabilities(&self) -> Capabilities {
        Capabilities {
            aes_gcm_hw: self.1,
            chacha20_simd: false,
        }
    }
    fn aead_key(&self, alg: Aead, key: &[u8]) -> Result<Self::AeadKey, CryptoError> {
        self.0.aead_key(alg, key)
    }
    fn seal(
        &self,
        key: &Self::AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
    ) -> Result<[u8; Aead::TAG_LEN], CryptoError> {
        self.0.seal(key, nonce, aad, buf)
    }
    fn open(
        &self,
        key: &Self::AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
        tag: &[u8; Aead::TAG_LEN],
    ) -> Result<(), CryptoError> {
        self.0.open(key, nonce, aad, buf, tag)
    }
    fn hp_key(&self, alg: Aead, key: &[u8]) -> Result<Self::HpKey, CryptoError> {
        self.0.hp_key(alg, key)
    }
    fn hp_mask(&self, key: &Self::HpKey, sample: &[u8; Aead::SAMPLE_LEN]) -> [u8; Aead::MASK_LEN] {
        self.0.hp_mask(key, sample)
    }
    fn sha256(&self, data: &[u8]) -> [u8; 32] {
        self.0.sha256(data)
    }
    fn x25519_secret(&self, seed: &[u8; 32]) -> Self::X25519Secret {
        self.0.x25519_secret(seed)
    }
    fn x25519_public(&self, secret: &Self::X25519Secret) -> [u8; 32] {
        self.0.x25519_public(secret)
    }
    fn x25519_dh(&self, secret: &Self::X25519Secret, peer: &[u8; 32]) -> Result<Secret<32>, CryptoError> {
        self.0.x25519_dh(secret, peer)
    }
    fn kem_keygen(&self, d: &[u8; 32], z: &[u8; 32]) -> (Self::KemDecapsKey, Self::KemEncapsKey) {
        self.0.kem_keygen(d, z)
    }
    fn kem_encaps_key(&self, bytes: &[u8]) -> Result<Self::KemEncapsKey, CryptoError> {
        self.0.kem_encaps_key(bytes)
    }
    fn kem_encaps_key_bytes(&self, ek: &Self::KemEncapsKey) -> [u8; KEM_ENCAPS_KEY_LEN] {
        self.0.kem_encaps_key_bytes(ek)
    }
    fn kem_ciphertext(&self, bytes: &[u8]) -> Result<Self::KemCiphertext, CryptoError> {
        self.0.kem_ciphertext(bytes)
    }
    fn kem_ciphertext_bytes(&self, ct: &Self::KemCiphertext) -> [u8; KEM_CIPHERTEXT_LEN] {
        self.0.kem_ciphertext_bytes(ct)
    }
    fn kem_encapsulate(
        &self,
        ek: &Self::KemEncapsKey,
        m: &[u8; 32],
    ) -> Result<(Self::KemCiphertext, Secret<32>), CryptoError> {
        self.0.kem_encapsulate(ek, m)
    }
    fn kem_decapsulate(&self, dk: &Self::KemDecapsKey, ct: &Self::KemCiphertext) -> Result<Secret<32>, CryptoError> {
        self.0.kem_decapsulate(dk, ct)
    }
}

/// Run `f` on a thread with a large stack: connections and key material are large values.
pub fn big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// One direction of a route.
#[derive(Debug, Clone, Copy)]
pub struct Params {
    pub delay_ns: u64,
    pub jitter_ns: u64,
    /// Loss probability in parts per million.
    pub loss_ppm: u32,
    pub dup_ppm: u32,
    /// Probability (ppm) that a datagram is held back by `reorder_ns`.
    pub reorder_ppm: u32,
    pub reorder_ns: u64,
    /// Each datagram draws its jitter independently and may overtake earlier ones (off: the queue keeps its order).
    pub unordered: bool,
    /// Datagrams longer than this are dropped.
    pub mtu: usize,
    /// Bits per second; 0 means unlimited.
    pub bps: u64,
    /// Longest queue behind the bandwidth cap before tail drop.
    pub queue_ns: u64,
}

impl Params {
    /// A clean link with the given one-way delay.
    pub fn new(delay_ns: u64) -> Self {
        Self {
            delay_ns,
            jitter_ns: 0,
            loss_ppm: 0,
            dup_ppm: 0,
            reorder_ppm: 0,
            reorder_ns: 0,
            unordered: false,
            mtu: 65_535,
            bps: 0,
            queue_ns: 200_000_000,
        }
    }
    pub fn loss(mut self, percent: f64) -> Self {
        self.loss_ppm = (percent * 10_000.0) as u32;
        self
    }
    pub fn dup(mut self, percent: f64) -> Self {
        self.dup_ppm = (percent * 10_000.0) as u32;
        self
    }
    pub fn reorder(mut self, percent: f64, extra_ns: u64) -> Self {
        self.reorder_ppm = (percent * 10_000.0) as u32;
        self.reorder_ns = extra_ns;
        self
    }
    /// Up to `ns` of extra delay per datagram, keeping the queue's order.
    pub fn jitter(mut self, ns: u64) -> Self {
        self.jitter_ns = ns;
        self
    }
    /// Up to `ns` of extra delay drawn independently per datagram, so datagrams sent within `ns` of each other arrive
    /// in any order (a stress model; no single real queue does this).
    pub fn unordered_jitter(mut self, ns: u64) -> Self {
        self.jitter_ns = ns;
        self.unordered = true;
        self
    }
    pub fn mtu(mut self, mtu: usize) -> Self {
        self.mtu = mtu;
        self
    }
    pub fn bandwidth(mut self, bps: u64) -> Self {
        self.bps = bps;
        self
    }
}

#[derive(Debug)]
struct Item {
    at: u64,
    seq: u64,
    data: Vec<u8>,
}
impl PartialEq for Item {
    fn eq(&self, o: &Self) -> bool {
        (self.at, self.seq) == (o.at, o.seq)
    }
}
impl Eq for Item {}
impl PartialOrd for Item {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Item {
    fn cmp(&self, o: &Self) -> Ordering {
        (o.at, o.seq).cmp(&(self.at, self.seq))
    }
}

/// One direction: parameters, randomness and the datagrams in flight.
#[derive(Debug)]
pub struct Dir {
    pub p: Params,
    rng: SplitMix64,
    heap: BinaryHeap<Item>,
    seq: u64,
    free_at: u64,
    last_at: u64,
    drop_next: u32,
    drop_index: Option<u64>,
    pub sent: u64,
    pub dropped: u64,
    pub delivered: u64,
}

impl Dir {
    fn new(p: Params, seed: u64) -> Self {
        Self {
            p,
            rng: SplitMix64::new(seed),
            heap: BinaryHeap::new(),
            seq: 0,
            free_at: 0,
            last_at: 0,
            drop_next: 0,
            drop_index: None,
            sent: 0,
            dropped: 0,
            delivered: 0,
        }
    }
    fn draw(&mut self, ppm: u32) -> bool {
        ppm > 0 && (self.rng.next_u64() % 1_000_000) < u64::from(ppm)
    }
    fn send(&mut self, now: u64, data: &[u8]) {
        self.sent += 1;
        if self.drop_index == Some(self.sent) {
            self.dropped += 1;
            return;
        }
        if self.drop_next > 0 {
            self.drop_next -= 1;
            self.dropped += 1;
            return;
        }
        if data.len() > self.p.mtu || self.draw(self.p.loss_ppm) {
            self.dropped += 1;
            return;
        }
        let mut at = now;
        if let Some(tx_ns) = (data.len() as u64 * 8 * 1_000_000_000).checked_div(self.p.bps) {
            let start = self.free_at.max(now);
            if start - now > self.p.queue_ns {
                self.dropped += 1;
                return;
            }
            self.free_at = start + tx_ns;
            at = self.free_at;
        }
        let jitter = if self.p.jitter_ns > 0 {
            self.rng.next_u64() % self.p.jitter_ns
        } else {
            0
        };
        at += self.p.delay_ns + jitter;
        if !self.p.unordered {
            at = at.max(self.last_at);
            self.last_at = at;
        }
        if self.draw(self.p.reorder_ppm) {
            at += self.p.reorder_ns;
        }
        self.push(at, data.to_vec());
        if self.draw(self.p.dup_ppm) {
            let extra = 1 + self.rng.next_u64() % 1_000_000;
            self.push(at + extra, data.to_vec());
        }
    }
    fn push(&mut self, at: u64, data: Vec<u8>) {
        self.seq += 1;
        self.heap.push(Item {
            at,
            seq: self.seq,
            data,
        });
    }
    /// Drop only the `k`th datagram (counting from 1) sent in this direction.
    pub fn drop_index(&mut self, k: u64) {
        self.drop_index = Some(k);
    }
    /// Drop the next `n` datagrams sent in this direction.
    pub fn drop_next(&mut self, n: u32) {
        self.drop_next = n;
    }
    fn next_at(&self) -> Option<u64> {
        self.heap.peek().map(|i| i.at)
    }
    fn pop(&mut self, now: u64) -> Option<Vec<u8>> {
        if self.heap.peek().is_some_and(|i| i.at <= now) {
            self.delivered += 1;
            return self.heap.pop().map(|i| i.data);
        }
        None
    }
}

/// A route between the endpoints: `a` is how A names it, `b` how B names it.
#[derive(Debug)]
pub struct Route {
    pub a: PathId,
    pub b: PathId,
    pub ab: Dir,
    pub ba: Dir,
    pub up: bool,
}

/// The network between endpoints A and B.
#[derive(Debug)]
pub struct Link {
    pub routes: Vec<Route>,
    seed: u64,
}

impl Link {
    /// One route, named 1 by A and 2 by B, symmetric.
    pub fn new(seed: u64, p: Params) -> Self {
        let mut l = Self {
            routes: Vec::new(),
            seed,
        };
        l.add_route(PathId(1), PathId(2), p, p);
        l
    }
    pub fn add_route(&mut self, a: PathId, b: PathId, ab: Params, ba: Params) {
        let n = self.routes.len() as u64;
        self.routes.push(Route {
            a,
            b,
            ab: Dir::new(ab, self.seed ^ (n * 2 + 1)),
            ba: Dir::new(ba, self.seed ^ (n * 2 + 2)),
            up: true,
        });
    }
    pub fn route(&mut self, a: PathId) -> &mut Route {
        self.routes.iter_mut().find(|r| r.a == a).unwrap()
    }
    /// Set the parameters of both directions of a route.
    pub fn set(&mut self, a: PathId, ab: Params, ba: Params) {
        let r = self.route(a);
        r.ab.p = ab;
        r.ba.p = ba;
    }
    /// A's datagram to the route A calls `a`.
    pub fn send_a(&mut self, now: u64, a: PathId, data: &[u8]) {
        if let Some(r) = self.routes.iter_mut().find(|r| r.a == a && r.up) {
            r.ab.send(now, data);
        }
    }
    /// B's datagram to the route B calls `b`.
    pub fn send_b(&mut self, now: u64, b: PathId, data: &[u8]) {
        if let Some(r) = self.routes.iter_mut().find(|r| r.b == b && r.up) {
            r.ba.send(now, data);
        }
    }
    pub fn next_at(&self) -> Option<u64> {
        self.routes
            .iter()
            .flat_map(|r| [r.ab.next_at(), r.ba.next_at()])
            .flatten()
            .min()
    }
    fn pop_b(&mut self, now: u64) -> Option<(PathId, Vec<u8>)> {
        self.routes.iter_mut().find_map(|r| r.ab.pop(now).map(|d| (r.b, d)))
    }
    fn pop_a(&mut self, now: u64) -> Option<(PathId, Vec<u8>)> {
        self.routes.iter_mut().find_map(|r| r.ba.pop(now).map(|d| (r.a, d)))
    }
    /// NAT rebinding: B now sees A's datagrams on the route `a` as coming from `new_b`.
    pub fn rebind(&mut self, a: PathId, new_b: PathId) {
        self.route(a).b = new_b;
    }
}

pub const CHUNKS: usize = 1024;
pub const PK: usize = 8;
pub const TK: usize = 512;
pub type Stores = ResponderStores<PK, TK>;
/// Chunk-ring slots per stream of the default table: it caps the granted window at 4 MiB.
pub const RING: usize = 257;
pub type Table<const C: usize = RING> = Streams<NoSource, 64, C>;
pub type Conn<'a, const C: usize = RING> = Connection<'a, Caps, NoSource, 64, C, 512, 4>;

/// Storage a connection borrows: its stream table, its loss average and its pool.
pub struct Store<const C: usize = RING> {
    pub streams: Box<Table<C>>,
    pub loss: LossEstimate,
    pub pool: Option<BufferPool<'static>>,
}

impl Store {
    pub fn new(client: bool) -> Self {
        Self::with_chunks(client, CHUNKS)
    }
    pub fn with_chunks(client: bool, chunks: usize) -> Self {
        Self::with_stream(chunks, &stream::Config::new(client))
    }
    /// A store whose stream table is built from `cfg`.
    pub fn with_stream(chunks: usize, cfg: &stream::Config) -> Self {
        Self::sized(chunks, cfg)
    }
}

impl<const C: usize> Store<C> {
    /// A store with `C` chunk-ring slots per stream, whose table is built from `cfg`.
    pub fn sized(chunks: usize, cfg: &stream::Config) -> Self {
        let pool = BufferPool::new_boxed(chunks);
        let streams = Box::new(Table::<C>::new(cfg, &pool));
        Self {
            streams,
            loss: LossEstimate::new(),
            pool: Some(BufferPool::new_boxed(chunks)),
        }
    }
    pub fn resources(&mut self) -> Resources<'_, NoSource, 64, C> {
        Resources {
            pool: self.pool.take().unwrap(),
            streams: &mut self.streams,
            loss: &self.loss,
        }
    }
}

/// An owned record of an event.
#[derive(Debug, Clone, PartialEq)]
pub enum Rec {
    Connected(bool),
    Opened(u64),
    Readable(u64),
    Writable(u64),
    OpenReady,
    Reset(u64, u64),
    Stopped(u64, u64),
    Datagram,
    Extension(u64, Vec<u8>),
    ExtensionUndeliverable(u64, usize),
    PathValidated(PathId),
    PathFailed(PathId),
    PeerAsleep,
    PeerAwake,
    WakeUnanswered,
    Tickets,
    Ready,
    Closed(CloseReason),
}

pub const ALPN: &[u8] = b"vinc/1";

/// A key answer computed but not yet delivered.
pub enum Deferred {
    Signature(Vec<u8>),
    Secret(Secret<32>),
    Failed,
}

/// An endpoint under test: a connection, its provider and keys, and what it saw.
pub struct Node<'a, const C: usize = RING> {
    pub conn: Conn<'a, C>,
    pub prov: Caps,
    pub drbg: Drbg,
    pub kp: Keypair,
    pub prekeys: Option<SoftPrekeys<Caps>>,
    pub log: Vec<Rec>,
    pub tickets: ClientTickets<8>,
    pub read: HashMap<u64, Vec<u8>>,
    pub fin: HashSet<u64>,
    pub dgrams: Vec<Vec<u8>>,
    /// Read and consume stream data as it arrives.
    pub auto_read: bool,
    pub tx_log: Vec<(u64, usize, PathId)>,
    /// Answer key requests at once; when false they are computed and held in `deferred` for the test to deliver.
    pub auto_keys: bool,
    pub deferred: Option<Deferred>,
    /// Compute a failure instead of the real answer when deferring.
    pub fail_keys: bool,
}

impl<'a, const C: usize> Node<'a, C> {
    /// Drain events: answer key requests, store tickets, read streams and datagrams.
    pub fn service(&mut self, now: u64) {
        loop {
            let mut key_request = false;
            let mut new_tickets: Option<TicketBatch> = None;
            let mut readable: Vec<u64> = Vec::new();
            let mut datagram = false;
            while let Some(ev) = self.conn.poll_event() {
                let rec = match ev {
                    Event::KeyRequest(req) => {
                        if self.auto_keys {
                            key_request = true;
                        } else {
                            let soft = SoftKeys {
                                signer: Some((KeyHandle(1), &self.kp)),
                                prekeys: self.prekeys.as_ref(),
                            };
                            let mut env = Env {
                                provider: &self.prov,
                                now,
                                drbg: &mut self.drbg,
                            };
                            let mut sig = [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN];
                            self.deferred = Some(if self.fail_keys {
                                Deferred::Failed
                            } else {
                                match soft.answer(&mut env, &req, &mut sig) {
                                    vinc_security::KeyResponse::Signature(s) => Deferred::Signature(s.to_vec()),
                                    vinc_security::KeyResponse::SharedSecret(s) => Deferred::Secret(s),
                                    vinc_security::KeyResponse::Failed => Deferred::Failed,
                                }
                            });
                        }
                        continue;
                    }
                    Event::Connected { resumed } => Rec::Connected(resumed),
                    Event::StreamOpened(id) => Rec::Opened(id),
                    Event::StreamReadable(id) => {
                        readable.push(id);
                        Rec::Readable(id)
                    }
                    Event::StreamWritable(id) => Rec::Writable(id),
                    Event::OpenReady => Rec::OpenReady,
                    Event::StreamReset { id, error } => Rec::Reset(id, error),
                    Event::StreamStopped { id, error } => Rec::Stopped(id, error),
                    Event::DatagramReceived => {
                        datagram = true;
                        Rec::Datagram
                    }
                    Event::Extension { ty, body } => Rec::Extension(ty, body.to_vec()),
                    Event::ExtensionUndeliverable { ty, len } => Rec::ExtensionUndeliverable(ty, len),
                    Event::PathValidated(p) => Rec::PathValidated(p),
                    Event::PathFailed(p) => Rec::PathFailed(p),
                    Event::PeerAsleep => Rec::PeerAsleep,
                    Event::PeerAwake => Rec::PeerAwake,
                    Event::WakeUnanswered => Rec::WakeUnanswered,
                    Event::TicketsReceived(b) => {
                        new_tickets = Some(b);
                        Rec::Tickets
                    }
                    Event::Ready => Rec::Ready,
                    Event::Closed(r) => Rec::Closed(r),
                };
                self.log.push(rec);
            }
            if let Some(b) = new_tickets {
                self.conn.store_tickets(&mut self.tickets, &b, now);
            }
            if datagram {
                while let Some(d) = self.conn.recv_datagram() {
                    self.dgrams.push(d.to_vec());
                    self.conn.pop_datagram();
                }
            }
            if self.auto_read {
                for id in readable {
                    self.read_stream(now, id);
                }
            }
            if key_request {
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &self.kp)),
                    prekeys: self.prekeys.as_ref(),
                };
                let mut env = Env {
                    provider: &self.prov,
                    now,
                    drbg: &mut self.drbg,
                };
                while self.conn.answer_soft(&mut env, &soft).unwrap_or(false) {}
                continue;
            }
            break;
        }
    }

    /// Read and consume everything readable on `id` into `self.read`.
    pub fn read_stream(&mut self, now: u64, id: u64) {
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg: &mut self.drbg,
        };
        while let Some(chunk) = self.conn.read_chunk(id) {
            let n = chunk.len();
            self.read.entry(id).or_default().extend_from_slice(chunk);
            if self.conn.consume(&mut env, id, n).unwrap() == RecvStatus::Finished {
                self.fin.insert(id);
            }
        }
        if self.conn.consume(&mut env, id, 0).ok() == Some(RecvStatus::Finished) {
            self.fin.insert(id);
        }
    }

    /// Call `f` with the connection and an `Env` at time `now`.
    pub fn with_env<R>(&mut self, now: u64, f: impl FnOnce(&mut Conn<'a, C>, &mut Env<'_, Caps>) -> R) -> R {
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg: &mut self.drbg,
        };
        f(&mut self.conn, &mut env)
    }

    /// Deliver the held key answer.
    pub fn deliver_deferred(&mut self, now: u64) -> Result<(), vinc_security::Failure> {
        let held = self.deferred.take().unwrap();
        self.with_env(now, |c, env| match held {
            Deferred::Signature(s) => c.on_key_response(env, vinc_security::KeyResponse::Signature(&s)),
            Deferred::Secret(s) => c.on_key_response(env, vinc_security::KeyResponse::SharedSecret(s)),
            Deferred::Failed => c.on_key_response(env, vinc_security::KeyResponse::Failed),
        })
    }

    pub fn closed(&self) -> Option<CloseReason> {
        self.log
            .iter()
            .find_map(|r| if let Rec::Closed(c) = r { Some(*c) } else { None })
    }
    pub fn saw(&self, f: impl Fn(&Rec) -> bool) -> bool {
        self.log.iter().any(f)
    }
    pub fn connected(&self) -> bool {
        self.saw(|r| matches!(r, Rec::Connected(_)))
    }
}

/// A keypair and its identity.
pub struct Party {
    pub kp: Keypair,
    pub id: LocalIdentity,
}

pub fn party(alg: IdentityAlg, tag: u8) -> Party {
    let kp = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    Party { kp, id }
}

/// Everything two endpoints share: identities, caches and tickets.
pub struct World {
    pub ip: Party,
    pub rp: Party,
    pub hw: bool,
    pub stores: Box<Stores>,
    pub alg: IdentityAlg,
    pub cfg: Config,
    /// Try the short first flight.
    pub short: bool,
    /// The client's own configuration when it differs from the server's.
    pub client_cfg: Option<Config>,
    /// Mixed into both sides' random generators, so two worlds with different seeds run different sessions.
    pub seed: u8,
}

impl World {
    pub fn new(alg: IdentityAlg) -> Self {
        Self::with_aead(alg, true)
    }
    pub fn with_aead(alg: IdentityAlg, hw: bool) -> Self {
        let cfg = Config::new();
        Self {
            ip: party(alg, 0x21),
            rp: party(alg, 0x22),
            hw,
            stores: Box::default(),
            alg,
            cfg,
            short: false,
            client_cfg: None,
            seed: 0,
        }
    }

    pub fn client<'a, const C: usize>(
        &self,
        store: &'a mut Store<C>,
        ticket: Option<vinc_security::Ticket>,
        tickets: ClientTickets<8>,
    ) -> Node<'a, C> {
        let prov = Caps(Software, self.hw);
        let mut drbg = Drbg::new(&[0x11 ^ self.seed; 32]);
        let kp = Keypair::from_seed(self.alg, &vec![0x21; self.alg.seed_len()]).unwrap();
        let mut env = Env {
            provider: &prov,
            now: T0,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        let prekey = prekeys.acquire(&mut env).unwrap();
        let conn = Conn::<C>::client(
            self.client_cfg.unwrap_or(self.cfg),
            ClientParams {
                peer: self.rp.id.node_id(),
                alpn: ALPN,
                identity: &self.ip.id,
                prekey: &prekey,
                peer_has_prekey: self.short,
                ticket,
                path: PathId(1),
                path_info: PathInfo::default(),
            },
            store.resources(),
            &mut env,
        )
        .unwrap();
        Node {
            conn,
            prov,
            drbg,
            kp,
            prekeys: Some(prekeys),
            log: Vec::new(),
            tickets,
            read: HashMap::new(),
            fin: HashSet::new(),
            dgrams: Vec::new(),
            auto_read: true,
            tx_log: Vec::new(),
            auto_keys: true,
            deferred: None,
            fail_keys: false,
        }
    }

    pub fn server<'a, const C: usize>(&self, store: &'a mut Store<C>) -> Node<'a, C> {
        let prov = Caps(Software, self.hw);
        let mut drbg = Drbg::new(&[0x33 ^ self.seed; 32]);
        let kp = Keypair::from_seed(self.alg, &vec![0x22; self.alg.seed_len()]).unwrap();
        let mut env = Env {
            provider: &prov,
            now: T0,
            drbg: &mut drbg,
        };
        let conn = Conn::<C>::server(
            self.cfg,
            &ServerParams {
                identity: self.rp.id,
                alpns: AlpnList::new(&[ALPN]).unwrap(),
                tickets_per_session: 1,
                ticket_lifetime_s: 86_400,
            },
            store.resources(),
            &mut env,
        )
        .unwrap();
        Node {
            conn,
            prov,
            drbg,
            kp,
            prekeys: None,
            log: Vec::new(),
            tickets: ClientTickets::new(),
            read: HashMap::new(),
            fin: HashSet::new(),
            dgrams: Vec::new(),
            auto_read: true,
            tx_log: Vec::new(),
            auto_keys: true,
            deferred: None,
            fail_keys: false,
        }
    }
}

/// Two nodes on a link, on virtual time.
pub struct Net<'a, 'b, const C: usize = RING> {
    pub a: Node<'a, C>,
    pub b: Node<'a, C>,
    pub link: Link,
    pub stores: &'b mut Stores,
    pub now: u64,
    /// Called with `(direction_is_a_to_b, datagram, now)` for every datagram a node sends.
    pub on_tx: Option<Box<dyn FnMut(bool, &[u8], u64)>>,
    pub buf: Vec<u8>,
    pub rx_drops: Vec<(bool, Drop)>,
    /// Assert that B sends at most 3 times what it received until it is connected, counting 48 bytes more than the
    /// size of every datagram.
    pub amp_check: bool,
    /// Drop A's first datagram sent after A is connected and B is not (the Finish flight).
    pub drop_finish: bool,
    pub b_rx: u64,
    pub b_tx: u64,
}

pub const T0: u64 = 1_000_000_000_000;
pub const MS: u64 = 1_000_000;
pub const SEC: u64 = 1_000_000_000;

impl<'a, 'b, const C: usize> Net<'a, 'b, C> {
    pub fn new(a: Node<'a, C>, b: Node<'a, C>, link: Link, stores: &'b mut Stores) -> Self {
        Self {
            a,
            b,
            link,
            stores,
            now: T0,
            on_tx: None,
            buf: vec![0u8; 65_536],
            rx_drops: Vec::new(),
            amp_check: false,
            drop_finish: false,
            b_rx: 0,
            b_tx: 0,
        }
    }

    /// Deliver what is due, let both nodes transmit until idle, and serve their events. Returns whether anything moved.
    pub fn flush(&mut self) -> bool {
        let mut moved = false;
        loop {
            let mut progress = false;
            let now = self.now;
            while let Some((p, mut d)) = self.link.pop_b(now) {
                self.b_rx += d.len() as u64;
                let mut env = Env {
                    provider: &self.b.prov,
                    now,
                    drbg: &mut self.b.drbg,
                };
                if let Err(e) = self.b.conn.handle_datagram_with(&mut env, self.stores, p, &mut d) {
                    self.rx_drops.push((false, e));
                }
                progress = true;
            }
            while let Some((p, mut d)) = self.link.pop_a(now) {
                let mut env = Env {
                    provider: &self.a.prov,
                    now,
                    drbg: &mut self.a.drbg,
                };
                if let Err(e) = self.a.conn.handle_datagram(&mut env, p, &mut d) {
                    self.rx_drops.push((true, e));
                }
                progress = true;
            }
            if self.drop_finish && self.a.conn.is_connected() && !self.b.conn.is_connected() {
                self.link.route(PathId(1)).ab.drop_next(1);
                self.drop_finish = false;
            }
            for is_a in [true, false] {
                loop {
                    let node = if is_a { &mut self.a } else { &mut self.b };
                    let mut env = Env {
                        provider: &node.prov,
                        now,
                        drbg: &mut node.drbg,
                    };
                    let Some(t) = node.conn.poll_transmit(&mut env, &mut self.buf) else {
                        break;
                    };
                    progress = true;
                    let Transmit {
                        path,
                        len,
                        segment_size,
                    } = t;
                    node.tx_log.push((now, len, path));
                    for seg in self.buf[..len].chunks(segment_size) {
                        if let Some(f) = self.on_tx.as_mut() {
                            f(is_a, seg, now);
                        }
                        if !is_a {
                            if self.amp_check && !self.b.conn.is_connected() {
                                assert!(
                                    self.b_tx + seg.len() as u64 + 48 <= 3 * self.b_rx,
                                    "amplification: sent {} + {} + 48 after receiving {}",
                                    self.b_tx,
                                    seg.len(),
                                    self.b_rx
                                );
                            }
                            // Every datagram counts 48 bytes more than its size.
                            self.b_tx += seg.len() as u64 + 48;
                        }
                        if is_a {
                            self.link.send_a(now, path, seg);
                        } else {
                            self.link.send_b(now, path, seg);
                        }
                    }
                }
            }
            self.a.service(now);
            self.b.service(now);
            if !progress {
                break;
            }
            moved = true;
        }
        moved
    }

    /// The next time anything is due.
    pub fn next_at(&self) -> Option<u64> {
        [
            self.link.next_at(),
            self.a.conn.poll_timeout(),
            self.b.conn.poll_timeout(),
        ]
        .into_iter()
        .flatten()
        .min()
    }

    /// Advance to the next due time (not past `deadline`) and run the timers there. Returns false if nothing is due.
    pub fn advance(&mut self, deadline: u64) -> bool {
        let Some(t) = self.next_at() else { return false };
        if t > deadline {
            return false;
        }
        self.now = self.now.max(t);
        let now = self.now;
        for node in [&mut self.a, &mut self.b] {
            if node.conn.poll_timeout().is_some_and(|t| t <= now) {
                let mut env = Env {
                    provider: &node.prov,
                    now,
                    drbg: &mut node.drbg,
                };
                node.conn.handle_timeout(&mut env);
            }
        }
        true
    }

    /// Run until `stop` says so, nothing is due, or `deadline` passes. `step` runs after every flush (for the
    /// application's own writes and reads). Panics if time stops advancing for too long.
    pub fn run(&mut self, deadline: u64, mut step: impl FnMut(&mut Self) -> bool) -> bool {
        let mut stuck = 0u32;
        let mut last = self.now;
        loop {
            self.flush();
            if step(self) {
                self.flush();
                return true;
            }
            self.flush();
            if !self.advance(deadline) {
                self.now = self.now.max(deadline.min(self.next_at().unwrap_or(deadline)));
                return false;
            }
            if self.now == last {
                stuck += 1;
                assert!(
                    stuck < 20_000,
                    "time is not advancing at {} (link {:?} a {:?} b {:?})",
                    self.now,
                    self.link.next_at(),
                    self.a.conn.poll_timeout(),
                    self.b.conn.poll_timeout()
                );
            } else {
                stuck = 0;
                last = self.now;
            }
        }
    }

    /// Run until both sides are connected (or `deadline`).
    pub fn connect(&mut self, deadline: u64) -> bool {
        self.run(deadline, |n| n.a.conn.is_connected() && n.b.conn.is_connected())
    }
}

/// Deterministic bytes.
pub fn pattern(len: usize, seed: u64) -> Vec<u8> {
    let mut v = vec![0u8; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

/// A client and a server on `link`, not yet connected.
pub fn setup<'a, const C: usize>(
    w: &'a mut World,
    sa: &'a mut Store<C>,
    sb: &'a mut Store<C>,
    link: Link,
) -> Net<'a, 'a, C> {
    let a = w.client(sa, None, ClientTickets::new());
    let b = w.server(sb);
    Net::new(a, b, link, &mut w.stores)
}

/// Send `data` on a new bidirectional stream from A and run until B has read it all and A has nothing in flight.
/// Returns the virtual time the transfer took and the stream id.
pub fn bulk<const C: usize>(net: &mut Net<'_, '_, C>, data: &[u8], timeout: u64) -> (u64, u64) {
    let id = net.a.conn.open_bi().unwrap();
    let mut off = 0;
    let mut finished = false;
    let start = net.now;
    let done = net.run(net.now + timeout, |n| {
        while off < data.len() {
            let end = (off + 256 * 1024).min(data.len());
            let k = n.a.conn.write(id, &data[off..end]).unwrap();
            if k == 0 {
                break;
            }
            off += k;
        }
        if off == data.len() && !finished {
            n.a.conn.finish(id).unwrap();
            finished = true;
        }
        n.b.fin.contains(&id)
    });
    assert!(
        done,
        "transfer did not finish: sent {off}/{} read {}",
        data.len(),
        net.b.read.get(&id).map_or(0, Vec::len)
    );
    assert!(net.b.read[&id] == data, "bytes differ");
    (net.now - start, id)
}
