//! The harness of `transport_link.rs` and `repro_transport_link.rs`: two real connections (the public API an
//! application uses) joined by a scripted link on virtual time, with the host's restart of a server session that
//! holds a damaged first message. Built as its own test target too, with no test of its own.
#![allow(
    dead_code,
    unreachable_pub,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet, BinaryHeap};

use ephyra::prelude::*;
use ephyra::{Arbitrary, gens};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::{
    AlpnList, Env, Failure, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys, SoftPrekeys,
};
use pinc_transport::conn::{
    ClientParams, CloseReason, Config, Connection, Drop, Event, Lent, PathId, PathInfo, Resources, ServerParams,
    Tables, Transmit,
};
use pinc_transport::packet::{LongHeader, LongType};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::spill::SpillArena;
use pinc_transport::stream::{self, NoSource, RecvStatus, Streams};

pub const MS: u64 = 1_000_000;
pub const SEC: u64 = 1_000_000_000;
pub const T0: u64 = 1_000_000_000_000;
pub const ALPN: &[u8] = b"pinc/1";

pub type Table = Streams<NoSource, 64, 257>;
pub type Conn<'a> = Connection<'a, Software, NoSource, 64, 257, 512, 4>;
pub type Stores = ResponderStores<8, 512>;

/// What the link does to one datagram while the chaos lasts.
#[derive(Clone, Debug, Arbitrary)]
pub enum Fate {
    Deliver,
    Drop,
    /// Delivered twice, the copy `later` ms after the first.
    Dup(#[ephyra(gen = gens::int(0u64..=80))] u64),
    /// Held back `extra` ms, so later datagrams overtake it.
    Hold(#[ephyra(gen = gens::int(1u64..=300))] u64),
    /// Cut to its first `keep` bytes.
    Truncate(#[ephyra(gen = gens::int(0usize..=1300))] usize),
    /// One byte flipped.
    Corrupt {
        #[ephyra(gen = gens::int(0usize..=1500))]
        at: usize,
        #[ephyra(gen = gens::int(1u8..=255))]
        xor: u8,
    },
}

#[derive(Clone, Debug)]
pub struct Case {
    /// One-way delay of the clean link, ms.
    pub delay: u64,
    /// Chaos length after both sides connected, ms; chaos also during the handshake when `early`.
    pub chaos: u64,
    pub early: bool,
    /// The schedule, used in turn for each datagram while the chaos lasts.
    pub fates: Vec<Fate>,
    /// Client-opened streams: (bidirectional, length).
    pub client_streams: Vec<(bool, usize)>,
    /// Server-opened unidirectional streams.
    pub server_streams: Vec<usize>,
    /// Datagrams the client sends, by length.
    pub datagrams: Vec<usize>,
    pub chunks: usize,
    /// Connection settings both sides use.
    pub knobs: Knobs,
}

/// The `conn::Config` fields a case varies, all documented settings of the public API.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Knobs {
    /// `key_update_after`: a key roll after this many packets (the default is 2^21).
    pub key_update_after: u64,
    pub max_gso: usize,
    pub flight_split: bool,
    pub ack_every: Option<u32>,
    pub keepalive: Option<u64>,
    pub probe_mtu: bool,
}

impl Knobs {
    pub fn default_config() -> Self {
        let c = Config::new();
        Self {
            key_update_after: c.key_update_after,
            max_gso: c.max_gso,
            flight_split: c.flight_split,
            ack_every: c.ack_every,
            keepalive: c.keepalive,
            probe_mtu: c.probe_mtu,
        }
    }

    pub fn config(&self) -> Config {
        let mut c = Config::new();
        c.key_update_after = self.key_update_after;
        c.max_gso = self.max_gso;
        c.flight_split = self.flight_split;
        c.ack_every = self.ack_every;
        c.keepalive = self.keepalive;
        c.probe_mtu = self.probe_mtu;
        c
    }
}

fn knobs() -> impl Gen<Value = Knobs> {
    let d = Knobs::default_config();
    (
        gens::frequency(vec![
            (2, gens::constant(d.key_update_after).boxed()),
            (1, gens::int(8u64..=300).boxed()),
        ]),
        gens::frequency(vec![
            (2, gens::constant(1usize).boxed()),
            (1, gens::int(2usize..=8).boxed()),
        ]),
        gens::bool(),
        gens::option(gens::int(1u32..=10)),
        gens::option(gens::int(100 * MS..=20 * SEC)),
        gens::bool_with(0.7),
    )
        .map(
            |(key_update_after, max_gso, flight_split, ack_every, keepalive, probe_mtu)| Knobs {
                key_update_after,
                max_gso,
                flight_split,
                ack_every,
                keepalive,
                probe_mtu,
            },
        )
}

pub fn case() -> impl Gen<Value = Case> {
    (
        gens::frequency(vec![
            (3, gens::int(0u64..=30).boxed()),
            (1, gens::int(0u64..=300).boxed()),
        ]),
        gens::int(0u64..=8000),
        gens::bool_with(0.3),
        gens::vec(gens::frequency(vec![
            (8, gens::constant(Fate::Deliver).boxed()),
            (6, ephyra::any::<Fate>().boxed()),
        ]))
        .len(1..=40),
        gens::vec((
            gens::bool(),
            gens::frequency(vec![
                (2, gens::int(0usize..=3000).boxed()),
                (1, gens::int(0usize..=400_000).boxed()),
            ]),
        ))
        .len(0..=4),
        gens::vec(gens::frequency(vec![
            (2, gens::int(0usize..=3000).boxed()),
            (1, gens::int(0usize..=200_000).boxed()),
        ]))
        .len(0..=2),
        gens::vec(gens::int(1usize..=1100)).len(0..=6),
        (gens::pick_from(vec![64usize, 256, 1024]), knobs()),
    )
        .map(
            |(delay, chaos, early, fates, client_streams, server_streams, datagrams, (chunks, knobs))| Case {
                delay,
                chaos,
                early,
                fates,
                client_streams,
                server_streams,
                datagrams,
                chunks,
                knobs,
            },
        )
        .with_shrink(shrink_case)
}

pub fn shrink_case(c: &Case, visit: &mut dyn FnMut(Case) -> std::ops::ControlFlow<()>) -> std::ops::ControlFlow<()> {
    if c.knobs != Knobs::default_config() {
        visit(Case {
            knobs: Knobs::default_config(),
            ..c.clone()
        })?;
    }
    if c.chaos > 0 {
        visit(Case {
            chaos: c.chaos / 2,
            ..c.clone()
        })?;
    }
    if c.early {
        visit(Case {
            early: false,
            ..c.clone()
        })?;
    }
    for i in 0..c.fates.len() {
        if c.fates.len() > 1 {
            let mut fates = c.fates.clone();
            fates.remove(i);
            visit(Case { fates, ..c.clone() })?;
        }
        if !matches!(c.fates[i], Fate::Deliver) {
            let mut fates = c.fates.clone();
            fates[i] = Fate::Deliver;
            visit(Case { fates, ..c.clone() })?;
        }
    }
    for i in 0..c.client_streams.len() {
        let mut s = c.client_streams.clone();
        s.remove(i);
        visit(Case {
            client_streams: s,
            ..c.clone()
        })?;
        if c.client_streams[i].1 > 0 {
            let mut s = c.client_streams.clone();
            s[i].1 /= 2;
            visit(Case {
                client_streams: s,
                ..c.clone()
            })?;
        }
    }
    for i in 0..c.server_streams.len() {
        let mut s = c.server_streams.clone();
        s.remove(i);
        visit(Case {
            server_streams: s,
            ..c.clone()
        })?;
    }
    for i in 0..c.datagrams.len() {
        let mut s = c.datagrams.clone();
        s.remove(i);
        visit(Case {
            datagrams: s,
            ..c.clone()
        })?;
    }
    if c.delay > 0 {
        visit(Case {
            delay: c.delay / 2,
            ..c.clone()
        })?;
    }
    std::ops::ControlFlow::Continue(())
}

pub fn pattern(len: usize, seed: u64) -> Vec<u8> {
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    (0..len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x as u8
        })
        .collect()
}

/// One endpoint: its connection, keys and what it received.
pub struct Node<'a> {
    conn: Conn<'a>,
    prov: Software,
    drbg: Drbg,
    kp: Keypair,
    prekeys: Option<SoftPrekeys<Software>>,
    spill: SpillArena<'a>,
    read: BTreeMap<u64, Vec<u8>>,
    fin: BTreeSet<u64>,
    dgrams: Vec<Vec<u8>>,
    connected: bool,
    closed: Option<CloseReason>,
}

impl Node<'_> {
    fn placeholder_read() -> (BTreeMap<u64, Vec<u8>>, BTreeSet<u64>) {
        (BTreeMap::new(), BTreeSet::new())
    }

    fn service(&mut self, now: u64) {
        loop {
            let mut key = false;
            let mut readable = Vec::new();
            let mut dgram = false;
            while let Some(ev) = self.conn.poll_event() {
                match ev {
                    Event::KeyRequest(_) => key = true,
                    Event::Connected { .. } => self.connected = true,
                    Event::StreamReadable(id) => readable.push(id),
                    Event::DatagramReceived => dgram = true,
                    Event::Closed(r) => self.closed = Some(r),
                    _ => {}
                }
            }
            if dgram {
                while let Some(d) = self.conn.recv_datagram() {
                    self.dgrams.push(d.to_vec());
                    self.conn.pop_datagram();
                }
            }
            for id in readable {
                self.read_stream(now, id);
            }
            if key {
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

    fn read_stream(&mut self, now: u64, id: u64) {
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg: &mut self.drbg,
        };
        while let Some(chunk) = self.conn.read_chunk(id) {
            let n = chunk.len();
            assert!(n > 0, "an empty readable chunk on stream {id}");
            self.read.entry(id).or_default().extend_from_slice(chunk);
            let st = self.conn.consume(&mut env, &mut Lent { spill: &mut self.spill }, id, n);
            assert!(st.is_ok(), "consume of {n} readable bytes on {id}: {st:?}");
            if st == Ok(RecvStatus::Finished) {
                self.fin.insert(id);
            }
        }
        if self.conn.consume(&mut env, &mut Lent { spill: &mut self.spill }, id, 0) == Ok(RecvStatus::Finished) {
            self.fin.insert(id);
        }
    }
}

pub fn server_params(kp: &Keypair) -> ServerParams {
    ServerParams {
        identity: LocalIdentity::from_keypair(kp, KeyHandle(1)).unwrap(),
        alpns: AlpnList::new(&[ALPN]).unwrap(),
        tickets_per_session: 1,
        ticket_lifetime_s: 86_400,
    }
}

pub type Res<'a> = Resources<'a, NoSource, 64, 257, 512>;

/// The most sessions that hold one connection id at once, as the endpoint allows (`MAX_CANDIDATES` in `pinc-core`).
pub const CANDIDATES: usize = 4;

/// A server session started from the memory of a free slot, the way the endpoint starts one: the pool is reset, the
/// stream table made again and the tables cleared.
pub fn new_server(mut res: Res<'_>, cfg: Config, now: u64, seed: u8) -> Node<'_> {
    res.pool.reset();
    res.streams.reinit(&stream::Config::new(false), &res.pool);
    res.tables.clear();
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &vec![0x22; alg.seed_len()]).unwrap();
    let prov = Software;
    let mut drbg = Drbg::new(&[seed; 32]);
    let mut env = Env {
        provider: &prov,
        now,
        drbg: &mut drbg,
    };
    let conn = Conn::server(cfg, &server_params(&kp), res, &mut env).unwrap();
    Node {
        conn,
        prov,
        drbg,
        kp,
        prekeys: None,
        spill: SpillArena::default(),
        read: BTreeMap::new(),
        fin: BTreeSet::new(),
        dgrams: Vec::new(),
        connected: false,
        closed: None,
    }
}

/// Give a session's memory back to the free slots.
pub fn free_server<'a>(mut n: Node<'a>, spare: &mut Vec<Res<'a>>) {
    spare.push(n.conn.into_resources(&mut Lent { spill: &mut n.spill }));
}

pub fn deliver_server(n: &mut Node<'_>, stores: &mut Stores, now: u64, d: &[u8]) -> Result<(), Drop> {
    let mut d = d.to_vec();
    let mut env = Env {
        provider: &n.prov,
        now,
        drbg: &mut n.drbg,
    };
    n.conn
        .handle_datagram_with(&mut env, &mut Lent { spill: &mut n.spill }, stores, PathId(1), &mut d)
}

/// The destination id, message length and offset of a long Handshake packet that carries a part of a message
/// (`classify` and `later_part` in `pinc-core`).
fn message_part(d: &[u8]) -> Option<(Vec<u8>, u64, u64)> {
    let (h, hlen) = LongHeader::parse(d).ok()?;
    if h.ty != LongType::Handshake {
        return None;
    }
    let mut r = pinc_wire::Reader::new(d.get(hlen..hlen.checked_add(h.body_len)?)?);
    let total = r.read_varint().ok()?;
    let off = r.read_varint().ok()?;
    (total > 0 && off < total).then(|| (h.dcid.as_bytes().to_vec(), total, off))
}

/// A datagram on the link: (arrival time, sequence, to the client, bytes).
pub type InFlight = Reverse<(u64, u64, bool, Vec<u8>)>;

pub struct Link {
    q: BinaryHeap<InFlight>,
    seq: u64,
    sent: u64,
}

/// One writer of a stream: what to write and how far it got.
pub struct Out {
    id: u64,
    data: Vec<u8>,
    off: usize,
    finished: bool,
}

pub fn write_out(conn: &mut Conn<'_>, outs: &mut [Out]) {
    for o in outs.iter_mut() {
        while o.off < o.data.len() {
            let end = (o.off + 64 * 1024).min(o.data.len());
            match conn.write(o.id, &o.data[o.off..end]) {
                Ok(0) => break,
                Ok(n) => {
                    assert!(n <= end - o.off, "write took more than it was given");
                    o.off += n;
                }
                Err(e) => panic!("write on stream {} refused: {e:?}", o.id),
            }
        }
        if o.off == o.data.len() && !o.finished {
            assert_eq!(conn.finish(o.id), Ok(()), "finish of stream {}", o.id);
            o.finished = true;
        }
    }
}

pub fn check_prefix(side: &str, read: &BTreeMap<u64, Vec<u8>>, outs: &[Out]) {
    for (id, got) in read {
        let o = outs.iter().find(|o| o.id == *id);
        assert!(o.is_some(), "{side} read stream {id}, which nobody wrote");
        let o = o.unwrap();
        assert!(
            got.len() <= o.data.len(),
            "{side} read {} bytes of stream {id}, {} written",
            got.len(),
            o.data.len()
        );
        assert!(
            *got == o.data[..got.len()],
            "{side} read bytes on stream {id} other than those written"
        );
    }
}

pub fn run(c: &Case) {
    let alg = IdentityAlg::Ed25519;
    let ckp = Keypair::from_seed(alg, &vec![0x21; alg.seed_len()]).unwrap();
    let skp = Keypair::from_seed(alg, &vec![0x22; alg.seed_len()]).unwrap();
    let cid = LocalIdentity::from_keypair(&ckp, KeyHandle(1)).unwrap();
    let sid = LocalIdentity::from_keypair(&skp, KeyHandle(1)).unwrap();
    drop(skp);
    let mut stores: Box<Stores> = Box::default();
    let mut ctab = Box::new(Table::new(&stream::Config::new(true), &BufferPool::new_boxed(c.chunks)));
    let mut stabs: Vec<Box<Table>> = (0..CANDIDATES)
        .map(|_| {
            Box::new(Table::new(
                &stream::Config::new(false),
                &BufferPool::new_boxed(c.chunks),
            ))
        })
        .collect();
    let slosses: Vec<LossEstimate> = (0..CANDIDATES).map(|_| LossEstimate::new()).collect();
    let closs = LossEstimate::new();
    let cfg = c.knobs.config();
    let prov = Software;

    let mut cdrbg = Drbg::new(&[0x11; 32]);
    let mut env = Env {
        provider: &prov,
        now: T0,
        drbg: &mut cdrbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let client = Conn::client(
        cfg,
        ClientParams {
            peer: sid.node_id(),
            alpn: ALPN,
            identity: &cid,
            prekey: &prekey,
            peer_has_prekey: false,
            ticket: None,
            path: PathId(1),
            path_info: PathInfo::default(),
        },
        Resources {
            pool: BufferPool::new_boxed(c.chunks),
            streams: (&mut *ctab).into(),
            loss: (&closs).into(),
            tables: Tables::new(),
        },
        &mut env,
    )
    .unwrap();
    // The server's free slots; a session starts on the first datagram, as the endpoint starts one.
    let mut spare: Vec<Res<'_>> = stabs
        .iter_mut()
        .zip(&slosses)
        .map(|(t, l)| Resources {
            pool: BufferPool::new_boxed(c.chunks),
            streams: (&mut **t).into(),
            loss: l.into(),
            tables: Tables::new(),
        })
        .collect();
    let mut srv: Vec<Node<'_>> = Vec::new();
    let mut started = 0u8;
    // Later parts of a first message no session took, waiting for their start (`orphans` in `pinc-core`).
    let mut orphans: Vec<(Vec<u8>, u64, Vec<u8>)> = Vec::new();
    let mut a = Node {
        conn: client,
        prov,
        drbg: cdrbg,
        kp: ckp,
        prekeys: Some(prekeys),
        spill: SpillArena::default(),
        read: BTreeMap::new(),
        fin: BTreeSet::new(),
        dgrams: Vec::new(),
        connected: false,
        closed: None,
    };
    let mut link = Link {
        q: BinaryHeap::new(),
        seq: 0,
        sent: 0,
    };
    let mut now = T0;
    let mut chaos_until: Option<u64> = if c.early { Some(T0 + c.chaos * MS) } else { None };
    let mut a_outs: Vec<Out> = Vec::new();
    let mut b_outs: Vec<Out> = Vec::new();
    let mut opened = false;
    let mut sent_dgrams: Vec<Vec<u8>> = Vec::new();
    let mut buf = vec![0u8; 65_536];
    let mut same_time = 0u32;
    let mut last_now = now;
    let mut clean_at: Option<u64> = None;
    let mut iterations = 0u64;
    let trace = std::env::var_os("PBT_TRACE").is_some();

    loop {
        iterations += 1;
        assert!(iterations < 3_000_000, "the driver loop ran 3,000,000 turns");
        // Deliver what is due.
        while let Some(Reverse((at, _, _, _))) = link.q.peek() {
            if *at > now {
                break;
            }
            let Reverse((_, _, to_a, mut d)) = link.q.pop().unwrap();
            let len = d.len();
            if to_a {
                let mut env = Env {
                    provider: &a.prov,
                    now,
                    drbg: &mut a.drbg,
                };
                let r = a
                    .conn
                    .handle_datagram(&mut env, &mut Lent { spill: &mut a.spill }, PathId(1), &mut d);
                if trace {
                    eprintln!("{} ms: client got {len} bytes: {r:?}", (now - T0) / MS);
                }
                continue;
            }
            // Ended sessions with no timer left are freed, as the endpoint frees them.
            let mut i = 0;
            while i < srv.len() {
                if srv[i].conn.is_closed() && srv[i].conn.poll_timeout().is_none() {
                    free_server(srv.remove(i), &mut spare);
                } else {
                    i += 1;
                }
            }
            // Offered to each holder, oldest first, until one owns it (`pinc-core` `offer`): a holder that refuses a
            // handshake message, cannot open it or has ended does not own it, and while there are several, neither
            // does one that only added a part to a message. When every live holder says it is a first flight other
            // than its own, a start of a message gets a session of its own and a later part waits for its start.
            let n = srv.len();
            let start = message_part(&d).filter(|p| p.2 == 0);
            // A start of a message whose later part waits goes to a session of its own at once (`starts_held_message`).
            let held = n > 0
                && n < CANDIDATES
                && start
                    .as_ref()
                    .is_some_and(|(dcid, total, _)| orphans.iter().any(|o| &o.0 == dcid && o.1 == *total));
            if !held {
                let (mut different, mut other, mut parted, mut owned) = (false, false, false, false);
                for (k, node) in srv.iter_mut().enumerate() {
                    let r = deliver_server(node, &mut stores, now, &d);
                    if trace {
                        eprintln!("{} ms: server session {k} got {len} bytes: {r:?}", (now - T0) / MS);
                    }
                    if n > 1 && r.is_ok() && node.conn.take_handshake_part() {
                        parted = true;
                        continue;
                    }
                    match r {
                        Err(Drop::Handshake(Failure::DifferentFirst)) => different = true,
                        Err(Drop::Closed) => {}
                        Err(Drop::Handshake(_) | Drop::Undecryptable) => other = true,
                        _ => {
                            owned = true;
                            break;
                        }
                    }
                }
                if n > 0 && (owned || !different || other || parted) {
                    continue;
                }
                if n > 0 && start.is_none() {
                    // vertexia: held parts never expire here (the endpoint's do); at most CANDIDATES are kept.
                    if let Some((dcid, total, _)) = message_part(&d)
                        && orphans.len() < CANDIDATES
                    {
                        orphans.push((dcid, total, d.clone()));
                    }
                    continue;
                }
            }
            if n < CANDIDATES
                && let Some(res) = spare.pop()
            {
                started += 1;
                assert!(started <= 64, "64 server sessions were started");
                let mut node = new_server(res, cfg, now, 0x33 ^ started);
                let r = deliver_server(&mut node, &mut stores, now, &d);
                if trace {
                    eprintln!(
                        "{} ms: new server session {} got {len} bytes: {r:?}",
                        (now - T0) / MS,
                        srv.len()
                    );
                }
                // A held later part of the message this datagram starts joins the new session.
                if let Some((dcid, total, _)) = start {
                    for (_, _, part) in orphans.extract_if(.., |o| o.0 == dcid && o.1 == total) {
                        let r = deliver_server(&mut node, &mut stores, now, &part);
                        if trace {
                            eprintln!(
                                "{} ms: new server session {} got the held {} bytes: {r:?}",
                                (now - T0) / MS,
                                srv.len(),
                                part.len()
                            );
                        }
                    }
                }
                srv.push(node);
            }
        }
        // Timers.
        for node in std::iter::once(&mut a).chain(srv.iter_mut()) {
            if node.conn.poll_timeout().is_some_and(|t| t <= now) {
                let mut env = Env {
                    provider: &node.prov,
                    now,
                    drbg: &mut node.drbg,
                };
                let due = node.conn.poll_timeout();
                node.conn.handle_timeout(&mut env, &mut Lent { spill: &mut node.spill });
                if trace {
                    eprintln!(
                        "{} ms: a timer fired on {} (due {due:?}, next {:?}, rekey {:?}, ring room {}, can send {}, loss {:?}): {:?}",
                        (now - T0) / MS,
                        if node.conn.is_client() { "client" } else { "server" },
                        node.conn.poll_timeout(),
                        node.conn.rekey_deadline(),
                        node.conn.recovery().ring_has_room(),
                        node.conn.recovery().can_send(),
                        node.conn.recovery().next_timeout(),
                        node.conn.stats()
                    );
                }
            }
        }
        a.service(now);
        srv.iter_mut().for_each(|n| n.service(now));
        // Once one session established, the others are closed by the host: only it holds the connection.
        if let Some(k) = srv.iter().position(|n| n.connected)
            && srv.len() > 1
        {
            let keep = srv.remove(k);
            for n in srv.drain(..) {
                free_server(n, &mut spare);
            }
            srv.push(keep);
        }
        let b_up = srv.len() == 1 && srv[0].connected;
        // Checked before the application writes again: a closed connection forgets its streams.
        assert!(a.closed.is_none(), "the client closed: {:?}", a.closed);
        if opened {
            assert!(srv[0].closed.is_none(), "the server closed: {:?}", srv[0].closed);
        }
        if a.connected && b_up && !opened {
            opened = true;
            let b = &mut srv[0];
            if chaos_until.is_none() {
                chaos_until = Some(now + c.chaos * MS);
            }
            for (i, &(bidi, len)) in c.client_streams.iter().enumerate() {
                let id = if bidi { a.conn.open_bi() } else { a.conn.open_uni() };
                let id = id.unwrap_or_else(|e| panic!("open of client stream {i} refused: {e:?}"));
                a_outs.push(Out {
                    id,
                    data: pattern(len, 100 + i as u64),
                    off: 0,
                    finished: false,
                });
            }
            for (i, &len) in c.server_streams.iter().enumerate() {
                let id = b
                    .conn
                    .open_uni()
                    .unwrap_or_else(|e| panic!("open of server stream {i} refused: {e:?}"));
                b_outs.push(Out {
                    id,
                    data: pattern(len, 200 + i as u64),
                    off: 0,
                    finished: false,
                });
            }
            for (i, &len) in c.datagrams.iter().enumerate() {
                let mut d = pattern(len, 300 + i as u64);
                d[0] = i as u8;
                if a.conn.send_datagram(&d).is_ok() {
                    sent_dgrams.push(d);
                }
            }
        }
        if opened {
            let b = &mut srv[0];
            write_out(&mut a.conn, &mut a_outs);
            write_out(&mut b.conn, &mut b_outs);
            // Read every known stream each turn too, so a missed readable event cannot stall the oracle.
            for o in &a_outs {
                b.read_stream(now, o.id);
            }
            for o in &b_outs {
                a.read_stream(now, o.id);
            }
        }
        // Transmit.
        for (k, node) in std::iter::once(&mut a).chain(srv.iter_mut()).enumerate() {
            let to_a = k > 0;
            loop {
                let mut env = Env {
                    provider: &node.prov,
                    now,
                    drbg: &mut node.drbg,
                };
                let Some(Transmit { len, segment_size, .. }) =
                    node.conn
                        .poll_transmit(&mut env, &mut Lent { spill: &mut node.spill }, &mut buf)
                else {
                    break;
                };
                assert!(
                    len <= buf.len() && segment_size > 0,
                    "a transmit of {len} bytes in segments of {segment_size}"
                );
                for seg in buf[..len].chunks(segment_size) {
                    assert!(seg.len() <= 1500, "a datagram of {} bytes", seg.len());
                    link.sent += 1;
                    let chaotic = chaos_until.is_none_or(|u| now < u) && (c.early || opened);
                    let fate = if chaotic {
                        c.fates[(link.sent as usize) % c.fates.len()].clone()
                    } else {
                        Fate::Deliver
                    };
                    if trace {
                        eprintln!(
                            "{} ms: {} sends {} bytes: {fate:?}",
                            (now - T0) / MS,
                            if to_a { "server" } else { "client" },
                            seg.len()
                        );
                    }
                    let at = now + c.delay * MS;
                    let push = |link: &mut Link, at: u64, d: Vec<u8>| {
                        link.seq += 1;
                        link.q.push(Reverse((at, link.seq, to_a, d)));
                    };
                    match fate {
                        Fate::Deliver => push(&mut link, at, seg.to_vec()),
                        Fate::Drop => {}
                        Fate::Dup(later) => {
                            push(&mut link, at, seg.to_vec());
                            push(&mut link, at + later * MS, seg.to_vec());
                        }
                        Fate::Hold(extra) => push(&mut link, at + extra * MS, seg.to_vec()),
                        Fate::Truncate(keep) => push(&mut link, at, seg[..keep.min(seg.len())].to_vec()),
                        Fate::Corrupt { at: i, xor } => {
                            let mut d = seg.to_vec();
                            let n = d.len();
                            if n > 0 {
                                d[i % n] ^= xor;
                            }
                            push(&mut link, at, d);
                        }
                    }
                }
            }
        }
        a.service(now);
        srv.iter_mut().for_each(|n| n.service(now));
        assert!(a.closed.is_none(), "the client closed: {:?}", a.closed);
        if opened {
            assert!(srv[0].closed.is_none(), "the server closed: {:?}", srv[0].closed);
        }
        let empty = Node::placeholder_read();
        let b_read = if opened { &srv[0].read } else { &empty.0 };
        let b_fin = if opened { &srv[0].fin } else { &empty.1 };
        let b_dgrams: &[Vec<u8>] = if opened { &srv[0].dgrams } else { &[] };
        check_prefix("the server", b_read, &a_outs);
        check_prefix("the client", &a.read, &b_outs);
        assert!(a.dgrams.is_empty(), "the client received a datagram it never was sent");
        {
            let mut ids = BTreeSet::new();
            for d in b_dgrams {
                let k = usize::from(d[0]);
                assert!(
                    k < sent_dgrams.len() && *d == sent_dgrams[k],
                    "the server received a datagram that was not sent"
                );
                assert!(ids.insert(k), "the server received datagram {k} twice");
            }
        }
        let done = opened
            && a_outs
                .iter()
                .all(|o| o.finished && b_fin.contains(&o.id) && b_read.get(&o.id).map_or(0, Vec::len) == o.data.len())
            && b_outs
                .iter()
                .all(|o| o.finished && a.fin.contains(&o.id) && a.read.get(&o.id).map_or(0, Vec::len) == o.data.len());
        let clean = chaos_until.is_some_and(|u| now >= u) && opened;
        if clean && clean_at.is_none() {
            clean_at = Some(now);
        }
        if done {
            break;
        }
        // The bytes left over a clean link: generous for slow start and the backed-off probe timer.
        let total: usize = c.client_streams.iter().map(|s| s.1).sum::<usize>() + c.server_streams.iter().sum::<usize>();
        let limit = 60 * SEC + (total as u64 / 100_000) * SEC + 40 * c.delay * MS;
        if let Some(t) = clean_at {
            assert!(
                now <= t + limit,
                "the transfer did not complete within {} s of a clean link: client read {:?}, server read {:?}",
                limit / SEC,
                a.read
                    .iter()
                    .map(|(k, v)| (*k, v.len(), a.fin.contains(k)))
                    .collect::<Vec<_>>(),
                b_read
                    .iter()
                    .map(|(k, v)| (*k, v.len(), b_fin.contains(k)))
                    .collect::<Vec<_>>()
            );
        } else {
            assert!(now <= T0 + 120 * SEC, "not connected after 120 s");
        }
        // Next instant.
        let next = [
            link.q.peek().map(|Reverse((t, ..))| *t),
            a.conn.poll_timeout(),
            srv.iter().filter_map(|n| n.conn.poll_timeout()).min(),
            chaos_until.filter(|u| *u > now),
        ]
        .into_iter()
        .flatten()
        .min();
        let Some(next) = next else {
            panic!(
                "nothing is scheduled and the transfer is not done (connected {} {b_up})",
                a.connected
            );
        };
        now = now.max(next);
        if now == last_now {
            same_time += 1;
            assert!(same_time < 20_000, "time does not advance at {now}: a timer stays due");
        } else {
            same_time = 0;
            last_now = now;
        }
    }
}

pub fn big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

pub fn case_size(c: &Case) -> u64 {
    let streams: usize =
        c.client_streams.iter().map(|s| s.1 + 1).sum::<usize>() + c.server_streams.iter().map(|s| s + 1).sum::<usize>();
    let fates = c.fates.len() + c.fates.iter().filter(|f| !matches!(f, Fate::Deliver)).count();
    let knobs = u64::from(c.knobs != Knobs::default_config());
    c.chaos + u64::from(c.early) + c.delay + knobs + (fates + streams + c.datagrams.len()) as u64
}

pub fn in_support(c: &Case) -> bool {
    !c.fates.is_empty()
        && c.client_streams.len() <= 4
        && c.server_streams.len() <= 2
        && c.datagrams.iter().all(|d| (1..=1100).contains(d))
}
