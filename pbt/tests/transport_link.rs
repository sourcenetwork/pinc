//! `pinc-transport` end to end: two real connections (a client and a server, the public API an application uses)
//! joined by a link whose every datagram is delivered, dropped, repeated, delayed past later ones, cut short or
//! corrupted by a generated schedule, on virtual time. After a stretch of chaos the link turns clean.
//!
//! Where the expected behaviour comes from:
//! - `conn` module docs: "running out drops data (a received packet is not acknowledged, so the peer sends it again)
//!   and never overflows. Nothing allocates per packet and no input panics"; "A datagram never exceeds the datagram
//!   size of its path".
//! - `stream` module docs and `Connection::write` / `read_chunk` / `consume`: a stream delivers the bytes written,
//!   in order, once; the end is seen after the last byte (`RecvStatus::Finished`).
//! - `stream::datagram`: an unreliable datagram arrives at most once and unchanged (a duplicate packet is dropped by
//!   the received-packet set: "a forgotten packet is dropped as a duplicate rather than processed twice").
//! - Universal: neither side closes the connection on a link that loses at most part of its datagrams for a few
//!   seconds (the idle timeout is 75 s); after the link turns clean the transfer completes within a bounded span of
//!   virtual time; the driver loop makes progress (a timer that fired moves on).
#![allow(
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
    AlpnList, Env, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys, SoftPrekeys,
};
use pinc_transport::conn::{
    ClientParams, CloseReason, Config, Connection, Event, Lent, PathId, PathInfo, Resources, ServerParams, Tables,
    Transmit,
};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::spill::SpillArena;
use pinc_transport::stream::{self, NoSource, RecvStatus, Streams};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000_000_000;
const T0: u64 = 1_000_000_000_000;
const ALPN: &[u8] = b"pinc/1";

type Table = Streams<NoSource, 64, 257>;
type Conn<'a> = Connection<'a, Software, NoSource, 64, 257, 512, 4>;
type Stores = ResponderStores<8, 512>;

/// What the link does to one datagram while the chaos lasts.
#[derive(Clone, Debug, Arbitrary)]
enum Fate {
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
struct Case {
    /// One-way delay of the clean link, ms.
    delay: u64,
    /// Chaos length after both sides connected, ms; chaos also during the handshake when `early`.
    chaos: u64,
    early: bool,
    /// The schedule, used in turn for each datagram while the chaos lasts.
    fates: Vec<Fate>,
    /// Client-opened streams: (bidirectional, length).
    client_streams: Vec<(bool, usize)>,
    /// Server-opened unidirectional streams.
    server_streams: Vec<usize>,
    /// Datagrams the client sends, by length.
    datagrams: Vec<usize>,
    chunks: usize,
}

fn case() -> impl Gen<Value = Case> {
    (
        gens::frequency(vec![(3, gens::int(0u64..=30).boxed()), (1, gens::int(0u64..=300).boxed())]),
        gens::int(0u64..=8000),
        gens::bool_with(0.3),
        gens::vec(gens::frequency(vec![
            (8, gens::constant(Fate::Deliver).boxed()),
            (6, ephyra::any::<Fate>().boxed()),
        ]))
        .len(1..=40),
        gens::vec((gens::bool(), gens::frequency(vec![(2, gens::int(0usize..=3000).boxed()), (1, gens::int(0usize..=400_000).boxed())]))).len(0..=4),
        gens::vec(gens::frequency(vec![(2, gens::int(0usize..=3000).boxed()), (1, gens::int(0usize..=200_000).boxed())])).len(0..=2),
        gens::vec(gens::int(1usize..=1100)).len(0..=6),
        gens::pick_from(vec![64usize, 256, 1024]),
    )
        .map(|(delay, chaos, early, fates, client_streams, server_streams, datagrams, chunks)| Case {
            delay,
            chaos,
            early,
            fates,
            client_streams,
            server_streams,
            datagrams,
            chunks,
        })
        .with_shrink(shrink_case)
}

fn shrink_case(c: &Case, visit: &mut dyn FnMut(Case) -> std::ops::ControlFlow<()>) -> std::ops::ControlFlow<()> {
    if c.chaos > 0 {
        visit(Case { chaos: c.chaos / 2, ..c.clone() })?;
    }
    if c.early {
        visit(Case { early: false, ..c.clone() })?;
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
        visit(Case { client_streams: s, ..c.clone() })?;
        if c.client_streams[i].1 > 0 {
            let mut s = c.client_streams.clone();
            s[i].1 /= 2;
            visit(Case { client_streams: s, ..c.clone() })?;
        }
    }
    for i in 0..c.server_streams.len() {
        let mut s = c.server_streams.clone();
        s.remove(i);
        visit(Case { server_streams: s, ..c.clone() })?;
    }
    for i in 0..c.datagrams.len() {
        let mut s = c.datagrams.clone();
        s.remove(i);
        visit(Case { datagrams: s, ..c.clone() })?;
    }
    if c.delay > 0 {
        visit(Case { delay: c.delay / 2, ..c.clone() })?;
    }
    std::ops::ControlFlow::Continue(())
}

fn pattern(len: usize, seed: u64) -> Vec<u8> {
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
struct Node<'a> {
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
                    _ => {},
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

/// A datagram on the link: (arrival time, sequence, to the client, bytes).
type InFlight = Reverse<(u64, u64, bool, Vec<u8>)>;

struct Link {
    q: BinaryHeap<InFlight>,
    seq: u64,
    sent: u64,
}

/// One writer of a stream: what to write and how far it got.
struct Out {
    id: u64,
    data: Vec<u8>,
    off: usize,
    finished: bool,
}

fn write_out(conn: &mut Conn<'_>, outs: &mut [Out]) {
    for o in outs.iter_mut() {
        while o.off < o.data.len() {
            let end = (o.off + 64 * 1024).min(o.data.len());
            match conn.write(o.id, &o.data[o.off..end]) {
                Ok(0) => break,
                Ok(n) => {
                    assert!(n <= end - o.off, "write took more than it was given");
                    o.off += n;
                },
                Err(e) => panic!("write on stream {} refused: {e:?}", o.id),
            }
        }
        if o.off == o.data.len() && !o.finished {
            assert_eq!(conn.finish(o.id), Ok(()), "finish of stream {}", o.id);
            o.finished = true;
        }
    }
}

fn check_prefix(side: &str, read: &BTreeMap<u64, Vec<u8>>, outs: &[Out]) {
    for (id, got) in read {
        let o = outs.iter().find(|o| o.id == *id);
        assert!(o.is_some(), "{side} read stream {id}, which nobody wrote");
        let o = o.unwrap();
        assert!(got.len() <= o.data.len(), "{side} read {} bytes of stream {id}, {} written", got.len(), o.data.len());
        assert!(*got == o.data[..got.len()], "{side} read bytes on stream {id} other than those written");
    }
}

fn run(c: &Case) {
    let alg = IdentityAlg::Ed25519;
    let ckp = Keypair::from_seed(alg, &vec![0x21; alg.seed_len()]).unwrap();
    let skp = Keypair::from_seed(alg, &vec![0x22; alg.seed_len()]).unwrap();
    let cid = LocalIdentity::from_keypair(&ckp, KeyHandle(1)).unwrap();
    let sid = LocalIdentity::from_keypair(&skp, KeyHandle(1)).unwrap();
    let mut stores: Box<Stores> = Box::default();
    let mut ctab = Box::new(Table::new(&stream::Config::new(true), &BufferPool::new_boxed(c.chunks)));
    let mut stab = Box::new(Table::new(&stream::Config::new(false), &BufferPool::new_boxed(c.chunks)));
    let (closs, sloss) = (LossEstimate::new(), LossEstimate::new());
    let cfg = Config::new();
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
    let mut sdrbg = Drbg::new(&[0x33; 32]);
    let mut env = Env {
        provider: &prov,
        now: T0,
        drbg: &mut sdrbg,
    };
    let server = Conn::server(
        cfg,
        &ServerParams {
            identity: sid,
            alpns: AlpnList::new(&[ALPN]).unwrap(),
            tickets_per_session: 1,
            ticket_lifetime_s: 86_400,
        },
        Resources {
            pool: BufferPool::new_boxed(c.chunks),
            streams: (&mut *stab).into(),
            loss: (&sloss).into(),
            tables: Tables::new(),
        },
        &mut env,
    )
    .unwrap();
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
    let mut b = Node {
        conn: server,
        prov,
        drbg: sdrbg,
        kp: skp,
        prekeys: None,
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

    loop {
        iterations += 1;
        assert!(iterations < 3_000_000, "the driver loop ran 3,000,000 turns");
        // Deliver what is due.
        while let Some(Reverse((at, _, _, _))) = link.q.peek() {
            if *at > now {
                break;
            }
            let Reverse((_, _, to_a, mut d)) = link.q.pop().unwrap();
            let node = if to_a { &mut a } else { &mut b };
            let mut env = Env {
                provider: &node.prov,
                now,
                drbg: &mut node.drbg,
            };
            let mut lent = Lent { spill: &mut node.spill };
            let _ = if to_a {
                node.conn.handle_datagram(&mut env, &mut lent, PathId(1), &mut d)
            } else {
                node.conn.handle_datagram_with(&mut env, &mut lent, &mut stores, PathId(1), &mut d)
            };
        }
        // Timers.
        for node in [&mut a, &mut b] {
            if node.conn.poll_timeout().is_some_and(|t| t <= now) {
                let mut env = Env {
                    provider: &node.prov,
                    now,
                    drbg: &mut node.drbg,
                };
                node.conn.handle_timeout(&mut env, &mut Lent { spill: &mut node.spill });
            }
        }
        a.service(now);
        b.service(now);
        if a.connected && b.connected && !opened {
            opened = true;
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
                let id = b.conn.open_uni().unwrap_or_else(|e| panic!("open of server stream {i} refused: {e:?}"));
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
        for to_a in [false, true] {
            let node = if to_a { &mut b } else { &mut a };
            loop {
                let mut env = Env {
                    provider: &node.prov,
                    now,
                    drbg: &mut node.drbg,
                };
                let Some(Transmit { len, segment_size, .. }) =
                    node.conn.poll_transmit(&mut env, &mut Lent { spill: &mut node.spill }, &mut buf)
                else {
                    break;
                };
                assert!(len <= buf.len() && segment_size > 0, "a transmit of {len} bytes in segments of {segment_size}");
                for seg in buf[..len].chunks(segment_size) {
                    assert!(seg.len() <= 1500, "a datagram of {} bytes", seg.len());
                    link.sent += 1;
                    let chaotic = chaos_until.is_none_or(|u| now < u) && (c.early || opened);
                    let fate = if chaotic {
                        c.fates[(link.sent as usize) % c.fates.len()].clone()
                    } else {
                        Fate::Deliver
                    };
                    let at = now + c.delay * MS;
                    let push = |link: &mut Link, at: u64, d: Vec<u8>| {
                        link.seq += 1;
                        link.q.push(Reverse((at, link.seq, to_a, d)));
                    };
                    match fate {
                        Fate::Deliver => push(&mut link, at, seg.to_vec()),
                        Fate::Drop => {},
                        Fate::Dup(later) => {
                            push(&mut link, at, seg.to_vec());
                            push(&mut link, at + later * MS, seg.to_vec());
                        },
                        Fate::Hold(extra) => push(&mut link, at + extra * MS, seg.to_vec()),
                        Fate::Truncate(keep) => push(&mut link, at, seg[..keep.min(seg.len())].to_vec()),
                        Fate::Corrupt { at: i, xor } => {
                            let mut d = seg.to_vec();
                            let n = d.len();
                            if n > 0 {
                                d[i % n] ^= xor;
                            }
                            push(&mut link, at, d);
                        },
                    }
                }
            }
        }
        a.service(now);
        b.service(now);
        assert!(a.closed.is_none(), "the client closed: {:?}", a.closed);
        assert!(b.closed.is_none(), "the server closed: {:?}", b.closed);
        check_prefix("the server", &b.read, &a_outs);
        check_prefix("the client", &a.read, &b_outs);
        assert!(a.dgrams.is_empty(), "the client received a datagram it never was sent");
        {
            let mut ids = BTreeSet::new();
            for d in &b.dgrams {
                let k = usize::from(d[0]);
                assert!(k < sent_dgrams.len() && *d == sent_dgrams[k], "the server received a datagram that was not sent");
                assert!(ids.insert(k), "the server received datagram {k} twice");
            }
        }
        let done = opened
            && a_outs.iter().all(|o| o.finished && b.fin.contains(&o.id) && b.read.get(&o.id).map_or(0, Vec::len) == o.data.len())
            && b_outs.iter().all(|o| o.finished && a.fin.contains(&o.id) && a.read.get(&o.id).map_or(0, Vec::len) == o.data.len());
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
                a.read.iter().map(|(k, v)| (*k, v.len(), a.fin.contains(k))).collect::<Vec<_>>(),
                b.read.iter().map(|(k, v)| (*k, v.len(), b.fin.contains(k))).collect::<Vec<_>>()
            );
        } else {
            assert!(now <= T0 + 120 * SEC, "not connected after 120 s");
        }
        // Next instant.
        let next = [
            link.q.peek().map(|Reverse((t, ..))| *t),
            a.conn.poll_timeout(),
            b.conn.poll_timeout(),
            chaos_until.filter(|u| *u > now),
        ]
        .into_iter()
        .flatten()
        .min();
        let Some(next) = next else {
            panic!(
                "nothing is scheduled and the transfer is not done (connected {} {})",
                a.connected, b.connected
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

fn big_stack(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn two_connections_deliver_every_byte_over_a_scripted_link() {
    big_stack(|| {
        let config = ephyra::Config::default().tests(150).name("two_connections_deliver_every_byte_over_a_scripted_link");
        ephyra::check(&config, case(), |c: Case| run(&c)).assert_passed();
    });
}

fn case_size(c: &Case) -> u64 {
    let streams: usize = c.client_streams.iter().map(|s| s.1 + 1).sum::<usize>() + c.server_streams.iter().map(|s| s + 1).sum::<usize>();
    let fates = c.fates.len() + c.fates.iter().filter(|f| !matches!(f, Fate::Deliver)).count();
    c.chaos + u64::from(c.early) + c.delay + (fates + streams + c.datagrams.len()) as u64
}

fn in_support(c: &Case) -> bool {
    !c.fates.is_empty() && c.client_streams.len() <= 4 && c.server_streams.len() <= 2 && c.datagrams.iter().all(|d| (1..=1100).contains(d))
}

#[test]
fn the_link_case_generator_and_shrinker_stay_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    ephyra::check_generator(&cfg, case(), in_support).assert_passed();
    ephyra::check_shrinker(&cfg, case(), in_support, case_size).assert_passed();
}
