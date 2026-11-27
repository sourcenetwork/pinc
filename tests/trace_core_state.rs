//! Trace generation for the endpoint's saved state (`pinc-core` `state.rs`): seeded runs of a real endpoint, recorded as
//! ndjson (`core_state.ndjson`, numbers below 2^30, for the TLA+ trace check `TraceCoreState.tla`; `core_state_wide.ndjson`,
//! numbers up to 2^64 - 1, for the Lean replay only) for the Lean replay (`Pinc/TraceCoreState.lean`).
//!
//! An event is one call of the real endpoint: `restore` (the bytes it was given, the state it held before as the bytes
//! `export_state` wrote for it, the result and the state after the same way) or `export` (the state, the size of the
//! buffer and whether the export fitted). The bytes given are what the test's own writer makes of random states (tickets
//! of a few peers so that one peer's ticket is replaced and the store evicts, round trips of zero, expiry before, at and
//! after `now`, hundreds of peers so that the tables fill), that writer's output cut at every kind of place, with one
//! byte changed (the version, the lengths and counts, every tag, the length of an ALPN) or bytes appended, bytes that
//! claim a length or count the input does not hold, and garbage. The endpoint is reused between events, so most refused
//! inputs reach one that holds a state: a refused input must leave it as it was.
//!
//! The test compares every call with a naive reading of the format and of the tables in the test itself: the input is
//! accepted exactly when the naive parse reads one state (version 1, the three sections, known tags, an ALPN of 1 to
//! 32 bytes, nothing left over), a refused input leaves the exported bytes unchanged, and an accepted one gives
//! the bytes and the counts of the naive tables (a ticket that expired is skipped and one per peer is kept with the oldest evicted at
//! the bound, a round trip of 0 is skipped and a new peer is refused when the table is full, a prekey peer is replaced
//! in place or the oldest evicted).
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::large_stack_arrays,
    clippy::panic,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_core::{Endpoint, EndpointConfig, PEER_RTTS, PREKEY_PEERS, STATE_VERSION, Slot, StateError, state_len};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::{KeyHandle, LocalIdentity};
use pinc_tests::*;
use pinc_transport::conn::{Resources, Tables};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{self, NoSource, Streams};

/// The client ticket slots of the endpoint in the test.
const CT: usize = 3;

type Ep = Endpoint<'static, 'static, Caps, NoSource, 1, 2, 16, 1, 1, 2, 4, 4, CT>;
type TSlot = Slot<'static, Caps, NoSource, 1, 2, 16, 1>;

fn small_memory() -> Resources<'static, NoSource, 1, 2, 16> {
    let pool = BufferPool::new_boxed(4);
    let streams: &'static mut Streams<NoSource, 1, 2> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    Resources {
        pool,
        streams: streams.into(),
        loss: (&*Box::leak(Box::new(LossEstimate::new()))).into(),
        tables: Tables::new(),
    }
}

fn endpoint() -> Box<Ep> {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let v: Vec<TSlot> = (0..1).map(|_| Slot::new(small_memory())).collect();
    let slots: Box<[TSlot; 1]> = v.into_boxed_slice().try_into().ok().unwrap();
    Box::new(Endpoint::new(
        0,
        Caps(Software, true),
        Drbg::new(&[3; 32]),
        id,
        EndpointConfig::new(5),
        Box::leak(slots),
    ))
}

/// The state as the test reads and writes it (the order of a list is the order of the bytes, oldest first).
#[derive(Clone, Default, PartialEq, Eq, Debug)]
struct M {
    tk: Vec<Tk>,
    kr: Vec<(u8, [u8; 32], u64)>,
    ek: Vec<(u8, [u8; 32], [u8; 32])>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Tk {
    alg: u8,
    node: [u8; 32],
    alpn: Vec<u8>,
    tid: [u8; 16],
    psk: [u8; 32],
    aead: u8,
    expiry: u64,
    credit: [u8; 6],
}

fn put_tickets(m: &M) -> Vec<u8> {
    let mut t = vec![1u8, m.tk.len() as u8];
    for e in &m.tk {
        t.push(e.alg);
        t.extend_from_slice(&e.node);
        t.push(e.alpn.len() as u8);
        t.extend_from_slice(&e.alpn);
        t.extend_from_slice(&e.tid);
        t.extend_from_slice(&e.psk);
        t.push(e.aead);
        t.extend_from_slice(&e.expiry.to_be_bytes());
        t.extend_from_slice(&e.credit);
    }
    t
}

fn put(m: &M) -> Vec<u8> {
    let t = put_tickets(m);
    let mut o = vec![STATE_VERSION];
    o.extend_from_slice(&(t.len() as u32).to_be_bytes());
    o.extend_from_slice(&t);
    o.extend_from_slice(&(m.kr.len() as u16).to_be_bytes());
    for (a, n, r) in &m.kr {
        o.push(*a);
        o.extend_from_slice(n);
        o.extend_from_slice(&r.to_be_bytes());
    }
    o.extend_from_slice(&(m.ek.len() as u16).to_be_bytes());
    for (a, n, h) in &m.ek {
        o.push(*a);
        o.extend_from_slice(n);
        o.extend_from_slice(h);
    }
    o
}

struct Rd<'a>(&'a [u8]);

impl<'a> Rd<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        if n > self.0.len() {
            return None;
        }
        let (a, b) = self.0.split_at(n);
        self.0 = b;
        Some(a)
    }

    fn num(&mut self, n: usize) -> Option<u64> {
        Some(self.take(n)?.iter().fold(0u64, |a, b| (a << 8) | u64::from(*b)))
    }

    fn arr<const N: usize>(&mut self) -> Option<[u8; N]> {
        self.take(N)?.try_into().ok()
    }
}

/// The naive parse: one state or nothing.
fn parse(b: &[u8]) -> Option<M> {
    let mut r = Rd(b);
    if r.num(1)? != u64::from(STATE_VERSION) {
        return None;
    }
    let tlen = r.num(4)? as usize;
    let tb = r.take(tlen)?;
    let nk = r.num(2)? as usize;
    let kb = r.take(nk * 41)?;
    let ne = r.num(2)? as usize;
    let eb = r.take(ne * 65)?;
    if !r.0.is_empty() {
        return None;
    }
    let mut m = M::default();
    let mut t = Rd(tb);
    if t.num(1)? != 1 {
        return None;
    }
    let n = t.num(1)? as usize;
    for _ in 0..n {
        let alg = t.num(1)? as u8;
        if !(1..=4).contains(&alg) {
            return None;
        }
        let node = t.arr::<32>()?;
        let l = t.num(1)? as usize;
        if !(1..=32).contains(&l) {
            return None;
        }
        let alpn = t.take(l)?.to_vec();
        let tid = t.arr::<16>()?;
        let psk = t.arr::<32>()?;
        let aead = t.num(1)? as u8;
        if !(1..=2).contains(&aead) {
            return None;
        }
        let expiry = t.num(8)?;
        let credit = t.arr::<6>()?;
        m.tk.push(Tk {
            alg,
            node,
            alpn,
            tid,
            psk,
            aead,
            expiry,
            credit,
        });
    }
    if !t.0.is_empty() {
        return None;
    }
    let mut k = Rd(kb);
    for _ in 0..nk {
        let alg = k.num(1)? as u8;
        if !(1..=4).contains(&alg) {
            return None;
        }
        m.kr.push((alg, k.arr::<32>()?, k.num(8)?));
    }
    let mut e = Rd(eb);
    for _ in 0..ne {
        let alg = e.num(1)? as u8;
        if !(1..=4).contains(&alg) {
            return None;
        }
        m.ek.push((alg, e.arr::<32>()?, e.arr::<32>()?));
    }
    Some(m)
}

/// The tables after a restore of `inp` at `now`, and what the restore reports. The ticket count is the tickets of
/// the input this restore left in the store: one replaced by a later ticket of the same peer, or evicted by a later
/// one at the bound, is not counted, nor is any ticket the store held before.
fn apply(live: &mut M, inp: &M, now: u64) -> (usize, usize, usize) {
    let mut fresh = vec![false; live.tk.len()];
    for t in &inp.tk {
        if t.expiry >= now {
            if let Some(i) = live.tk.iter().position(|o| (o.alg, o.node) == (t.alg, t.node)) {
                live.tk.remove(i);
                fresh.remove(i);
            } else if live.tk.len() == CT {
                live.tk.remove(0);
                fresh.remove(0);
            }
            live.tk.push(t.clone());
            fresh.push(true);
        }
    }
    let stored = fresh.iter().filter(|f| **f).count();
    let mut peers = 0;
    for (a, n, r) in &inp.kr {
        if *r > 0 {
            if let Some(o) = live.kr.iter_mut().find(|o| (o.0, o.1) == (*a, *n)) {
                o.2 = *r;
                peers += 1;
            } else if live.kr.len() < PEER_RTTS {
                live.kr.push((*a, *n, *r));
                peers += 1;
            }
        }
    }
    for (a, n, h) in &inp.ek {
        if let Some(o) = live.ek.iter_mut().find(|o| (o.0, o.1) == (*a, *n)) {
            o.2 = *h;
        } else {
            if live.ek.len() == PREKEY_PEERS {
                live.ek.remove(0);
            }
            live.ek.push((*a, *n, *h));
        }
    }
    (stored, peers, inp.ek.len())
}

fn array(b: &[u8]) -> String {
    let parts: Vec<String> = b.iter().map(ToString::to_string).collect();
    format!("[{}]", parts.join(","))
}

struct Run {
    ep: Box<Ep>,
    live: M,
    now: u64,
    out: String,
}

impl Run {
    fn export(&mut self) -> Vec<u8> {
        let mut buf = vec![0u8; state_len(CT)];
        let n = self.ep.export_state(self.now, &mut buf).unwrap();
        buf.truncate(n);
        buf
    }

    /// Move the clock: a ticket that expired is no longer written.
    fn tick(&mut self, now: u64) {
        self.now = now;
        let n = now;
        self.live.tk.retain(|t| t.expiry >= n);
    }

    fn check_export(&mut self) -> Vec<u8> {
        let b = self.export();
        assert_eq!(
            b,
            put(&self.live),
            "the exported state is the tables of the naive model"
        );
        b
    }

    /// An export into a buffer of `cap` bytes.
    fn export_cap(&mut self, cap: usize) {
        let pre = self.check_export();
        let mut buf = vec![0u8; cap];
        let r = self.ep.export_state(self.now, &mut buf);
        let ok = r.is_ok();
        assert_eq!(
            ok,
            cap >= pre.len(),
            "an export fits exactly when the buffer holds the state"
        );
        match r {
            Ok(n) => assert_eq!(&buf[..n], &pre[..]),
            Err(e) => assert_eq!(e, StateError::BufferTooSmall),
        }
        assert_eq!(self.export(), pre, "an export changes nothing");
        let _ = writeln!(
            self.out,
            r#"{{"t":"cs","op":"export","now":{},"pre":{},"cap":{cap},"ok":{ok}}}"#,
            self.now,
            array(&pre)
        );
    }

    fn restore(&mut self, inp: &[u8]) -> bool {
        let pre = self.check_export();
        let want = parse(inp);
        let r = self.ep.restore_state(self.now, inp);
        assert_eq!(r.is_ok(), want.is_some(), "accepted exactly what the naive parse reads");
        let res = match (&r, want) {
            (Ok(rs), Some(inp_state)) => {
                let (t, p, k) = apply(&mut self.live, &inp_state, self.now);
                assert_eq!((rs.tickets, rs.peers, rs.prekeys), (t, p, k));
                format!("[{t},{p},{k}]")
            }
            (Err(e), None) => {
                assert_eq!(*e, StateError::Malformed);
                "[]".to_string()
            }
            _ => unreachable!(),
        };
        let post = self.check_export();
        if r.is_err() {
            assert_eq!(post, pre, "a refused state changes nothing");
        }
        let _ = writeln!(
            self.out,
            r#"{{"t":"cs","op":"restore","now":{},"pre":{},"in":{},"ok":{},"res":{res},"post":{}}}"#,
            self.now,
            array(&pre),
            array(inp),
            r.is_ok(),
            array(&post)
        );
        r.is_ok()
    }
}

/// How the numbers of a run are drawn: below 2^30, or anywhere up to 2^64 - 1.
#[derive(Clone, Copy)]
struct Gen {
    wide: bool,
}

fn node(i: u64) -> (u8, [u8; 32]) {
    let mut n = [0u8; 32];
    for (j, b) in n.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(7).wrapping_add(j as u8);
    }
    n[0] = i as u8;
    n[1] = (i >> 8) as u8;
    (1 + (i % 4) as u8, n)
}

fn fill(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    rng.fill(&mut v);
    v
}

impl Gen {
    fn expiry(self, rng: &mut SplitMix64, now: u64) -> u64 {
        match rng.next_u64() % 8 {
            0 => now.saturating_sub(1),
            1 => now,
            2 => now.saturating_add(1),
            3 if self.wide => u64::MAX,
            4 => 0,
            _ => now.saturating_add(1 + rng.next_u64() % 1000),
        }
    }

    fn rtt(self, rng: &mut SplitMix64) -> u64 {
        match rng.next_u64() % 6 {
            0 => 0,
            1 if self.wide => u64::MAX,
            2 if self.wide => rng.next_u64(),
            _ => 1 + rng.next_u64() % 500_000,
        }
    }

    fn ticket(self, rng: &mut SplitMix64, now: u64, pool: u64) -> Tk {
        let (alg, n) = node(rng.next_u64() % pool);
        let l = match rng.next_u64() % 5 {
            0 => 1,
            1 => 32,
            _ => 1 + (rng.next_u64() % 32) as usize,
        };
        Tk {
            alg,
            node: n,
            alpn: fill(rng, l),
            tid: fill(rng, 16).try_into().unwrap(),
            psk: fill(rng, 32).try_into().unwrap(),
            aead: 1 + (rng.next_u64() % 2) as u8,
            expiry: self.expiry(rng, now),
            credit: fill(rng, 6).try_into().unwrap(),
        }
    }

    /// A state a host could have saved, or near it: few peers (so a peer repeats), some with a round trip of 0.
    fn state(self, rng: &mut SplitMix64, now: u64) -> M {
        let pool = 2 + rng.next_u64() % 6;
        let nt = (rng.next_u64() % (CT as u64 + 4)) as usize;
        let nk = (rng.next_u64() % 7) as usize;
        let ne = (rng.next_u64() % 7) as usize;
        M {
            tk: (0..nt).map(|_| self.ticket(rng, now, pool)).collect(),
            kr: (0..nk)
                .map(|_| {
                    let (a, n) = node(rng.next_u64() % (pool + 2));
                    (a, n, self.rtt(rng))
                })
                .collect(),
            ek: (0..ne)
                .map(|_| {
                    let (a, n) = node(rng.next_u64() % (pool + 2));
                    (a, n, fill(rng, 32).try_into().unwrap())
                })
                .collect(),
        }
    }

    /// Hundreds of peers: the tables of round trips and prekey peers fill and run over.
    fn big(self, rng: &mut SplitMix64, now: u64, base: u64, extra: usize) -> M {
        let nk = PEER_RTTS - 3 + extra;
        let ne = PREKEY_PEERS - 3 + extra;
        M {
            tk: (0..CT + 2).map(|_| self.ticket(rng, now, 9)).collect(),
            kr: (0..nk)
                .map(|i| {
                    let (a, n) = node(base + i as u64);
                    (a, n, 1 + rng.next_u64() % 1000)
                })
                .collect(),
            ek: (0..ne)
                .map(|i| {
                    let (a, n) = node(base + 500 + i as u64);
                    (a, n, fill(rng, 32).try_into().unwrap())
                })
                .collect(),
        }
    }
}

/// The places of a state's bytes whose change matters: every length, count, tag and flag.
fn places(m: &M) -> Vec<usize> {
    let mut p = vec![0, 1, 2, 3, 4, 5, 6];
    let mut at = 7;
    for t in &m.tk {
        p.extend([at, at + 33]);
        let l = t.alpn.len();
        p.push(at + 34 + l + 16 + 32);
        p.push(at + 34 + l + 16 + 32 + 1 + 7);
        at += 34 + l + 16 + 32 + 1 + 8 + 6;
    }
    p.extend([at, at + 1]);
    at += 2;
    for _ in &m.kr {
        p.extend([at, at + 1, at + 40]);
        at += 41;
    }
    p.extend([at, at + 1]);
    at += 2;
    for _ in &m.ek {
        p.extend([at, at + 1, at + 64]);
        at += 65;
    }
    p
}

/// An input made from `bytes` (an encoding of `m`) by one of the kinds of damage.
fn damage(rng: &mut SplitMix64, m: &M, bytes: &[u8]) -> Vec<u8> {
    let mut b = bytes.to_vec();
    let pl = places(m);
    let at = |rng: &mut SplitMix64| pl[(rng.next_u64() % pl.len() as u64) as usize].min(b.len().saturating_sub(1));
    match rng.next_u64() % 12 {
        0 | 1 => {
            let i = at(rng);
            b[i] = [0, 1, 2, 4, 5, 32, 33, 255][(rng.next_u64() % 8) as usize];
        }
        2 => {
            let i = at(rng);
            b[i] = b[i].wrapping_add(1);
        }
        3 => {
            let i = (rng.next_u64() % b.len() as u64) as usize;
            b[i] = rng.next_u64() as u8;
        }
        4 => b.truncate((rng.next_u64() % b.len() as u64) as usize),
        5 => {
            let i = at(rng);
            b.truncate(i);
        }
        6 => b.truncate(b.len() - 1),
        7 => {
            let n = 1 + (rng.next_u64() % 5) as usize;
            b.extend(fill(rng, n));
        }
        8 => {
            // a claimed length no input holds
            let v = [u32::MAX, 0x8000_0000, bytes.len() as u32, 0][(rng.next_u64() % 4) as usize];
            b[1..5].copy_from_slice(&v.to_be_bytes());
        }
        9 => {
            // one more or one fewer than the tickets section holds
            let t = u32::from_be_bytes(b[1..5].try_into().unwrap());
            let v = if rng.next_u64().is_multiple_of(2) {
                t + 1
            } else {
                t.saturating_sub(1)
            };
            b[1..5].copy_from_slice(&v.to_be_bytes());
        }
        10 => {
            // the count of round trips or of prekey peers one off or at its limit
            let tl = u32::from_be_bytes(b[1..5].try_into().unwrap()) as usize;
            let i = 5
                + tl
                + if rng.next_u64().is_multiple_of(2) {
                    0
                } else {
                    2 + 41 * m.kr.len()
                };
            if i + 1 < b.len() {
                let v = u16::from_be_bytes([b[i], b[i + 1]]);
                let v = [v.wrapping_add(1), v.wrapping_sub(1), u16::MAX, 0][(rng.next_u64() % 4) as usize];
                b[i..i + 2].copy_from_slice(&v.to_be_bytes());
            }
        }
        _ => {
            let i = at(rng);
            b[i] = b[i].wrapping_add(255);
        }
    }
    b
}

fn garbage(rng: &mut SplitMix64) -> Vec<u8> {
    let n = (rng.next_u64() % 70) as usize;
    let mut v = fill(rng, n);
    if rng.next_u64().is_multiple_of(2) && !v.is_empty() {
        v[0] = STATE_VERSION;
    }
    v
}

fn run(rng: &mut SplitMix64, id: u64, wide: bool, out: &mut String) {
    let g = Gen { wide };
    let now = if wide {
        u64::MAX / 2 + rng.next_u64() % 1_000_000
    } else {
        1_000 + rng.next_u64() % 1_000_000
    };
    let mut r = Run {
        ep: endpoint(),
        live: M::default(),
        now,
        out: String::new(),
    };
    // The empty endpoint exports the empty state, and the buffer sizes around it.
    let empty = r.check_export();
    assert_eq!(empty.len(), 11);
    for cap in [0, 1, 5, 6, 10, 11, 12, state_len(CT)] {
        r.export_cap(cap);
    }
    let big = id.is_multiple_of(20);
    let steps: u64 = if big { 5 } else { 22 };
    for step in 0..steps {
        // the clock moves, never back
        if rng.next_u64().is_multiple_of(3) {
            let n = r.now.saturating_add(rng.next_u64() % 2000);
            r.tick(n);
        }
        let m = if big && step < 2 {
            g.big(rng, r.now, 1000 * id + 3 * step, usize::from(step == 0) * 5)
        } else {
            g.state(rng, r.now)
        };
        let good = put(&m);
        match rng.next_u64() % 6 {
            0 => {
                // the endpoint's own export is a state it restores, into itself and into a fresh endpoint
                let own = r.check_export();
                assert!(r.restore(&own));
                let mut f = Run {
                    ep: endpoint(),
                    live: M::default(),
                    now: r.now,
                    out: String::new(),
                };
                assert!(f.restore(&own));
                assert_eq!(f.live, parse(&own).unwrap(), "a fresh endpoint restores what was saved");
                r.out.push_str(&f.out);
            }
            1 => {
                r.restore(&garbage(rng));
            }
            2 | 3 => {
                let d = damage(rng, &m, &good);
                r.restore(&d);
            }
            _ => {
                r.restore(&good);
            }
        }
        if step % 5 == 4 {
            let n = r.check_export().len();
            r.export_cap(n.saturating_sub(1));
            r.export_cap(n);
        }
    }
    assert!(r.live.tk.len() <= CT && r.live.kr.len() <= PEER_RTTS && r.live.ek.len() <= PREKEY_PEERS);
    out.push_str(&r.out);
}

#[test]
fn saved_state_matches_the_models() {
    let mut rng = SplitMix64::new(0x4353_0001);
    let mut small = String::new();
    let mut wide = String::new();
    for id in 1..=70u64 {
        run(&mut rng, id, false, &mut small);
    }
    for id in 1..=14u64 {
        run(&mut rng, id, true, &mut wide);
    }
    for s in [&small, &wide] {
        assert!(s.contains(r#""ok":true,"res":["#) && s.contains(r#""ok":false,"res":[]"#));
        assert!(s.contains(r#""op":"export""#));
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("core_state.ndjson"), &small).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("core_state_wide.ndjson"), &wide).unwrap();
    }
}
