//! Trace generation for the datagrams out of an endpoint: recorded `poll_transmit` calls of a real `pinc-core` endpoint
//! (built with the `trace` feature) with four peers, written as ndjson (`tx.ndjson`) for the TLA+ trace check
//! (`TraceTx.tla`).
//!
//! Node 0 holds sessions to nodes 1 to 3 (equal and mixed writes, buffers from 64 bytes to 65536, broadcast sessions
//! with and without a sub-session open, a slot freed while queued, a kept datagram dropped, rejects, and 200 seeded
//! calls). Each call is recorded with the queues, the kept datagram and the broadcast flags before it, the steps the
//! endpoint took (the session asked, the size sent to the ledger, the drops, the queue moves, the rejects) and the
//! queues and kept datagram after it; the checker replays each call step by step. A destination is written as the id
//! of the node that owns the address.
//!
//! The test asserts what it can itself: no record was lost, a result is one run of equal-size datagrams that fits the
//! buffer and the segment limit, no session waits twice, every datagram taken from a connection is gated, dropped or
//! kept, and the datagrams the ledger let out are the datagrams of the result. Further tests build the moves
//! between the two queues: a session served alone whose class changed, and a waiting session whose class became
//! ordinary.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::large_stack_arrays,
    unreachable_pub,
    clippy::cast_sign_loss,
    clippy::panic
)]

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::net::SocketAddr;

use pinc_core::{Answer, Command, Event, MAX_DATAGRAM, Query, Role, SessionId, TraceEvent, Transmit, Value};
use pinc_crypto::Aead;
use pinc_security::message::ResumeHello;
use pinc_security::{ConnId, CreditRecord, VERSION};
use pinc_tests::*;
use pinc_wire::Writer;

/// `max_gso` of a `CoreNet` node.
const LIM: usize = 4;
const NONE: u64 = u64::MAX;

/// A long handshake datagram of at least `len` bytes (zero padded) that carries the whole `message` as its first
/// fragment, as a dialer's first packet does.
fn first_datagram(odcid: u64, message: &[u8], len: usize) -> Vec<u8> {
    let dcid = ConnId::new(&odcid.to_be_bytes()).unwrap();
    let mut head = [0u8; 16];
    let mut w = Writer::new(&mut head);
    w.put_varint(message.len() as u64).unwrap();
    w.put_varint(0).unwrap();
    let mut body = w.written().to_vec();
    body.extend_from_slice(message);
    let d = forge_packet(dcid, &body);
    if d.len() >= len {
        return d;
    }
    body.resize(body.len() + len - d.len(), 0);
    forge_packet(dcid, &body)
}

/// A well-formed resumption Hello for a ticket nobody issued: random ticket id, key and binder.
fn forged_hello(seed: u64) -> Vec<u8> {
    hello_naming(None, seed)
}

/// The same forged Hello, naming ticket `named` when given.
fn hello_naming(named: Option<[u8; 16]>, seed: u64) -> Vec<u8> {
    let mut rng = SplitMix64::new(seed);
    let (mut tid, mut e, mut binder) = ([0u8; 16], [0u8; 32], [0u8; 32]);
    rng.fill(&mut tid);
    tid = named.unwrap_or(tid);
    rng.fill(&mut e);
    rng.fill(&mut binder);
    let cid = ConnId::new(&[1, 2, 3, 4]).unwrap();
    let hello = ResumeHello {
        version: VERSION,
        dcid: cid,
        scid: cid,
        alpn: ALPN_A,
        aead: Aead::ChaCha20Poly1305,
        tid,
        e,
        binder,
        credit: CreditRecord::NONE,
    };
    let mut buf = [0u8; 256];
    let mut w = Writer::new(&mut buf);
    hello.write(&mut w).unwrap();
    w.written().to_vec()
}

/// The number a trace line carries for an IPv4 address (`addr_key` of `pinc-core`).
fn key(a: SocketAddr) -> u64 {
    match a {
        SocketAddr::V4(v) => u64::from(u32::from(*v.ip())) << 16 | u64::from(v.port()),
        SocketAddr::V6(_) => panic!("every address of the test is IPv4"),
    }
}

fn drain(net: &mut CoreNet) -> Vec<TraceEvent> {
    let mut v = Vec::new();
    while let Some(r) = net.nodes[0].ep.poll_trace() {
        v.push(r.event);
    }
    v
}

fn list<T: std::fmt::Display>(v: impl IntoIterator<Item = T>) -> String {
    format!(
        "[{}]",
        v.into_iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
    )
}

/// One step the endpoint took in a call, with the eleven fields of the line.
#[derive(Default, Clone)]
struct Step {
    k: &'static str,
    slot: i64,
    room: u64,
    has: bool,
    d: u64,
    len: u64,
    seg: u64,
    segs: u64,
    n: u64,
    ok: bool,
    q: u64,
}

impl Step {
    fn json(&self) -> String {
        format!(
            r#"{{"k":"{}","slot":{},"room":{},"has":{},"d":{},"len":{},"seg":{},"segs":{},"n":{},"ok":{},"q":{}}}"#,
            self.k, self.slot, self.room, self.has, self.d, self.len, self.seg, self.segs, self.n, self.ok, self.q
        )
    }
}

#[derive(Default)]
struct Summary {
    calls: u32,
    results: u32,
    joins: u32,
    kept: u32,
    drops: u32,
    stash_drops: u32,
    rejects: u32,
    gone: u32,
    broadcast_served: u32,
    writes_failed: u32,
}

struct Tracer {
    net: CoreNet,
    ids: HashMap<u64, u64>,
    next_id: u64,
    out: String,
    st: Summary,
    streams: HashMap<SessionId, u64>,
    /// Whether the last recorded call left a datagram kept.
    kept_now: bool,
}

impl Tracer {
    fn new(net: CoreNet) -> Self {
        let mut ids = HashMap::new();
        for (k, n) in net.nodes.iter().enumerate() {
            for a in std::iter::once(&n.addr).chain(&n.extra) {
                ids.insert(key(*a), k as u64 + 1);
            }
        }
        Self {
            net,
            ids,
            next_id: 100,
            out: String::new(),
            st: Summary::default(),
            streams: HashMap::new(),
            kept_now: false,
        }
    }

    /// The id of the address with number `k`; an unknown one is a failure unless `fresh` (the target of a reject).
    fn id(&mut self, k: u64, fresh: bool) -> u64 {
        if let Some(i) = self.ids.get(&k) {
            return *i;
        }
        assert!(fresh, "a datagram to an address the test does not know: {k:#x}");
        let i = self.next_id;
        self.next_id += 1;
        self.ids.insert(k, i);
        i
    }

    fn step(&mut self, ev: TraceEvent) -> Option<Step> {
        let mut s = Step::default();
        match ev {
            TraceEvent::TxConn {
                slot,
                room,
                len,
                seg,
                dest,
            } => {
                s.k = "conn";
                s.slot = slot as i64;
                s.room = room;
                s.has = len != NONE;
                if s.has {
                    s.len = len;
                    s.seg = seg;
                    s.d = if dest == NONE - 1 { 0 } else { self.id(dest, false) };
                }
            }
            TraceEvent::TxGone { slot } => {
                s.k = "gone";
                s.slot = slot as i64;
            }
            TraceEvent::TxGate {
                dest,
                len,
                segments,
                n,
                allowed,
            } => {
                s.k = "gate";
                s.d = self.id(dest, false);
                s.len = len;
                s.segs = segments;
                s.n = n;
                s.ok = allowed == 1;
            }
            TraceEvent::TxDrop { slot } => {
                s.k = "drop";
                s.slot = if slot == NONE { -1 } else { slot as i64 };
            }
            TraceEvent::TxMark { slot, queue } => {
                s.k = "mark";
                s.slot = slot as i64;
                s.q = queue;
            }
            TraceEvent::TxReject { dest, len, seg } => {
                s.k = "reject";
                s.d = self.id(dest, true);
                s.len = len;
                s.seg = seg;
            }
            _ => return None,
        }
        Some(s)
    }

    fn stash_json(&mut self, s: Option<(SocketAddr, usize, usize)>, fresh: bool) -> String {
        s.map_or_else(
            || "[]".to_string(),
            |(a, len, seg)| {
                let d = self.id(key(a), fresh);
                format!(r#"[{{"d":{d},"len":{len},"seg":{seg}}}]"#)
            },
        )
    }

    /// One recorded `poll_transmit` call of node 0 with a buffer of `out_len` bytes.
    fn rec(&mut self, out_len: usize) -> Option<Transmit> {
        drain(&mut self.net);
        let ep = &self.net.nodes[0].ep;
        let gos: Vec<bool> = (0..CK).map(|i| ep.trace_gossip(i).unwrap()).collect();
        let q0: Vec<usize> = ep.trace_dirty(0).collect();
        let q1: Vec<usize> = ep.trace_dirty(1).collect();
        let stash = ep.trace_stash();
        let dropped = ep.trace_dropped();
        let mut buf = vec![0u8; out_len];
        let now = self.net.now;
        let r = self.net.nodes[0].ep.poll_transmit(now, &mut buf);
        let events = drain(&mut self.net);
        let ep = &self.net.nodes[0].ep;
        let q0a: Vec<usize> = ep.trace_dirty(0).collect();
        let q1a: Vec<usize> = ep.trace_dirty(1).collect();
        let stasha = ep.trace_stash();
        assert_eq!(
            ep.trace_dropped(),
            dropped,
            "the trace ring dropped records during a call"
        );
        let steps: Vec<Step> = events.into_iter().filter_map(|e| self.step(e)).collect();
        let has_reject = steps.iter().any(|s| s.k == "reject");

        // the result
        if let Some(t) = &r {
            assert!(t.segment_size >= 1, "a result with a segment size of 0");
            assert!(t.len <= out_len, "a result of {} bytes in a buffer of {out_len}", t.len);
            assert!(
                t.len.div_ceil(t.segment_size) <= LIM,
                "more than {LIM} datagrams in one result"
            );
        }
        // each session waits at most once, and on one queue
        for (a, b) in [(&q0, &q1), (&q0a, &q1a)] {
            let all: Vec<usize> = a.iter().chain(b).copied().collect();
            let set: HashSet<usize> = all.iter().copied().collect();
            assert_eq!(set.len(), all.len(), "a session waits twice: {a:?} {b:?}");
        }
        // a kept datagram comes from a call that returned a result and did not send the stash
        let from_stash = stash.is_some() && matches!(steps.as_slice(), [s] if s.k == "gate" && s.ok);
        if stasha.is_some() {
            assert!(
                r.is_some() && !from_stash,
                "a datagram was kept by a call without a fresh result"
            );
        }
        // every datagram taken from a connection is gated or dropped, or kept at the end of the call
        let convs: Vec<usize> = (0..steps.len())
            .filter(|&i| steps[i].k == "conn" && steps[i].has)
            .collect();
        for (n, &i) in convs.iter().enumerate() {
            let end = steps[i + 1..]
                .iter()
                .position(|s| s.k == "conn")
                .map_or(steps.len(), |p| i + 1 + p);
            let fin = steps[i + 1..end]
                .iter()
                .filter(|s| s.k == "gate" || s.k == "drop")
                .count();
            assert!(
                fin == 1 || (fin == 0 && n + 1 == convs.len() && end == steps.len() && stasha.is_some()),
                "a datagram taken from a connection was neither gated, dropped nor kept"
            );
        }
        // the datagrams the ledger let out are the datagrams of the result (a reject is charged when it is made)
        let gated: u64 = steps.iter().filter(|s| s.k == "gate" && s.ok).map(|s| s.segs).sum();
        let sent = r.map_or(0, |t| t.len.div_ceil(t.segment_size.max(1)) as u64);
        if !has_reject {
            assert_eq!(gated, sent, "the ledger and the result disagree");
        }

        self.st.calls += 1;
        self.st.results += u32::from(r.is_some());
        self.st.joins += steps.iter().filter(|s| s.k == "gate" && s.ok).count().saturating_sub(1) as u32;
        self.st.kept += u32::from(stasha.is_some());
        self.st.drops += steps.iter().filter(|s| s.k == "drop").count() as u32;
        self.st.stash_drops += steps.iter().filter(|s| s.k == "drop" && s.slot == -1).count() as u32;
        self.st.rejects += steps.iter().filter(|s| s.k == "reject").count() as u32;
        self.st.gone += steps.iter().filter(|s| s.k == "gone").count() as u32;
        self.st.broadcast_served += steps
            .iter()
            .filter(|s| s.k == "conn" && s.has && gos.get(s.slot as usize).copied().unwrap_or(false))
            .count() as u32;
        self.kept_now = stasha.is_some();

        let stash_s = self.stash_json(stash, false);
        let stasha_s = self.stash_json(stasha, false);
        let res = match &r {
            None => "[]".to_string(),
            Some(t) => {
                let d = self.id(key(t.remote), has_reject);
                format!(r#"[{{"d":{d},"len":{},"seg":{}}}]"#, t.len, t.segment_size)
            }
        };
        let _ = writeln!(
            self.out,
            r#"{{"t":"tx","out":{out_len},"lim":{LIM},"md":{MAX_DATAGRAM},"gos":{},"q0":{},"q1":{},"stash":{stash_s},"steps":{},"res":{res},"q0a":{},"q1a":{},"stasha":{stasha_s}}}"#,
            list(&gos),
            list(&q0),
            list(&q1),
            list(steps.iter().map(Step::json)),
            list(&q0a),
            list(&q1a),
        );
        if let Some(t) = r {
            let delay = self.net.delay;
            for chunk in buf[..t.len].chunks(t.segment_size) {
                self.net.inject(t.local, t.remote, chunk.to_vec(), delay);
            }
        }
        r
    }

    /// Recorded calls until one returns `None` with nothing waiting, at most 64.
    fn round(&mut self, out: impl Fn(usize) -> usize) {
        for k in 0..64 {
            let r = self.rec(out(k));
            if r.is_none() && !self.net.nodes[0].ep.transmit_waiting() {
                return;
            }
        }
    }

    /// Open a unidirectional stream on `s` and write `n` bytes (the last stream of the session when no new one opens).
    fn write(&mut self, s: SessionId, n: usize) {
        let now = self.net.now;
        let node = &mut self.net.nodes[0];
        if let Ok(rep) = node.cmd(
            now,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        ) && let Value::Stream(id) = rep.value
        {
            self.streams.insert(s, id);
        }
        let Some(&stream) = self.streams.get(&s) else {
            self.st.writes_failed += 1;
            return;
        };
        let data = vec![0x5a; n];
        if node
            .cmd(
                now,
                Command::Write {
                    session: s,
                    stream,
                    data: &data,
                },
            )
            .is_err()
        {
            self.st.writes_failed += 1;
        }
    }

    fn gossip(&mut self, s: SessionId, on: bool) {
        let now = self.net.now;
        self.net.nodes[0]
            .cmd(now, Command::SetGossip { session: s, gossip: on })
            .unwrap();
    }

    /// The sessions of node `a` that are established and whose route runs to `to`.
    fn sessions_to(&mut self, a: usize, to: SocketAddr) -> Vec<SessionId> {
        let mut seen: Vec<SessionId> = Vec::new();
        for (_, e) in &self.net.nodes[a].events {
            if let Event::Connected { session, .. } | Event::Incoming { session, .. } = e
                && !seen.contains(session)
            {
                seen.push(*session);
            }
        }
        seen.into_iter()
            .filter(|s| {
                matches!(self.net.nodes[a].ep.query(Query::Stats(*s)),
                    Answer::Stats(st) if st.established && st.route.map(|(_, r)| r) == Some(to))
            })
            .collect()
    }
}

#[test]
fn trace_tx() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        for tag in 1..=4 {
            net.add(tag);
        }
        let (addr1, node1) = (net.nodes[1].addr, net.nodes[1].node);
        let node0 = net.nodes[0].node;
        // the crossing dials: both sides dial at once, which may leave two sessions between the same pair
        let now = net.now;
        let addr0 = net.nodes[0].addr;
        net.nodes[0].connect(now, node1, ALPN_A, addr1, Role::Other).unwrap();
        net.nodes[1].connect(now, node0, ALPN_A, addr0, Role::Other).unwrap();
        let end = net.now + 10 * SEC_NS;
        net.run(end, |_| false);
        let mut t = Tracer::new(net);
        let mut to1 = t.sessions_to(0, addr1);
        if to1.is_empty() {
            let (sa, _) = t.net.connect_pair(0, 1, ALPN_A, Role::Other);
            to1.push(sa);
        }
        let (s1, s1x) = (to1[0], to1.get(1).copied());
        let merged = u32::from(s1x.is_none());
        let (s2, _) = t.net.connect_pair(0, 2, ALPN_A, Role::Other);
        let (s3, _) = t.net.connect_pair(0, 3, ALPN_A, Role::Other);
        let (s4, _) = t.net.connect_pair(0, 1, ALPN_B, Role::Other);
        t.net.run_for(2 * SEC_NS);
        let four: Vec<SessionId> = [Some(s1), s1x, Some(s2), Some(s3)].into_iter().flatten().collect();

        // 1: equal writes
        for &s in &four {
            t.write(s, 4000);
        }
        t.round(|_| 65536);
        t.net.run_for(50 * MS_NS);
        // 2: the same, buffers cycling
        for &s in &four {
            t.write(s, 4000);
        }
        t.round(|k| [65536, 9216, 3000, 1500, 1200][k % 5]);
        t.net.run_for(50 * MS_NS);
        // 3: mixed sizes in a seeded order
        let mut rng = SplitMix64::traced(0x7478_0000_0000_0001);
        for n in [1, 700, 1300, 2600, 9000] {
            let s = four[(rng.next_u64() % four.len() as u64) as usize];
            t.write(s, n);
        }
        t.round(|_| 65536);
        t.net.run_for(50 * MS_NS);
        // 4: broadcast
        t.gossip(s2, true);
        t.gossip(s3, true);
        for s in [s1, s2, s3] {
            t.write(s, 3000);
        }
        t.round(|_| 65536);
        t.net.run_for(50 * MS_NS);
        // 5: a broadcast session with an open still to leave, alone in its queue (the pattern of the second test)
        let (peer2, addr2) = (t.net.nodes[2].node, t.net.nodes[2].addr);
        let now = t.net.now;
        t.net.nodes[0].connect(now, peer2, ALPN_B, addr2, Role::Other).unwrap();
        t.write(s2, 8000);
        t.rec(1500);
        t.write(s1, 3000);
        t.write(s3, 3000);
        t.round(|_| 1500);
        t.net.run_for(50 * MS_NS);
        // 6: a slot freed while it may still be queued
        t.write(s3, 3000);
        t.rec(1500);
        let now = t.net.now;
        t.net.nodes[0]
            .cmd(now, Command::Close { session: s3, error: 0 })
            .unwrap();
        t.net.run_for(3 * SEC_NS);
        t.write(s1, 3000);
        t.round(|_| 65536);
        t.net.run_for(50 * MS_NS);
        // 7: a datagram kept for the next call, then dropped by a buffer too short for it
        t.write(s1, 3000);
        t.write(s2, 3000);
        for _ in 0..16 {
            t.rec(65536);
            if t.kept_now {
                break;
            }
        }
        if t.kept_now {
            t.rec(100);
        }
        t.round(|_| 65536);
        t.net.run_for(50 * MS_NS);
        // 8: rejects. The datagrams reach the endpoint directly: a network pump would send the rejects unrecorded.
        drain(&mut t.net);
        let to = t.net.nodes[0].addr;
        for i in 1..=3u64 {
            let from = SocketAddr::from(([10, 9, 9, i as u8], 4433));
            let mut d = first_datagram(i + 1, &forged_hello(i), 0);
            let now = t.net.now;
            t.net.nodes[0].ep.handle_datagram(now, to, from, &mut d);
        }
        let before = t.st.rejects;
        t.round(|_| 65536);
        assert!(t.st.rejects > before, "no recorded call returned a reject");
        t.net.run_for(50 * MS_NS);
        // 9: random
        let mut rng = SplitMix64::traced(0x7478_0000_0000_0002);
        let live: Vec<SessionId> = [Some(s1), s1x, Some(s2), Some(s4)].into_iter().flatten().collect();
        for c in 0..200usize {
            if rng.next_u64().is_multiple_of(3) {
                let s = live[(rng.next_u64() % live.len() as u64) as usize];
                let n = [1, 100, 1200, 1300, 2600, 4000, 9000][(rng.next_u64() % 7) as usize];
                t.write(s, n);
            }
            if rng.next_u64().is_multiple_of(20) {
                let s = live[(rng.next_u64() % live.len() as u64) as usize];
                let on = !t.net.nodes[0].ep.trace_gossip(s.slot()).unwrap();
                t.gossip(s, on);
            }
            let out = [65536, 65536, 65536, 9216, 3000, 1500, 1200, 64][(rng.next_u64() % 8) as usize];
            t.rec(out);
            if c % 10 == 9 {
                t.net.run_for(20 * MS_NS);
            }
        }
        let st = &t.st;
        eprintln!(
            "trace_tx: calls {} results {} joins {} kept {} drops {} (of the kept {}) rejects {} gone {} broadcast served {} \
             writes failed {} merged crossing dials {merged}",
            st.calls,
            st.results,
            st.joins,
            st.kept,
            st.drops,
            st.stash_drops,
            st.rejects,
            st.gone,
            st.broadcast_served,
            st.writes_failed
        );
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("tx.ndjson"), &t.out).unwrap();
        }
    });
}

/// Open a stream on session `s` of node `n` and write `len` bytes to it at the network's time.
fn write(net: &mut CoreNet, n: usize, s: SessionId, len: usize) {
    let now = net.now;
    let Value::Stream(id) = net.nodes[n]
        .cmd(
            now,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!("no stream")
    };
    net.nodes[n]
        .cmd(
            now,
            Command::Write {
                session: s,
                stream: id,
                data: &vec![0x5a; len],
            },
        )
        .unwrap();
}

/// The sessions waiting in queue `k` of node `n`, first to last.
fn queue(net: &CoreNet, n: usize, k: usize) -> Vec<usize> {
    net.nodes[n].ep.trace_dirty(k).collect()
}

fn set_gossip(net: &mut CoreNet, n: usize, session: SessionId, gossip: bool) {
    let now = net.now;
    net.nodes[n].cmd(now, Command::SetGossip { session, gossip }).unwrap();
}

/// The remote of the next datagram node `n` sends.
fn next_remote(net: &mut CoreNet, n: usize) -> Option<SocketAddr> {
    let mut buf = vec![0u8; 1500];
    let now = net.now;
    net.nodes[n].ep.poll_transmit(now, &mut buf).map(|t| t.remote)
}

/// A node with all its queues empty after its sessions settled.
fn quiet(net: &mut CoreNet, a: usize) {
    net.run_for(2 * SEC_NS);
    assert_eq!(queue(net, a, 0), Vec::<usize>::new(), "queue 0 is not empty");
    assert_eq!(queue(net, a, 1), Vec::<usize>::new(), "queue 1 is not empty");
}

/// A broadcast session counts as ordinary while a sub-session open waits to leave it, and as broadcast once the open
/// has left (the module documentation of `tx.rs`): the open puts it in queue 0 ahead of the sub-session it opens, and
/// once the open has left the ordinary session is served first.
#[test]
fn a_broadcast_session_moves_behind_after_its_open() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let (s1, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (s2, _) = net.connect_pair(a, c, ALPN_A, Role::Other);
        quiet(&mut net, a);
        let now = net.now;
        let (peer1, addr1) = (net.nodes[b].node, net.nodes[b].addr);
        let addr2 = net.nodes[c].addr;
        set_gossip(&mut net, a, s1, true);
        let rep = net.nodes[a].connect(now, peer1, ALPN_B, addr1, Role::Other).unwrap();
        let child = net.nodes[a].session(&rep);
        assert_eq!(
            queue(&net, a, 0),
            [s1.slot(), child.slot()],
            "the open waits in queue 0 ahead of the sub-session it opens"
        );
        write(&mut net, a, s1, 8000);
        assert!(next_remote(&mut net, a).is_some(), "the first call served no one");
        assert!(
            !queue(&net, a, 0).contains(&s1.slot()) && queue(&net, a, 1).contains(&s1.slot()),
            "once its open has left the session waits behind the ordinary ones"
        );
        write(&mut net, a, s2, 3000);
        let served: Vec<_> = (0..3).map(|_| next_remote(&mut net, a)).collect();
        assert!(
            served.contains(&Some(addr2)),
            "the ordinary session is served before the broadcast one: {served:?}"
        );
    });
}

/// A session made broadcast while it waits alone in queue 0 is moved behind at its turn: it cannot keep the first
/// place until it runs dry.
#[test]
fn a_lone_session_made_broadcast_moves_behind_at_its_turn() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let (s1, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (s2, _) = net.connect_pair(a, c, ALPN_A, Role::Other);
        quiet(&mut net, a);
        let (addr1, addr2) = (net.nodes[b].addr, net.nodes[c].addr);
        set_gossip(&mut net, a, s2, true);
        write(&mut net, a, s2, 3000);
        write(&mut net, a, s1, 8000);
        assert_eq!(queue(&net, a, 0), [s1.slot()]);
        assert_eq!(queue(&net, a, 1), [s2.slot()]);
        set_gossip(&mut net, a, s1, true);
        assert_eq!(
            queue(&net, a, 0),
            [s1.slot()],
            "a session made broadcast keeps its place until its turn"
        );
        assert_eq!(next_remote(&mut net, a), Some(addr1));
        assert!(
            !queue(&net, a, 0).contains(&s1.slot()),
            "a broadcast session served alone waits behind once served"
        );
        assert!(queue(&net, a, 1).contains(&s1.slot()));
        assert_eq!(
            next_remote(&mut net, a),
            Some(addr2),
            "the other broadcast session gets its turn"
        );
    });
}

/// A broadcast session waiting behind others moves to the ordinary queue when its open is queued, so the open
/// leaves before the broadcast session that waited ahead of it.
#[test]
fn a_broadcast_session_waiting_behind_others_is_promoted_when_its_open_is_queued() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b, c, d) = (net.add(1), net.add(2), net.add(3), net.add(4));
        let (sb, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (sa, _) = net.connect_pair(a, d, ALPN_A, Role::Other);
        let (so, _) = net.connect_pair(a, c, ALPN_A, Role::Other);
        quiet(&mut net, a);
        let now = net.now;
        let (node_b, addr_b, addr_c) = (net.nodes[b].node, net.nodes[b].addr, net.nodes[c].addr);
        set_gossip(&mut net, a, sa, true);
        set_gossip(&mut net, a, sb, true);
        write(&mut net, a, sa, 3000);
        write(&mut net, a, sb, 3000);
        write(&mut net, a, so, 8000);
        assert_eq!(queue(&net, a, 0), [so.slot()]);
        assert_eq!(queue(&net, a, 1), [sa.slot(), sb.slot()]);
        let rep = net.nodes[a].connect(now, node_b, ALPN_B, addr_b, Role::Other).unwrap();
        let child = net.nodes[a].session(&rep);
        assert_eq!(
            queue(&net, a, 0),
            [so.slot(), sb.slot(), child.slot()],
            "the open moves its session to the ordinary queue, ahead of the sub-session it opens"
        );
        assert_eq!(queue(&net, a, 1), [sa.slot()]);
        assert_eq!(next_remote(&mut net, a), Some(addr_c));
        assert_eq!(
            next_remote(&mut net, a),
            Some(addr_b),
            "the open leaves before the broadcast session that waited ahead of it"
        );
        assert_eq!(
            queue(&net, a, 1),
            [sa.slot(), sb.slot()],
            "once its open has left the session waits behind again"
        );
    });
}

/// A waiting broadcast session that stops being one moves to the back of the ordinary queue at once.
#[test]
fn a_waiting_broadcast_session_made_ordinary_moves_to_the_ordinary_queue() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS_NS);
        let (a, b, c) = (net.add(1), net.add(2), net.add(3));
        let (s1, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let (s2, _) = net.connect_pair(a, c, ALPN_A, Role::Other);
        quiet(&mut net, a);
        let (addr1, addr2) = (net.nodes[b].addr, net.nodes[c].addr);
        set_gossip(&mut net, a, s1, true);
        write(&mut net, a, s1, 3000);
        write(&mut net, a, s2, 3000);
        assert_eq!(queue(&net, a, 0), [s2.slot()]);
        assert_eq!(queue(&net, a, 1), [s1.slot()]);
        set_gossip(&mut net, a, s1, false);
        assert_eq!(
            queue(&net, a, 0),
            [s2.slot(), s1.slot()],
            "a session made ordinary joins the ordinary queue at once"
        );
        assert_eq!(queue(&net, a, 1), Vec::<usize>::new());
        assert_eq!(next_remote(&mut net, a), Some(addr2));
        assert_eq!(
            next_remote(&mut net, a),
            Some(addr1),
            "the ordinary sessions take turns"
        );
    });
}
