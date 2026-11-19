//! Trace generation for the node's own record and address discovery: seeded random runs of the real `Connectivity`
//! through its public API, recorded as ndjson (`connect_own.ndjson`) for the TLA+ trace check (`TraceConnectOwn.tla`) and
//! the Lean replay (`Pinc/TraceConnectOwn.lean`).
//!
//! A run is one node with ten relay slots (some with a UDP address, some without, some sharing an address), local
//! discovery off (no beacon shares the signing slot), driven by `set_local` (up to eleven addresses, with repeats),
//! `set_hints` (also too long), `probe_all` and the probes `tick` sends itself, QADR datagrams (valid for the probe
//! sent to the relay; from an address no relay has; from the address of another relay's probe; with a fresh nonce; with
//! the nonce of an earlier probe; the same answer twice; malformed bytes), `link_changed`, `tick` with no wall clock, the
//! same wall clock, a higher one and a lower one (a clock set back), `restore_record_seq` below and above the last
//! number, and the host's answers to the signature requests (a good length and a wrong one; the signature itself is a
//! stub of zeros, the record is parsed, not verified). After every call the candidate list the node offers is read back
//! (`candidates`) and recorded; a restore records the last number the node reports after it (`record_seq`); a call that
//! starts a record job records the fields of the record about to be signed (the sequence number, the home, the class,
//! the addresses and the hints, read from the bytes of the signature request), the home and the class the node reports
//! at that moment being inputs of the model (`ConnectClient`'s rules decide them).
//!
//! The test also runs a plain reference of the rules (probe per relay, answer taken for the first relay with that
//! address and the nonce of its probe, the candidates as one fold over the reflexive addresses in relay order and then
//! the local ones, each listed once, the number as the wall clock or one above the last number) and requires the same
//! candidates after every call, the same taking of every answer as far as it shows in them (the test picks the reported
//! addresses so it mostly does), a job exactly when the reference says one starts, and the same number for every record,
//! each above the one before. A scripted run shows #287 fixed: records signed in one tick, after a tick with no wall
//! clock and after the clock was set back are each one above the one before. Addresses are small numbers (the address
//! `k` is `10.0.0.k:k`; a relay's UDP address `100 + k`), nonces are numbered from 1 in the order they are sent.
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity,
    clippy::cast_possible_wrap,
    clippy::needless_range_loop,
    unreachable_pub
)]

mod connect_common;

use std::collections::HashMap;
use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use connect_common::{SEC, big_stack, nid};
use pinc_connect::client::{Config, Connectivity, RelayCfg};
use pinc_connect::record::{MAX_ADDRS, MAX_HINT_LEN, Record};
use pinc_connect::relay::datagram::Datagram;
use pinc_crypto::Software;
use pinc_security::{Env, KeyRequest, KeyResponse};
use pinc_tests::{Host, SplitMix64};

const NR: usize = 10;
type Conn = Connectivity<Software, NR, 4>;

fn sa(k: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, k as u8)), k)
}

fn lst<T: ToString>(v: &[T]) -> String {
    format!("[{}]", v.iter().map(ToString::to_string).collect::<Vec<_>>().join(","))
}

fn pick<T: Copy>(rng: &mut SplitMix64, v: &[T]) -> T {
    v[(rng.next_u64() % v.len() as u64) as usize]
}

/// The reference: what the rules say, kept as plain lists.
#[derive(Clone, Default)]
struct Reference {
    udp: Vec<u16>,
    probe: Vec<Option<[u8; 8]>>,
    refl: Vec<Option<u16>>,
    local: Vec<u16>,
    wall: Option<u64>,
    last_seq: u64,
    hints: Vec<u8>,
    want: bool,
    job: bool,
}

impl Reference {
    /// The reflexive addresses in relay order, then the local ones, each once, at most `MAX_ADDRS`.
    fn cands(&self) -> Vec<u16> {
        let mut c: Vec<u16> = Vec::new();
        for a in self.refl.iter().flatten().chain(&self.local) {
            if c.len() < MAX_ADDRS && !c.contains(a) {
                c.push(*a);
            }
        }
        c
    }

    /// The number of the next record: the wall clock, or one above the last number when the clock is not past it.
    fn next_seq(&self, wall: u64) -> u64 {
        wall.max(self.last_seq.saturating_add(1))
    }

    /// The relay that takes an answer from `from` with `nonce`, if any.
    fn takes(&self, from: u16, nonce: [u8; 8]) -> Option<usize> {
        let k = self.udp.iter().position(|u| *u == from && from != 0)?;
        (self.probe[k] == Some(nonce)).then_some(k)
    }
}

struct Run {
    conn: Box<Conn>,
    drbg: pinc_crypto::Drbg,
    r: Reference,
    out: Vec<String>,
    now: u64,
    ids: HashMap<[u8; 8], u32>,
    relay_ids: Vec<pinc_crypto::NodeId>,
    sig_len: usize,
    stats: Stats,
    seqs: Vec<u64>,
    last_wall: Option<u64>,
}

#[derive(Default)]
struct Stats {
    taken: u32,
    refused: u32,
    jobs: u32,
    wall_seq: u32,
    next_seq: u32,
    set_back: u32,
    restore_up: u32,
    restore_kept: u32,
    full: u32,
    dedup: u32,
    shared_refl: u32,
    blocked: u32,
    toolong: u32,
    badsig: u32,
}

impl Run {
    fn id(&mut self, nonce: [u8; 8]) -> u32 {
        let n = self.ids.len() as u32 + 1;
        *self.ids.entry(nonce).or_insert(n)
    }

    fn real_cands(&self) -> Vec<u16> {
        let mut out = [sa(0); MAX_ADDRS];
        let n = self.conn.candidates(&mut out);
        out[..n].iter().map(SocketAddr::port).collect()
    }

    /// The candidates the node offers, checked against the reference; for the event.
    fn cands(&mut self) -> String {
        let real = self.real_cands();
        assert_eq!(real, self.r.cands(), "candidates differ from the reference");
        if real.len() == MAX_ADDRS {
            self.stats.full += 1;
        }
        let refl: Vec<u16> = self.r.refl.iter().flatten().copied().collect();
        if refl.iter().enumerate().any(|(i, a)| refl[..i].contains(a)) {
            self.stats.shared_refl += 1;
        }
        if self.r.local.iter().any(|a| refl.contains(a)) {
            self.stats.dedup += 1;
        }
        lst(&real)
    }

    fn push(&mut self, s: String) {
        self.out.push(s);
    }

    /// Drain what the layer queued: the probes (recorded, nonce per relay slot) and anything else (dropped).
    fn drain(&mut self) {
        let mut buf = vec![0u8; 2048];
        let mut probes: Vec<(SocketAddr, [u8; 8])> = Vec::new();
        while let Some((to, n)) = self.conn.poll_udp(&mut buf) {
            if let Ok(Datagram::Qad { nonce }) = Datagram::decode(&buf[..n]) {
                probes.push((to, nonce));
            }
        }
        while self.conn.poll_io().is_some() {}
        while self.conn.poll_notice().is_some() {}
        if probes.is_empty() {
            return;
        }
        let mut ns = vec![0u32; NR];
        let mut it = probes.into_iter();
        for k in 0..NR {
            if self.r.udp[k] != 0 {
                let (to, nonce) = it.next().expect("a probe per relay with a UDP address");
                assert_eq!(to.port(), self.r.udp[k], "probe to the relay's address, in relay order");
                ns[k] = self.id(nonce);
                self.r.probe[k] = Some(nonce);
            }
        }
        assert!(it.next().is_none());
        let c = self.cands();
        self.push(format!(r#"{{"t":"oprobe","n":{},"c":{c}}}"#, lst(&ns)));
    }

    fn local(&mut self, addrs: &[u16]) {
        let sas: Vec<SocketAddr> = addrs.iter().map(|k| sa(*k)).collect();
        self.conn.set_local(&sas);
        self.r.local = addrs.iter().copied().take(MAX_ADDRS).collect();
        let c = self.cands();
        self.push(format!(r#"{{"t":"olocal","a":{},"c":{c}}}"#, lst(addrs)));
    }

    fn probe_all(&mut self) {
        let now = self.now;
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.probe_all(now, &mut env);
        self.drain();
    }

    fn restart(&mut self) {
        self.conn.link_changed(self.now);
        self.r.probe = vec![None; NR];
        self.r.refl = vec![None; NR];
        let c = self.cands();
        self.push(format!(r#"{{"t":"orestart","c":{c}}}"#));
        self.drain_quiet();
    }

    /// Queued traffic that is not a probe (a restart queues none; kept for the carrier's dial requests).
    fn drain_quiet(&mut self) {
        let mut buf = vec![0u8; 2048];
        while self.conn.poll_udp(&mut buf).is_some() {}
        while self.conn.poll_io().is_some() {}
        while self.conn.poll_notice().is_some() {}
    }

    /// A QADR datagram `from` an address, with the nonce bytes and the reported address.
    fn answer(&mut self, from: u16, nonce: [u8; 8], a: u16) {
        let mut buf = [0u8; 128];
        let n = Datagram::Qadr { nonce, addr: sa(a) }.encode(&mut buf).unwrap();
        let took = self.r.takes(from, nonce);
        let id = self.id(nonce);
        let from_sa = if from == 999 {
            "9.9.9.9:999".parse().unwrap()
        } else {
            sa_udp(from)
        };
        let now = self.now;
        let handled = self.conn.handle_udp(now, from_sa, &buf[..n]);
        assert_eq!(
            handled,
            self.r.udp.contains(&from) && from != 0,
            "a relay datagram is the layer's"
        );
        if let Some(k) = took {
            self.r.probe[k] = None;
            self.r.refl[k] = Some(a);
            self.stats.taken += 1;
        } else {
            self.stats.refused += 1;
        }
        let c = self.cands();
        self.push(format!(
            r#"{{"t":"oans","from":{from},"n":{id},"a":{a},"took":{},"c":{c}}}"#,
            u8::from(took.is_some())
        ));
        self.drain_quiet();
    }

    fn malformed(&mut self, from: u16) {
        let junk = [0x01u8, 1, 2, 3];
        let from_sa = if from == 999 {
            "9.9.9.9:999".parse().unwrap()
        } else {
            sa_udp(from)
        };
        let now = self.now;
        let _ = self.conn.handle_udp(now, from_sa, &junk);
        let c = self.cands();
        self.push(format!(r#"{{"t":"onoop","c":{c}}}"#));
        self.drain_quiet();
    }

    /// The host gives back a saved number: it only raises the last one.
    fn restore(&mut self, n: u64) {
        self.conn.restore_record_seq(n);
        if n > self.r.last_seq {
            self.r.last_seq = n;
            self.stats.restore_up += 1;
        } else {
            self.stats.restore_kept += 1;
        }
        assert_eq!(
            self.conn.record_seq(),
            self.r.last_seq,
            "a restored number only raises the last one"
        );
        let c = self.cands();
        self.push(format!(r#"{{"t":"oseq","n":{n},"last":{},"c":{c}}}"#, self.r.last_seq));
    }

    fn hints(&mut self, h: &[u8]) {
        let ok = self.conn.set_hints(h);
        assert_eq!(ok, h.len() <= MAX_HINT_LEN);
        if ok {
            self.r.hints = h.to_vec();
            self.r.want = true;
        } else {
            self.stats.toolong += 1;
        }
        let c = self.cands();
        self.push(format!(
            r#"{{"t":"ohint","h":{},"ok":{},"c":{c}}}"#,
            lst(&if ok { h.to_vec() } else { vec![] }),
            u8::from(ok)
        ));
    }

    /// The fields of the record job the layer waits to have signed, if any.
    fn job_fields(&mut self) -> Option<(u64, usize, u8, Vec<u16>, Vec<u8>)> {
        let Some(KeyRequest::Sign { message, .. }) = self.conn.sign_request() else {
            return None;
        };
        let mut bytes = message.to_vec();
        bytes.extend(vec![0u8; self.sig_len]);
        let rec = Record::parse(&bytes).expect("a record job is a record");
        let home = self
            .relay_ids
            .iter()
            .position(|i| *i == rec.home)
            .expect("the home is a relay");
        let addrs: Vec<u16> = rec.addrs().map(|a| a.port()).collect();
        Some((rec.seq, home, rec.reach as u8, addrs, rec.hints.to_vec()))
    }

    /// After a call that may start jobs (`pre`: a record job was outstanding before it): the tail of its event, with the
    /// job it started, if any.
    fn job_tail(&mut self, pre: bool) -> String {
        let hm = self.conn.home().map_or(0, |h| h + 1);
        let cl = self.conn.class().map_or(0, |c| c as u8);
        let real = self.job_fields();
        let mut tail = format!(r#""hm":{hm},"cl":{cl},"#);
        if pre {
            assert!(real.is_some(), "the job outstanding went away");
            assert!(self.r.job);
            tail += r#""j":0,"seq":0,"home":0,"reach":0,"a":[],"h":[]"#;
            return tail;
        }
        let consumed = self.r.want && self.r.wall.is_some();
        let expect = consumed && hm != 0 && cl != 0;
        assert_eq!(
            real.is_some(),
            expect,
            "a record job starts exactly when the reference says"
        );
        if consumed {
            self.r.want = false;
        }
        let Some((seq, home, reach, addrs, hints)) = real else {
            if consumed {
                self.stats.blocked += 1;
            }
            tail += r#""j":0,"seq":0,"home":0,"reach":0,"a":[],"h":[]"#;
            return tail;
        };
        let wall = self.r.wall.expect("a job needs a wall clock");
        assert_eq!(
            seq,
            self.r.next_seq(wall),
            "the sequence number is the wall clock, or one above the last number"
        );
        assert!(seq > self.r.last_seq, "a record's number is above the last one");
        if let Some(prev) = self.seqs.last() {
            assert!(seq > *prev, "a record's number is above the record before it");
        }
        assert_eq!(home + 1, hm);
        assert_eq!(reach, cl);
        assert_eq!(addrs, self.r.cands());
        assert_eq!(hints, self.r.hints);
        self.r.job = true;
        self.stats.jobs += 1;
        if seq == wall {
            self.stats.wall_seq += 1;
        } else {
            self.stats.next_seq += 1;
        }
        if self.last_wall.is_some_and(|w| wall < w) {
            self.stats.set_back += 1;
        }
        self.r.last_seq = seq;
        self.seqs.push(seq);
        self.last_wall = Some(wall);
        write!(
            tail,
            r#""j":1,"seq":{seq},"home":{hm},"reach":{reach},"a":{},"h":{}"#,
            lst(&addrs),
            lst(&hints)
        )
        .unwrap();
        tail
    }

    fn tick(&mut self, dt: u64, wall: Option<u64>) {
        self.now += dt;
        if wall.is_some() {
            self.r.wall = wall;
        }
        let pre = self.r.job;
        let now = self.now;
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.tick(now, &mut env, wall);
        self.drain();
        let c = self.cands();
        let tail = self.job_tail(pre);
        self.push(format!(r#"{{"t":"otick","w":{},"c":{c},{tail}}}"#, wall.unwrap_or(0)));
    }

    /// The host answers the outstanding signature request (a stub of zeros; too short when `good` is false).
    fn sign(&mut self, good: bool) {
        assert!(self.r.job);
        self.now += 1_000_000;
        let len = if good { self.sig_len } else { self.sig_len - 1 };
        if !good {
            self.stats.badsig += 1;
        }
        let sig = vec![0u8; len];
        self.r.job = false;
        let now = self.now;
        self.conn.sign_response(now, KeyResponse::Signature(&sig));
        self.drain();
        let c = self.cands();
        let tail = self.job_tail(false);
        self.push(format!(r#"{{"t":"osign","ok":{},"c":{c},{tail}}}"#, u8::from(good)));
    }
}

fn sa_udp(k: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(20, 0, 0, k as u8)), k)
}

fn new_run(host: &Host, udp: &[u16], seed: u64, out: Vec<String>, stats: Stats) -> Run {
    let mut relays = [None; NR];
    let mut relay_ids = Vec::new();
    for k in 0..NR {
        relay_ids.push(nid(0x10 + k as u8));
        if k < udp.len() {
            relays[k] = Some(RelayCfg {
                id: relay_ids[k],
                udp: (udp[k] != 0).then(|| sa_udp(udp[k])),
                tcp: Some(SocketAddr::new(IpAddr::V4(Ipv4Addr::new(30, 0, 0, k as u8)), 443)),
                ws: None,
            });
        }
    }
    let cfg = Config {
        me: host.identity.node_id(),
        identity: host.identity,
        relays,
        phone: false,
        restarted: false,
        start: 1000 * SEC,
        v6: false,
        keep_learn: false,
    };
    let mut conn = Box::new(Connectivity::new(cfg, host.prekey_info.clone(), Software, seed));
    conn.set_local_discovery(false);
    let mut u = udp.to_vec();
    u.resize(NR, 0);
    let mut run = Run {
        conn,
        drbg: pinc_crypto::Drbg::new(&[seed as u8 ^ 0x62; 32]),
        r: Reference {
            udp: u.clone(),
            probe: vec![None; NR],
            refl: vec![None; NR],
            ..Reference::default()
        },
        out,
        now: 1000 * SEC,
        ids: HashMap::new(),
        relay_ids,
        sig_len: host.identity.alg().signature_len(),
        stats,
        seqs: Vec::new(),
        last_wall: None,
    };
    let c = run.cands();
    run.push(format!(r#"{{"t":"onew","udp":{},"cap":{MAX_ADDRS},"c":{c}}}"#, lst(&u)));
    run
}

/// A scripted run of #287 fixed: records signed in one tick, after a tick without a wall clock and after a clock set
/// back are each one above the one before; a clock past the last number gives its own.
fn scripted(host: &Host, out: Vec<String>, stats: Stats) -> (Vec<String>, Stats) {
    let mut run = new_run(host, &[101, 102], 1, out, stats);
    run.local(&[5, 6]);
    run.probe_all();
    let n1 = run.r.probe[0].unwrap();
    let n2 = run.r.probe[1].unwrap();
    run.answer(101, n1, 1);
    run.answer(102, n2, 2);
    run.tick(SEC, None);
    run.tick(SEC, Some(7000));
    run.hints(&[1]);
    run.tick(0, Some(7000));
    assert!(run.r.job);
    // a second set_hints while the first record is being signed: the next job starts with the answer, in the same tick
    run.hints(&[2]);
    run.sign(true);
    assert!(run.r.job);
    run.sign(true);
    // and after a tick that had no wall clock
    run.hints(&[3]);
    run.tick(SEC, None);
    run.sign(true);
    // a clock set back
    run.hints(&[4]);
    run.tick(SEC, Some(6900));
    run.sign(true);
    run.hints(&[5]);
    run.tick(SEC, Some(7100));
    run.sign(true);
    assert_eq!(run.seqs, [7000, 7001, 7002, 7003, 7100]);
    (run.out, run.stats)
}

fn episode(host: &Host, seed: u64, out: Vec<String>, stats: Stats) -> (Vec<String>, Stats) {
    let mut rng = SplitMix64::new(seed);
    let n_rel = 1 + (rng.next_u64() % NR as u64) as usize;
    let mut udp: Vec<u16> = Vec::new();
    for k in 0..n_rel {
        let r = rng.next_u64() % 10;
        udp.push(if r < 2 {
            0
        } else if r < 4 && k > 0 {
            udp[k - 1]
        } else {
            101 + k as u16
        });
    }
    let mut run = new_run(host, &udp, seed, out, stats);
    let pool: Vec<u16> = (1..=14).collect();
    let mut seen_nonces: Vec<[u8; 8]> = Vec::new();
    for _ in 0..70 {
        match rng.next_u64() % 23 {
            0 | 1 => {
                let n = (rng.next_u64() % 12) as usize;
                let a: Vec<u16> = (0..n).map(|_| pick(&mut rng, &pool)).collect();
                run.local(&a);
            }
            2 | 3 => run.probe_all(),
            4..=9 => {
                for _ in 0..=(rng.next_u64() % 2) {
                    let k = (rng.next_u64() % NR as u64) as usize;
                    let a = pick(&mut rng, &pool);
                    let fresh = {
                        let mut b = [0u8; 8];
                        b.copy_from_slice(&rng.next_u64().to_be_bytes());
                        b
                    };
                    let (from, nonce) = match rng.next_u64() % 6 {
                        0..=2 => match run.r.probe[k] {
                            Some(n) if run.r.udp[k] != 0 => (run.r.udp[k], n),
                            _ => (run.r.udp[k], fresh),
                        },
                        3 => (run.r.udp[k], fresh),
                        4 => match run.r.probe[k] {
                            Some(n) => (999, n),
                            None => (999, fresh),
                        },
                        _ => (run.r.udp[k], seen_nonces.last().copied().unwrap_or(fresh)),
                    };
                    if let Some(n) = run.r.probe[k] {
                        seen_nonces.push(n);
                    }
                    run.answer(from, nonce, a);
                }
            }
            10 => {
                let k = (rng.next_u64() % NR as u64) as usize;
                let from = if rng.next_u64().is_multiple_of(2) {
                    run.r.udp[k]
                } else {
                    999
                };
                run.malformed(from);
            }
            11 => run.restart(),
            12..=17 => {
                let dt = pick(&mut rng, &[0, 1_000_000, SEC, 2 * SEC, 70 * SEC]);
                let last = run.r.wall.unwrap_or(5_000_000);
                let wall = match rng.next_u64() % 8 {
                    0 | 1 => None,
                    2 | 3 => Some(last),
                    4 | 5 => Some(last + 1 + rng.next_u64() % 1000),
                    6 => Some(last.saturating_sub(1 + rng.next_u64() % 500).max(1)),
                    _ => Some(5_000_000 + rng.next_u64() % 100),
                };
                run.tick(dt, wall);
            }
            22 => {
                let last = run.r.last_seq;
                let n = match rng.next_u64() % 3 {
                    0 => last.saturating_sub(1 + rng.next_u64() % 10),
                    1 => last,
                    _ => last + 1 + rng.next_u64() % 1000,
                };
                run.restore(n);
            }
            18 | 19 => {
                let len = match rng.next_u64() % 8 {
                    0 => MAX_HINT_LEN + 1,
                    1 => MAX_HINT_LEN,
                    n => (n % 4) as usize,
                };
                let h: Vec<u8> = (0..len).map(|_| (rng.next_u64() % 200) as u8).collect();
                run.hints(&h);
            }
            _ => {
                if run.r.job {
                    let good = !rng.next_u64().is_multiple_of(5);
                    run.sign(good);
                }
            }
        }
    }
    (run.out, run.stats)
}

#[test]
fn the_own_record_and_address_discovery_trace() {
    big_stack(|| {
        let host = Box::new(Host::new(0x41, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (mut out, mut stats) = scripted(&host, Vec::new(), Stats::default());
        for seed in 0..120u64 {
            (out, stats) = episode(&host, 0x0A00 + seed, out, stats);
        }
        assert!(stats.taken > 50, "answers taken: {}", stats.taken);
        assert!(stats.refused > 50, "answers refused: {}", stats.refused);
        assert!(stats.jobs > 50, "record jobs: {}", stats.jobs);
        assert!(stats.wall_seq > 3, "numbers from the clock: {}", stats.wall_seq);
        assert!(stats.next_seq > 5, "numbers one above the last: {}", stats.next_seq);
        assert!(stats.set_back > 3, "records after a clock set back: {}", stats.set_back);
        assert!(
            stats.restore_up > 3,
            "restores that raised the number: {}",
            stats.restore_up
        );
        assert!(stats.restore_kept > 3, "restores that kept it: {}", stats.restore_kept);
        assert!(stats.full > 3, "full candidate lists: {}", stats.full);
        assert!(stats.dedup > 3, "own addresses already listed: {}", stats.dedup);
        assert!(
            stats.shared_refl > 3,
            "an address that several relays report: {}",
            stats.shared_refl
        );
        assert!(stats.toolong > 0, "hints too long");
        assert!(stats.badsig > 0, "signature of the wrong length");
        assert!(stats.blocked > 0, "a wanted record dropped for want of a home or class");
        let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
            return;
        };
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        let mut text = String::new();
        for l in &out {
            writeln!(text, "{l}").unwrap();
        }
        std::fs::write(dir.join("connect_own.ndjson"), text).unwrap();
    });
}
