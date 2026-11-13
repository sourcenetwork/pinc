//! Trace generation for the relay's record store: seeded random runs of the real `Relay` through its public API,
//! recorded as ndjson (`connect_records.ndjson`) for the TLA+ trace check (`TraceConnectRecords.tla`) and the Lean replay
//! (`Vinc/TraceConnectRecords.lean`).
//!
//! A run is one relay with three record slots, five carrier sessions open (four Ed25519 nodes and one ML-DSA-65 node,
//! whose records are too large for a UDP answer) and the relay's own key, driven by every way a record arrives (PUB on a
//! carrier of the node itself and of another node, SYNC from a peer relay, `restore_record`, `set_own_record`), by
//! `handle_timeout`, by DNSQ datagrams (the lookup answer), by `sync_record`, and by `add_peer` and `remove_peer`.
//! The records are really signed: good ones, one with a flipped signature byte, one whose key belongs to another node
//! id, and bytes that are no record. A record is recorded as the fields the store sees (node, sequence number, home, a
//! tag standing for every other byte, the length, and whether it verifies: the check is an oracle of the model, the
//! test says which bytes verify by how it built them). Times are whole seconds and step by amounts around the
//! lifetime (5400 s), the republish period (1800 s) and the sweep period (1 s).
//!
//! The test also runs a plain reference of the rules (a map of bytes and receive times) and requires the same answer to
//! every call, the same stored bytes for every node after every call, the same bytes in every lookup answer and the same
//! number of replication frames. What is recorded is what an observer sees: the call, its answer, every effect the
//! relay emitted in order (frames to peer relays and the `Trace` transitions of the record rules; the carrier PINGs of
//! `handle_timeout` are not about records and are left out), and after every call the store of the relay (for each
//! stored node: sequence number, home, tag, length and receive time, read back from the stored bytes) and its counters.
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
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
    unreachable_pub
)]

mod connect_common;

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;

use connect_common::{addr, dg, keypair, nid};
use vinc_connect::carrier::Frame;
use vinc_connect::carrier::frame::DnsAnswer;
use vinc_connect::record::{self, MAX_RECORD_LEN, Reach, Record, RecordFields};
use vinc_connect::relay::datagram::Datagram;
use vinc_connect::relay::{Config, Effect, Quota, RecordOrigin, Reject, Relay, SessionId, Sink, Trace, UdpTarget};
use vinc_crypto::identity::MAX_PUBLIC_KEY_LEN;
use vinc_crypto::{IdentityAlg, Keypair, NodeId};
use vinc_tests::SplitMix64;

const SEC: u64 = 1_000_000_000;
const TTL: u64 = 5400;
const REPUB: u64 = 1800;
const CAP: usize = 3;
type R = Relay<8, CAP, 1, 300>;

/// Names: 1 to 4 are Ed25519 key holders, 5 the ML-DSA-65 holder, 6 the relay itself, 7 to 9 peer relays, 10 another home.
struct Names(Vec<NodeId>);

impl Names {
    fn n(&self, id: &NodeId) -> usize {
        self.0.iter().position(|x| x == id).map_or(99, |p| p + 1)
    }
    fn id(&self, n: usize) -> NodeId {
        self.0[n - 1]
    }
}

fn reject_name(r: Reject) -> &'static str {
    match r {
        Reject::StoreFull => "storefull",
        Reject::BadRecord(_) => "badrecord",
        Reject::StaleRecord => "stalerec",
        Reject::WrongOwner => "wrongowner",
        other => panic!("unexpected refusal {other:?}"),
    }
}

fn res_name(r: &Result<(), Reject>) -> String {
    r.as_ref()
        .map_or_else(|e| reject_name(*e).to_string(), |()| "ok".into())
}

/// Collects the record-related effects as JSON arrays and the datagram answer.
struct Col<'a> {
    names: &'a Names,
    out: Vec<String>,
    reply: Option<(u8, Vec<u8>)>,
}

impl Sink for Col<'_> {
    fn emit(&mut self, e: Effect<'_>) {
        let n = |x: &NodeId| self.names.n(x);
        match e {
            Effect::PeerRelay {
                to,
                frame: Frame::Sync { record },
            } => self.out.push(format!(r#"["peer",{},"sync",{}]"#, n(&to), record.len())),
            Effect::Carrier { frame: Frame::Ping, .. } => {}
            Effect::Udp {
                to: UdpTarget::Reply(_),
                datagram: Datagram::DnsReply { answer, .. },
            } => {
                self.reply = Some(match answer {
                    DnsAnswer::Absent => (0, vec![]),
                    DnsAnswer::TooLarge => (2, vec![]),
                    DnsAnswer::Record(b) => (1, b.to_vec()),
                });
            }
            Effect::Trace(t) => match t {
                Trace::RecordStored { node, seq, origin } => self.out.push(format!(
                    r#"["t","rstored",{},{seq},"{}"]"#,
                    n(&node),
                    match origin {
                        RecordOrigin::Publish => "publish",
                        RecordOrigin::Replica => "replica",
                        RecordOrigin::Own => "own",
                    }
                )),
                Trace::Rejected { reason, node } => self.out.push(format!(
                    r#"["t","rej","{}",{}]"#,
                    reject_name(reason),
                    node.map_or(0, |x| n(&x))
                )),
                Trace::LookupServed { peer, found } => {
                    self.out
                        .push(format!(r#"["t","lookup",{},{}]"#, n(&peer), u8::from(found)));
                }
                Trace::Republished { peers } => self.out.push(format!(r#"["t","repub",{peers}]"#)),
                other => panic!("unexpected trace {other:?}"),
            },
            other => panic!("unexpected effect {other:?}"),
        }
    }
}

struct Null;
impl Sink for Null {
    fn emit(&mut self, _e: Effect<'_>) {}
}

/// One record as the store sees it.
#[derive(Clone)]
struct Spec {
    node: usize,
    seq: u64,
    home: usize,
    tag: u8,
    kind: u8,
    bytes: Vec<u8>,
}

impl Spec {
    fn ok(&self) -> bool {
        self.kind == 0
    }
    fn json(&self) -> String {
        format!(
            r#""rn":{},"rs":{},"rh":{},"rt":{},"rl":{},"rok":{}"#,
            self.node,
            self.seq,
            self.home,
            u32::from(self.tag) + 50 * u32::from(self.kind),
            self.bytes.len(),
            u8::from(self.ok())
        )
    }
}

fn hints(tag: u8) -> Vec<u8> {
    vec![tag; 1 + usize::from(tag % 3)]
}

struct Maker {
    kps: Vec<Keypair>,
    names: Names,
    cache: HashMap<(usize, u64, usize, u8, u8), Vec<u8>>,
}

impl Maker {
    /// kind 0: verifies; 1: a flipped signature byte; 2: the key of another node under this node id; 3: no record.
    fn make(&mut self, rng: &mut SplitMix64, node: usize, seq: u64, home: usize, tag: u8, kind: u8) -> Spec {
        if kind == 3 {
            let mut b = vec![0u8; (rng.next_u64() % 60) as usize];
            rng.fill(&mut b);
            return Spec {
                node: 0,
                seq: 0,
                home: 0,
                tag: 0,
                kind: 3,
                bytes: b,
            };
        }
        let key = (node, seq, home, tag, kind);
        if let Some(b) = self.cache.get(&key) {
            return Spec {
                node,
                seq,
                home,
                tag,
                kind,
                bytes: b.clone(),
            };
        }
        let h = hints(tag);
        let fields = RecordFields {
            home: self.names.id(home),
            seq,
            reach: Reach::Public,
            addrs: &[],
            hints: &h,
        };
        let kp = &self.kps[node - 1];
        let mut buf = vec![0u8; MAX_RECORD_LEN];
        let mut len = if kind == 2 {
            let other = &self.kps[if node <= 4 { node % 4 } else { 0 }];
            let mut pk = [0u8; MAX_PUBLIC_KEY_LEN];
            let n = other.public_key(&mut pk).unwrap();
            let signed = record::prepare(&self.names.id(node), &pk[..n], &fields, &mut buf).unwrap();
            let (msg, sig_out) = buf.split_at_mut(signed);
            let sl = other.sign(msg, sig_out).unwrap();
            signed + sl
        } else {
            record::sign(kp, &fields, &mut buf).unwrap()
        };
        if kind == 1 {
            buf[len - 1] ^= 1;
        }
        buf.truncate(len);
        len = buf.len();
        assert_eq!(buf.len(), len);
        self.cache.insert(key, buf.clone());
        Spec {
            node,
            seq,
            home,
            tag,
            kind,
            bytes: buf,
        }
    }
}

/// The plain reference of the rules, in whole seconds.
struct Reference {
    me: usize,
    store: BTreeMap<usize, (Vec<u8>, u64, u64)>,
    peers: Vec<usize>,
    np: u64,
    ls: u64,
    rejected: u64,
    lookups: u64,
    records: u64,
}

impl Reference {
    /// The answer of a store call for a record of `owner` (0 none) received at `at`; the number of replication frames.
    fn store(&mut self, at: u64, s: &Spec, owner: usize) -> &'static str {
        if !s.ok() {
            self.rejected += 1;
            return "badrecord";
        }
        if owner != 0 && owner != s.node {
            self.rejected += 1;
            return "wrongowner";
        }
        if let Some((b, seq, rcv)) = self.store.get_mut(&s.node) {
            if s.seq < *seq || (s.seq == *seq && *b != s.bytes) {
                self.rejected += 1;
                return "stalerec";
            }
            if s.seq == *seq {
                *rcv = at;
                return "ok";
            }
        } else if self.store.len() >= CAP {
            self.rejected += 1;
            return "storefull";
        }
        self.store.insert(s.node, (s.bytes.clone(), s.seq, at));
        self.records += 1;
        "ok"
    }
    fn fresh(&self, now: u64, node: usize) -> bool {
        self.store
            .get(&node)
            .is_some_and(|(_, _, rcv)| now.saturating_sub(*rcv) < TTL)
    }
    fn timeout(&mut self, now: u64) -> usize {
        let mut frames = 0;
        if self.np != 0 && now >= self.np {
            self.np = now + REPUB;
            if let Some(e) = self.store.get_mut(&self.me) {
                e.2 = now;
                frames = self.peers.len();
            }
        }
        if now.saturating_sub(self.ls) >= 1 {
            self.ls = now;
            self.store.retain(|_, (_, _, rcv)| now.saturating_sub(*rcv) < TTL);
        }
        frames
    }
}

fn st_json(r: &R, names: &Names) -> String {
    let mut nodes: Vec<usize> = r.record_nodes().map(|n| names.n(&n)).collect();
    nodes.sort_unstable();
    assert_eq!(nodes.len(), r.record_count());
    let mut s = String::from("[");
    for (i, k) in nodes.iter().enumerate() {
        let id = names.id(*k);
        let rcv = r.record_received(&id).unwrap();
        // a lookup at the receive time is always fresh, so it reads the stored bytes back
        let bytes = r.lookup(rcv, &id).unwrap();
        let rec = Record::parse(bytes).unwrap();
        if i > 0 {
            s.push(',');
        }
        write!(
            s,
            "[{k},{},{},{},{},{}]",
            rec.seq,
            names.n(&rec.home),
            rec.hints.first().copied().unwrap_or(0),
            bytes.len(),
            rcv / SEC
        )
        .unwrap();
    }
    s.push(']');
    s
}

fn cn_json(r: &R) -> String {
    let s = r.stats();
    format!("[{},{},{}]", s.records, s.lookups, s.rejected)
}

fn run(seed: u64, out: &mut Vec<String>, cov: &mut Cov) {
    let mut rng = SplitMix64::new(seed.wrapping_mul(0x1234_5678_9abc_def1) ^ 0xabcd);
    let mut kps: Vec<Keypair> = (1..=4).map(|t| keypair(IdentityAlg::Ed25519, t)).collect();
    kps.push(keypair(IdentityAlg::MlDsa65, 5));
    kps.push(keypair(IdentityAlg::Ed25519, 6));
    let mut ids: Vec<NodeId> = kps.iter().map(Keypair::node_id).collect();
    ids.extend([nid(0xa7), nid(0xa8), nid(0xa9), nid(0xb0)]);
    let names = Names(ids.clone());
    let me = ids[5];
    let mut cfg = Config::new(me, seed);
    cfg.quota = Quota {
        bytes: u64::MAX / 4,
        window_ns: 60 * SEC,
        session_ns: u64::MAX / 4,
    };
    let mut relay: Box<R> = Box::new(R::new(cfg));
    let mut mk = Maker {
        kps,
        names: Names(ids.clone()),
        cache: HashMap::new(),
    };
    let mut rf = Reference {
        me: 6,
        store: BTreeMap::new(),
        peers: vec![],
        np: 0,
        ls: 0,
        rejected: 0,
        lookups: 0,
        records: 0,
    };
    out.push(format!(
        r#"{{"t":"qnew","me":6,"r":{CAP},"p":{}}}"#,
        vinc_connect::relay::rule::MAX_PEERS
    ));
    let mut now_s = 1000u64;
    let mut sess: Vec<SessionId> = Vec::new();
    for k in 1..=5 {
        sess.push(relay.carrier_opened(now_s * SEC, ids[k - 1], &mut Null).unwrap());
    }
    // peers 7 and 8 up front; later calls add and remove
    for p in [7usize, 8] {
        assert!(relay.add_peer(ids[p - 1]));
        rf.peers.push(p);
        out.push(format!(r#"{{"t":"qadd","p":{p},"res":"ok"}}"#));
    }
    let mut seqs = [0u64; 7];
    let pick = |rng: &mut SplitMix64, v: &[u64]| v[(rng.next_u64() % v.len() as u64) as usize];
    for _ in 0..140 {
        let dt = pick(
            &mut rng,
            &[
                0, 0, 1, 1, 2, 5, 100, 1799, 1800, 1801, 3599, 3600, 5398, 5399, 5400, 5401, 7200,
            ],
        );
        now_s += dt;
        let now = now_s * SEC;
        let node = 1 + (rng.next_u64() % 5) as usize;
        let tag = 1 + (rng.next_u64() % 2) as u8;
        let home = pick(&mut rng, &[6, 7, 10]) as usize;
        let kind = pick(&mut rng, &[0, 0, 0, 0, 0, 0, 0, 1, 2, 3]) as u8;
        let kind = if kind == 2 && node == 5 { 1 } else { kind };
        // sequence numbers: mostly a little above the last, sometimes equal or lower
        let seq = match rng.next_u64() % 6 {
            0 => seqs[node].saturating_sub(1).max(1),
            1 | 2 => seqs[node].max(1),
            _ => seqs[node] + 1 + rng.next_u64() % 2,
        };
        let op = rng.next_u64() % 100;
        let mut col = Col {
            names: &names,
            out: vec![],
            reply: None,
        };
        let head;
        let res: String;
        let mut frames_expected: Option<usize> = None;
        match op {
            // PUB on the carrier of a node: its own record, or sometimes another node's
            0..=27 => {
                let owner = if rng.next_u64().is_multiple_of(8) {
                    1 + (rng.next_u64() % 5) as usize
                } else {
                    node
                };
                let s = mk.make(&mut rng, node, seq, home, tag, kind);
                let got = relay.carrier_frame(
                    now,
                    &ids[owner - 1],
                    sess[owner - 1],
                    &Frame::Publish { record: &s.bytes },
                    &mut col,
                );
                res = res_name(&got);
                let want = rf.store(now_s, &s, owner);
                assert_eq!(res, want, "publish");
                if res == "ok" {
                    seqs[node] = seqs[node].max(seq);
                    frames_expected = Some(rf.peers.len());
                }
                head = format!(r#"{{"t":"qpub","now":{now_s},"n":{owner},{}"#, s.json());
            }
            // SYNC from a peer relay
            28..=45 if !rf.peers.is_empty() => {
                let from = rf.peers[(rng.next_u64() % rf.peers.len() as u64) as usize];
                let s = mk.make(&mut rng, node, seq, home, tag, kind);
                let got = relay.peer_frame(now, &ids[from - 1], &Frame::Sync { record: &s.bytes }, &mut col);
                res = res_name(&got);
                let want = rf.store(now_s, &s, 0);
                assert_eq!(res, want, "replica");
                if res == "ok" {
                    seqs[node] = seqs[node].max(seq);
                    frames_expected = Some(0);
                }
                head = format!(r#"{{"t":"qrep","now":{now_s},{}"#, s.json());
            }
            // restore_record, received a while ago
            46..=53 => {
                let back = pick(&mut rng, &[0, 1, 100, 5399, 5400, 5401]);
                let at_s = now_s.saturating_sub(back);
                let s = mk.make(&mut rng, node, seq, home, tag, kind);
                let got = relay.restore_record(at_s * SEC, &s.bytes, &mut col);
                res = res_name(&got);
                let want = rf.store(at_s, &s, 0);
                assert_eq!(res, want, "restore");
                if res == "ok" {
                    seqs[node] = seqs[node].max(seq);
                    frames_expected = Some(0);
                }
                head = format!(r#"{{"t":"qrst","at":{at_s},{}"#, s.json());
            }
            // set_own_record: the relay's own, sometimes someone else's
            54..=60 => {
                let who = if rng.next_u64().is_multiple_of(5) { node } else { 6 };
                let s = mk.make(&mut rng, who, seq, home, tag, kind);
                let got = relay.set_own_record(now, &s.bytes, &mut col);
                res = res_name(&got);
                let want = rf.store(now_s, &s, 6);
                assert_eq!(res, want, "own");
                if res == "ok" {
                    seqs[who] = seqs[who].max(seq);
                    frames_expected = Some(rf.peers.len());
                    rf.np = now_s + REPUB;
                }
                head = format!(r#"{{"t":"qown","now":{now_s},{}"#, s.json());
            }
            // the timer
            61..=76 => {
                relay.handle_timeout(now, &mut col);
                let frames = rf.timeout(now_s);
                let peers_out = col.out.iter().filter(|e| e.starts_with(r#"["peer"#)).count();
                assert_eq!(peers_out, frames, "republish frames");
                res = "ok".into();
                head = format!(r#"{{"t":"qtime","now":{now_s}"#);
            }
            // a lookup over UDP
            77..=91 => {
                let k = 1 + (rng.next_u64() % 6) as usize;
                let q = dg(&Datagram::DnsQuery { peer: ids[k - 1] });
                relay.datagram(now, addr(), None, &q, &mut col).unwrap();
                rf.lookups += 1;
                let (kind_a, bytes) = col.reply.take().unwrap();
                let want_fresh = rf.fresh(now_s, k);
                let stored = rf.store.get(&k);
                let (a, extra) = match kind_a {
                    0 => {
                        assert!(!want_fresh, "absent answer for a fresh record");
                        ("absent", String::new())
                    }
                    1 => {
                        assert!(want_fresh, "an expired record was answered");
                        assert_eq!(&bytes, &stored.unwrap().0, "the answered bytes");
                        let rec = Record::parse(&bytes).unwrap();
                        cov.hit += 1;
                        (
                            "record",
                            format!(r#","as":{},"at":{},"al":{}"#, rec.seq, rec.hints[0], bytes.len()),
                        )
                    }
                    _ => {
                        assert!(want_fresh && stored.unwrap().0.len() > 1389, "too large");
                        cov.toolarge += 1;
                        ("toolarge", String::new())
                    }
                };
                if kind_a == 1 {
                    assert!(stored.unwrap().0.len() <= 1389);
                }
                res = a.into();
                head = format!(r#"{{"t":"qlook","now":{now_s},"peer":{k},"ans":"{a}"{extra}"#);
            }
            // sync_record
            92..=96 => {
                let to = 7 + (rng.next_u64() % 3) as usize;
                let k = 1 + (rng.next_u64() % 6) as usize;
                let ok = relay.sync_record(&ids[to - 1], &ids[k - 1], &mut col);
                let want = rf.peers.contains(&to)
                    && rf
                        .store
                        .get(&k)
                        .is_some_and(|(b, _, _)| Record::parse(b).is_ok_and(|r| names.n(&r.home) == 6));
                assert_eq!(ok, want, "sync_record");
                res = if ok { "ok" } else { "no" }.into();
                cov.sync += u32::from(ok);
                head = format!(r#"{{"t":"qsync","to":{to},"node":{k}"#);
            }
            // add or remove a peer
            _ => {
                let p = 7 + (rng.next_u64() % 3) as usize;
                if rng.next_u64().is_multiple_of(2) {
                    relay.remove_peer(&ids[p - 1]);
                    rf.peers.retain(|x| *x != p);
                    out.push(format!(r#"{{"t":"qrem","p":{p}}}"#));
                } else {
                    assert!(relay.add_peer(ids[p - 1]));
                    if !rf.peers.contains(&p) {
                        rf.peers.push(p);
                    }
                    out.push(format!(r#"{{"t":"qadd","p":{p},"res":"ok"}}"#));
                }
                continue;
            }
        }
        if let Some(n) = frames_expected {
            let got = col.out.iter().filter(|e| e.starts_with(r#"["peer"#)).count();
            assert_eq!(got, n, "replication frames");
        }
        for e in &col.out {
            cov.stale += u32::from(e.contains(r#""stalerec""#));
            cov.full += u32::from(e.contains("storefull"));
            cov.bad += u32::from(e.contains("badrecord"));
            cov.wrong += u32::from(e.contains("wrongowner"));
            cov.stored += u32::from(e.contains("rstored"));
            cov.repub += u32::from(e.contains("repub"));
            cov.frames += u32::from(e.starts_with(r#"["peer"#));
        }
        assert_eq!(relay.stats().rejected, rf.rejected);
        assert_eq!(relay.stats().records, rf.records);
        assert_eq!(relay.stats().lookups, rf.lookups);
        // the stored bytes are the reference's, for every node
        let mut mine: Vec<usize> = relay.record_nodes().map(|n| names.n(&n)).collect();
        mine.sort_unstable();
        let theirs: Vec<usize> = rf.store.keys().copied().collect();
        assert_eq!(mine, theirs, "the stored nodes");
        for (k, (b, _, rcv)) in &rf.store {
            let id = names.id(*k);
            let r = relay.record_received(&id).unwrap();
            assert_eq!(r / SEC, *rcv, "receive time of {k}");
            assert_eq!(relay.lookup(r, &id).unwrap(), b.as_slice(), "bytes of {k}");
        }
        out.push(format!(
            r#"{head},"res":"{res}","out":[{}],"st":{},"cn":{}}}"#,
            col.out.join(","),
            st_json(&relay, &names),
            cn_json(&relay)
        ));
    }
}

#[derive(Default)]
struct Cov {
    stale: u32,
    full: u32,
    bad: u32,
    wrong: u32,
    stored: u32,
    repub: u32,
    frames: u32,
    hit: u32,
    toolarge: u32,
    sync: u32,
}

#[test]
fn the_relay_records_its_record_trace() {
    let mut out = Vec::new();
    let mut cov = Cov::default();
    for seed in 0..60u64 {
        run(seed, &mut out, &mut cov);
    }
    assert!(cov.stale > 0, "no stale record");
    assert!(cov.full > 0, "store never full");
    assert!(cov.bad > 0, "no bad record");
    assert!(cov.wrong > 0, "no wrong owner");
    assert!(cov.stored > 0, "nothing stored");
    assert!(cov.repub > 0, "no republish");
    assert!(cov.frames > 0, "no replication frame");
    assert!(cov.hit > 0, "no lookup hit");
    assert!(cov.toolarge > 0, "no too-large answer");
    assert!(cov.sync > 0, "no sync_record");
    let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut text = String::new();
    for l in &out {
        writeln!(text, "{l}").unwrap();
    }
    std::fs::write(dir.join("connect_records.ndjson"), text).unwrap();
}
