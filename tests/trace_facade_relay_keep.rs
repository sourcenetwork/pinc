//! Trace generation for what a node that carries the relay role keeps across a restart (`relay/state/keep.rs`): a
//! `KeepProbe` (a relay core with no carriers, behind the `trace` feature of `pinc`) beside a `MemStore`, recorded as
//! ndjson (`relay-keep.ndjson`) for the TLA+ trace check `TraceFacadeRelayKeep.tla`.
//!
//! A boundary run walks the cases one by one (a refresh, a stale record, the mailbox cap, the lifetime, a torn write,
//! a clock that goes back, a full table, a churn, a failed write, a rerun, a hand over); then seeded runs draw publishes,
//! holds, ticks, jobs, writes, restarts and reruns. Times are whole units of a quarter of a record lifetime, so the
//! record lifetime is 4 and the mailbox age 3. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub,
    missing_docs
)]

use std::collections::HashSet;
use std::fmt::Write as _;

use pinc::relay::{KeepJob, KeepProbe, MemStore, Store};
use pinc_connect::record::{self, Reach, RecordFields};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};
use pinc_tests::SplitMix64;
use smol::block_on;

/// One time unit in nanoseconds: a quarter of a record lifetime.
const U: u64 = 1_350_000_000_000;
/// Records of the table.
const NODES: usize = 1030;
/// The tries of a write before it is given up (`MAX_TRIES` of `relay/state/keep.rs`).
const MAX_TRIES: u64 = 8;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tear {
    None,
    Lost,
    Whole,
    NoParse,
    NoVerify,
    Prefix,
}

impl Tear {
    fn name(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Lost => "lost",
            Self::Whole => "whole",
            Self::NoParse => "noparse",
            Self::NoVerify => "noverify",
            Self::Prefix => "prefix",
        }
    }
}

fn key(id: &NodeId) -> (u8, [u8; 32]) {
    (id.alg.tag(), id.bytes)
}

/// The probe, its store, the job out, and the record of the run.
struct Run {
    probe: KeepProbe,
    store: MemStore,
    t: u64,
    job: Option<KeepJob>,
    out: String,
    /// The signing keys and node ids of the record nodes, in store key order: node n is index n - 1.
    nodes: Vec<(NodeId, Keypair)>,
    members: [NodeId; 3],
    src: NodeId,
    next_id: u32,
    held_ever: HashSet<(usize, u32)>,
}

fn nodes() -> Vec<(NodeId, Keypair)> {
    let mut v: Vec<(NodeId, Keypair)> = (0..NODES)
        .map(|k| {
            let mut seed = [(k as u8) ^ 0x11; 32];
            seed[..4].copy_from_slice(&(k as u32).to_be_bytes());
            let kp = Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap();
            (kp.node_id(), kp)
        })
        .collect();
    v.sort_by_key(|(id, _)| key(id));
    v
}

fn members() -> [NodeId; 3] {
    let mut m: Vec<NodeId> = (0..3u8)
        .map(|j| {
            Keypair::from_seed(IdentityAlg::Ed25519, &[0xA0 + j; 32])
                .unwrap()
                .node_id()
        })
        .collect();
    m.sort_by_key(key);
    [m[0], m[1], m[2]]
}

/// The packets of a Mail blob as the test decodes them: (id, arrival time in ns), with no byte left over.
fn decode(mut blob: &[u8]) -> Vec<(u32, u64)> {
    let mut out = Vec::new();
    while !blob.is_empty() {
        assert!(blob.len() >= 44, "a packet header is cut");
        let flag_at = 33;
        let at = u64::from_be_bytes(blob[flag_at + 1..flag_at + 9].try_into().unwrap());
        let len = usize::from(u16::from_be_bytes(blob[flag_at + 9..flag_at + 11].try_into().unwrap()));
        let body = &blob[44..];
        assert!(body.len() >= len, "a packet body is cut");
        out.push((u32::from_be_bytes(body[..4].try_into().unwrap()), at));
        blob = &body[len..];
    }
    out
}

fn list(ids: &[u32]) -> String {
    format!("[{}]", ids.iter().map(u32::to_string).collect::<Vec<_>>().join(","))
}

impl Run {
    /// A run on a new, empty store, restarted at t 0.
    fn new() -> Self {
        let nodes = nodes();
        let relay = KeepProbe::new(0).unwrap();
        let mut r = Self {
            probe: relay,
            store: MemStore::new(),
            t: 0,
            job: None,
            out: String::new(),
            nodes,
            members: members(),
            src: Keypair::from_seed(IdentityAlg::Ed25519, &[0x50; 32]).unwrap().node_id(),
            next_id: 1,
            held_ever: HashSet::new(),
        };
        r.restart(0, Tear::None);
        r
    }

    /// The number of the node the job out is about.
    fn job_node(&self) -> usize {
        match &self.job {
            Some(KeepJob::Put { node, .. } | KeepJob::Remove(node)) => self.node_number(node),
            Some(KeepJob::Mail { node, .. }) => self.member_number(node),
            None => 0,
        }
    }

    fn node_number(&self, id: &NodeId) -> usize {
        self.nodes.iter().position(|(n, _)| n == id).map_or(0, |i| i + 1)
    }

    fn member_number(&self, id: &NodeId) -> usize {
        self.members.iter().position(|m| m == id).map_or(0, |i| i + 1)
    }

    fn held_ids(&self, m: usize) -> Vec<u32> {
        let held = self.probe.held(&self.members[m - 1]);
        held.iter()
            .map(|(_, body)| {
                let id = u32::from_be_bytes(body[..4].try_into().unwrap());
                assert!(
                    self.held_ever.contains(&(m, id)),
                    "a packet the test never held for member {m}"
                );
                id
            })
            .collect()
    }

    fn mail_view(&self) -> String {
        let l: Vec<String> = (1..=3).map(|m| list(&self.held_ids(m))).collect();
        format!("[{}]", l.join(","))
    }

    fn recs_view(&self) -> String {
        let recs: Vec<String> = (1..=NODES)
            .filter_map(|n| {
                let (seq, rcv) = self.probe.record(&self.nodes[n - 1].0)?;
                Some(format!("{{\"n\":{n},\"seq\":{seq},\"rcv\":{}}}", rcv / U))
            })
            .collect();
        format!("[{}]", recs.join(","))
    }

    /// What the probe holds must not be past its lifetime (called right after a restore).
    fn check_alive(&self) {
        let now = self.t * U;
        for (id, _) in &self.nodes {
            if let Some((_, rcv)) = self.probe.record(id) {
                assert!(rcv + 4 * U > now, "a record past its lifetime was restored");
            }
        }
        for m in &self.members {
            for (at, _) in self.probe.held(m) {
                assert!(at + 3 * U > now, "a packet past its age was restored");
            }
        }
    }

    fn view_line(&mut self, op: &str, tear: Tear) {
        let _ = writeln!(
            self.out,
            "{{\"op\":\"{op}\",\"t\":{},\"tear\":\"{}\",\"recs\":{},\"mail\":{},\"errs\":{}}}",
            self.t,
            tear.name(),
            self.recs_view(),
            self.mail_view(),
            self.probe.store_errors()
        );
    }

    /// Apply a job to the store as a good write does.
    fn apply(&self, job: &KeepJob) {
        match job {
            KeepJob::Put { node, record, received } => block_on(self.store.put(node, record, *received)).unwrap(),
            KeepJob::Remove(n) => block_on(self.store.remove(n)).unwrap(),
            KeepJob::Mail { node, blob } => block_on(self.store.put_mailbox(node, blob)).unwrap(),
        }
    }

    /// The tear modes the job out allows.
    fn modes(&self) -> Vec<Tear> {
        match &self.job {
            None => vec![Tear::None],
            Some(KeepJob::Put { .. }) => vec![Tear::Lost, Tear::Whole, Tear::NoVerify, Tear::NoParse],
            Some(KeepJob::Remove(_)) => vec![Tear::Lost, Tear::Whole],
            Some(KeepJob::Mail { blob, .. }) if blob.is_empty() => vec![Tear::Lost, Tear::Whole],
            Some(KeepJob::Mail { .. }) => vec![Tear::Lost, Tear::Whole, Tear::Prefix],
        }
    }

    /// Cut the job out with `tear`, applied to the store first.
    fn cut(&mut self, tear: Tear) {
        let Some(job) = self.job.take() else {
            assert_eq!(tear, Tear::None, "a tear with no job out");
            return;
        };
        match (tear, &job) {
            (Tear::Lost | Tear::None, _) => {}
            (Tear::Whole, j) => self.apply(j),
            (Tear::NoVerify, KeepJob::Put { node, record, received }) => {
                let mut bad = record.clone();
                *bad.last_mut().unwrap() ^= 1;
                block_on(self.store.put(node, &bad, *received)).unwrap();
            }
            (Tear::NoParse, KeepJob::Put { node, record, received }) => {
                block_on(self.store.put(node, &record[..3], *received)).unwrap();
            }
            (Tear::Prefix, KeepJob::Mail { node, blob }) => {
                block_on(self.store.put_mailbox(node, &blob[..blob.len() - 1])).unwrap();
            }
            (t, _) => panic!("the tear {t:?} does not fit the job out"),
        }
    }

    fn replace_probe(&mut self, t: u64) {
        assert_eq!(self.probe.dropped(), 0, "the probe dropped packets");
        self.probe = KeepProbe::new(t * U).unwrap();
        assert_eq!(self.probe.record_count(), 0, "a new probe holds records");
    }

    /// A restart at `t` with the job out cut by `tear`: a new probe restored from the store.
    fn restart(&mut self, t: u64, tear: Tear) {
        self.cut_for(tear);
        self.t = t;
        self.replace_probe(t);
        let kept = block_on(self.store.load()).unwrap();
        self.probe.restore(t * U, &kept);
        self.check_alive();
        self.view_line("restart", tear);
    }

    /// The next run of the same run: a restart at 0 on the same store, the job out lost.
    fn again(mut self) -> Self {
        let tear = if self.job.is_some() { Tear::Lost } else { Tear::None };
        self.restart(0, tear);
        self
    }

    /// The run ends at `t` and the same core runs again: the write out is given back and the restore, run again,
    /// restores nothing.
    fn rerun(&mut self, t: u64, tear: Tear) {
        self.cut_for(tear);
        self.t = t;
        self.probe.end();
        let (recs, mail) = (self.recs_view(), self.mail_view());
        let kept = block_on(self.store.load()).unwrap();
        self.probe.restore(t * U, &kept);
        assert!(self.probe.restored(), "a restored core says it was not");
        assert!(
            recs == self.recs_view() && mail == self.mail_view(),
            "a rerun restored again"
        );
        self.view_line("rerun", tear);
    }

    /// The kind of the job out.
    fn kind(&self) -> &'static str {
        match &self.job {
            None => "none",
            Some(KeepJob::Put { .. }) => "put",
            Some(KeepJob::Remove(_)) => "remove",
            Some(KeepJob::Mail { .. }) => "mail",
        }
    }

    /// Take the next job and check its kind.
    fn expect(&mut self, kind: &str) {
        self.job();
        assert_eq!(self.kind(), kind, "the job is not the one the case intends");
    }

    fn cut_for(&mut self, tear: Tear) {
        if self.job.is_some() {
            assert!(
                self.modes().contains(&tear),
                "the tear {tear:?} does not fit the job out"
            );
        }
        self.cut(tear);
    }

    fn publish(&mut self, t: u64, n: usize, seq: u64) {
        self.t = t;
        let rec = self.record(n, seq);
        let ok = self.probe.publish(t * U, &rec);
        let node = self.nodes[n - 1].0;
        let cur = self.probe.record(&node);
        let (c, r) = cur.map_or((0, 0), |(s, rcv)| (s, rcv / U));
        let _ = writeln!(
            self.out,
            "{{\"op\":\"publish\",\"t\":{t},\"n\":{n},\"seq\":{seq},\"ok\":{ok},\"has\":{},\"cur\":{c},\"rcv\":{r}}}",
            cur.is_some()
        );
    }

    fn record(&self, n: usize, seq: u64) -> Vec<u8> {
        let (_, kp) = &self.nodes[n - 1];
        let mut out = vec![0u8; record::MAX_RECORD_LEN];
        let len = record::sign(
            kp,
            &RecordFields {
                home: self.probe.node_id(),
                seq,
                reach: Reach::UdpBlocked,
                addrs: &[],
                hints: &[],
            },
            &mut out,
        )
        .unwrap();
        out.truncate(len);
        out
    }

    fn hold(&mut self, t: u64, m: usize) {
        self.t = t;
        let id = self.next_id;
        self.next_id += 1;
        let mut body = vec![0xA5u8; 1389];
        body[..4].copy_from_slice(&id.to_be_bytes());
        self.held_ever.insert((m, id));
        let ok = self.probe.hold(t * U, &self.members[m - 1], &self.src, 0, &body);
        let held = list(&self.held_ids(m));
        let _ = writeln!(
            self.out,
            "{{\"op\":\"hold\",\"t\":{t},\"m\":{m},\"id\":{id},\"ok\":{ok},\"held\":{held}}}"
        );
    }

    fn heard(&mut self, t: u64, m: usize) {
        self.t = t;
        self.probe.heard(t * U, &self.members[m - 1]);
        let held = list(&self.held_ids(m));
        let _ = writeln!(self.out, "{{\"op\":\"heard\",\"t\":{t},\"m\":{m},\"held\":{held}}}");
    }

    fn tick(&mut self, t: u64) {
        self.t = t;
        self.probe.tick(t * U);
        let _ = writeln!(
            self.out,
            "{{\"op\":\"tick\",\"t\":{t},\"cnt\":{}}}",
            self.probe.record_count()
        );
    }

    /// Take the next job; nothing when one is out.
    fn job(&mut self) {
        assert!(self.job.is_none(), "a job is out");
        self.job = self.probe.next_job();
        let (k, n, seq, rcv, pk) = match &self.job {
            None => ("none", 0, 0, 0, String::new()),
            Some(KeepJob::Put { node, record, received }) => {
                let seq = pinc_connect::record::Record::parse(record).unwrap().seq;
                ("put", self.node_number(node), seq, received / U, String::new())
            }
            Some(KeepJob::Remove(node)) => ("remove", self.node_number(node), 0, 0, String::new()),
            Some(KeepJob::Mail { node, blob }) => {
                let m = self.member_number(node);
                let pk: Vec<String> = decode(blob)
                    .iter()
                    .map(|(id, at)| {
                        assert!(
                            self.held_ever.contains(&(m, *id)),
                            "a packet the test never held for member {m}"
                        );
                        format!("{{\"id\":{id},\"at\":{}}}", at / U)
                    })
                    .collect();
                ("mail", m, 0, 0, format!("[{}]", pk.join(",")))
            }
        };
        let pk = if pk.is_empty() { "[]".to_owned() } else { pk };
        let _ = writeln!(
            self.out,
            "{{\"op\":\"job\",\"k\":\"{k}\",\"n\":{n},\"seq\":{seq},\"rcv\":{rcv},\"pk\":{pk}}}"
        );
    }

    fn write(&mut self, ok: bool) {
        let job = self.job.take().expect("a write with no job out");
        if ok {
            self.apply(&job);
        }
        self.probe.written(ok);
        let _ = writeln!(self.out, "{{\"op\":\"write\",\"ok\":{ok}}}");
    }

    /// Jobs, each written, until none is left.
    fn drain(&mut self) {
        loop {
            self.job();
            if self.job.is_none() {
                return;
            }
            self.write(true);
        }
    }

    fn finish(&self) {
        assert_eq!(self.probe.dropped(), 0, "the probe dropped packets");
    }
}

/// Writes the store refuses: one given up after its tries, one tried again behind a mark not tried yet, with the
/// run ending while the retry is out.
fn failures(r: &mut Run) {
    r.hold(0, 3);
    let errs = r.probe.store_errors();
    r.expect("mail");
    for i in 1..=MAX_TRIES {
        r.write(false);
        r.tick(i);
        r.expect(if i < MAX_TRIES { "mail" } else { "none" });
    }
    assert_eq!(
        r.probe.store_errors() - errs,
        MAX_TRIES + 1,
        "a write given up is counted once per try and once more"
    );
    r.restart(0, Tear::None);
    r.publish(0, 5, 1);
    r.expect("put");
    let first = r.job_node();
    r.write(false);
    r.expect("none");
    r.publish(0, 6, 1);
    r.tick(1);
    r.expect("put");
    assert_ne!(r.job_node(), first, "the retry went before a mark not tried yet");
    r.write(true);
    r.expect("put");
    assert_eq!(r.job_node(), first, "the failed write is not tried again");
    r.rerun(1, Tear::Lost);
    r.expect("put");
    assert_eq!(
        r.job_node(),
        first,
        "the write out at the end of the run is not written again"
    );
    r.write(true);
    r.expect("none");
    r.restart(0, Tear::None);
}

/// The boundary run, one case after the other.
fn boundary(r: &mut Run) {
    failures(r);
    // a record, refreshed, stale
    r.publish(0, 1, 1);
    r.job();
    r.write(true);
    r.publish(1, 1, 1);
    r.job();
    r.publish(1, 1, 2);
    r.publish(1, 1, 1);
    r.job();
    r.write(true);
    // the mailbox cap
    for _ in 0..12 {
        r.hold(1, 1);
    }
    r.job();
    r.write(true);
    // the lifetime
    for t in 1..=6 {
        r.tick(t);
    }
    r.drain();
    // torn writes
    for tear in [Tear::NoVerify, Tear::NoParse] {
        r.publish(6, 2, 1);
        r.job();
        r.restart(6, tear);
        r.drain();
    }
    r.hold(6, 2);
    r.job();
    r.restart(6, Tear::Prefix);
    r.drain();
    for (tear, seq) in [(Tear::Lost, 2), (Tear::Whole, 3)] {
        r.publish(6, 2, seq);
        r.job();
        r.restart(6, tear);
        r.drain();
    }
    // the clock goes back and forward
    r.publish(8, 3, 1);
    r.hold(8, 3);
    r.drain();
    for t in [6, 0, 8, 20] {
        r.restart(t, Tear::None);
        r.drain();
    }
    // a full table
    for n in 4..=1027 {
        r.publish(21, n, 1);
    }
    r.publish(21, 1028, 1);
    r.drain();
    r.restart(21, Tear::None);
    r.restart(26, Tear::None);
    r.drain();
    // churn
    r.publish(27, 1029, 1);
    for t in 27..=30 {
        r.tick(t);
    }
    r.publish(31, 1030, 1);
    r.tick(31);
    r.drain();
    r.restart(31, Tear::None);
    // a failed write
    r.publish(31, 1, 3);
    r.job();
    r.write(false);
    r.restart(31, Tear::None);
    // a rerun, with a job out
    r.hold(31, 1);
    r.job();
    r.write(true);
    r.rerun(31, Tear::None);
    r.hold(31, 2);
    r.job();
    r.rerun(32, Tear::Whole);
    r.expect("mail");
    assert_eq!(
        r.job_node(),
        2,
        "the packets of the write out are not written in the next run"
    );
    r.write(true);
    // a hand over
    r.hold(32, 2);
    r.heard(32, 2);
}

fn seeded(seed: u64, prev: Run) -> Run {
    let mut rng = SplitMix64::new(seed);
    let mut r = prev.again();
    for _ in 0..200 {
        let v = rng.next_u64() % 100;
        let t = r.t;
        match v {
            0..30 => {
                let n = (rng.next_u64() % 8) as usize + 1;
                let seq = rng.next_u64() % 3 + 1;
                r.publish(t, n, seq);
            }
            30..50 => r.hold(t, (rng.next_u64() % 3) as usize + 1),
            50..55 => r.heard(t, (rng.next_u64() % 3) as usize + 1),
            55..70 => r.tick(t),
            70..80 => r.tick(t + 1),
            80..97 => {
                if r.job.is_some() {
                    let ok = !rng.next_u64().is_multiple_of(10);
                    r.write(ok);
                } else {
                    r.job();
                }
            }
            97..99 => {
                let at = [0, t.saturating_sub(2), t, t + 1, t + 5][(rng.next_u64() % 5) as usize];
                let tear = pick(&mut rng, &r);
                r.restart(at, tear);
            }
            _ => {
                let tear = pick(&mut rng, &r);
                r.rerun(t, tear);
            }
        }
    }
    r.finish();
    r
}

fn pick(rng: &mut SplitMix64, r: &Run) -> Tear {
    let modes = r.modes();
    modes[(rng.next_u64() % modes.len() as u64) as usize]
}

#[test]
fn facade_relay_keep_trace() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut r = Run::new();
            boundary(&mut r);
            r.finish();
            let mut out = std::mem::take(&mut r.out);
            for seed in 1..=20 {
                r = seeded(seed, r);
                out.push_str(&std::mem::take(&mut r.out));
            }
            let count = |what: &str| out.matches(what).count();
            assert!(count("\"op\":\"write\",\"ok\":false") >= 10, "too few failed writes");
            assert!(count("\"op\":\"rerun\"") >= 3, "too few reruns");
            assert!(count("\"op\":\"job\",\"k\":\"mail\"") >= 12, "too few mail jobs");
            if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(std::path::Path::new(&dir).join("relay-keep.ndjson"), out).unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
