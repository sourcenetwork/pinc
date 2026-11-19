//! Model-based tests of the handshake's output queue: a real `Outbox` of `pinc-security`, reached through the `trace`
//! probe `OutboxProbe`, driven along every edge of the state graph of `proofs/tla/MbtOutbox.tla`.
//!
//! TLC enumerates every state the operators of `OutboxOps.tla` reach within the bounds of `MbtOutbox.cfg` and writes the
//! graph; `scripts/mbt.py` turns it into paths from the empty queue that take every edge, which `scripts/proofs.sh`
//! writes to the directory `PINC_MBT_DIR` as `outbox.ndjson`. This test runs each path on a fresh probe: every call of
//! the model is the call of the same name on the queue (a build of `k` bytes of value `k`, a refused build that writes
//! `w` bytes of value 9 and then fails, a request, early keys or an established event of a mark, a failure of a code,
//! a poll that must hand out what the model says). After every call the queue's own state read through the probe (the
//! length and the first two bytes of the buffer, the padding floor, the send flag, the request and whether it was
//! announced, the events queued) must be the model's. It stops at the first difference and names the file, the case,
//! the step, the field and the calls that led there. Without `PINC_MBT_DIR` the walk checks nothing, while
//! `order_without_model` always runs: seeded random calls against a reference of the order the module documents.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::match_same_arms
)]

use std::fmt::Write as _;

use pinc_crypto::{Aead, IdentityAlg, NodeId, Secret};
use pinc_security::credit::CreditRecord;
use pinc_security::{
    Alpn, EarlyKeys, Established, Event, Failure, KeyHandle, KeyRequest, OutboxProbe, OutboxView, Output, TicketBatch,
    Traffic,
};
use pinc_tests::{Json, MbtCase, SplitMix64, mbt_cases};
use pinc_wire::WireError;

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

fn nums(v: &Json) -> Vec<u64> {
    v.arr().unwrap().iter().map(num).collect()
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

fn early_keys(e: u64) -> EarlyKeys {
    EarlyKeys {
        aead: Aead::ChaCha20Poly1305,
        secret: Secret::new([e as u8; 32]),
    }
}

fn established(e: u64) -> Established {
    let e = e as u8;
    Established {
        peer: NodeId {
            alg: IdentityAlg::Ed25519,
            bytes: [e; 32],
        },
        alpn: Alpn::new(b"m").unwrap(),
        traffic: Traffic {
            aead: Aead::ChaCha20Poly1305,
            send: Secret::new([e; 32]),
            recv: Secret::new([e; 32]),
        },
        resume: Secret::new([e; 32]),
        tickets: TicketBatch::new(),
        resumed: false,
        peer_credit: CreditRecord::NONE,
        local_credit: CreditRecord::NONE,
        remembered_credit: CreditRecord::NONE,
        cid_secret: Secret::new([e; 32]),
    }
}

fn failure(f: u64) -> Failure {
    match f {
        1 => Failure::KeyOperation,
        2 => Failure::Randomness,
        _ => panic!("a failure code the test does not know: {f}"),
    }
}

fn failure_code(f: Option<&Failure>) -> u64 {
    match f {
        None => 0,
        Some(Failure::KeyOperation) => 1,
        Some(Failure::Randomness) => 2,
        Some(other) => panic!("a failure the test does not know: {other:?}"),
    }
}

/// The mark of a request read back: 0 none, 1 the Sign of key 1, 2 the Decapsulate of key 2.
fn request_mark(r: Option<(bool, KeyHandle)>) -> u64 {
    match r {
        None => 0,
        Some((false, KeyHandle(1))) => 1,
        Some((true, KeyHandle(2))) => 2,
        Some(other) => panic!("a request the test does not know: {other:?}"),
    }
}

fn set_request(p: &mut OutboxProbe, r: u64) {
    match r {
        1 => p.set_request(false, KeyHandle(1)),
        2 => p.set_request(true, KeyHandle(2)),
        _ => panic!("a request mark the test does not know: {r}"),
    }
}

/// The queue's state against the model's `ob`, field by field.
fn same_state(v: &OutboxView, ob: &Json, at: &dyn Fn() -> String) {
    let field = |n: &str| {
        ob.get(n)
            .unwrap_or_else(|| panic!("{}: the model's state has no {n}", at()))
    };
    let flag = |n: &str| u64::from(field(n).bool().unwrap());
    let fields: [(&str, Vec<u64>, Vec<u64>); 10] = [
        ("len", vec![v.len as u64], vec![num(field("len"))]),
        (
            "buf",
            v.head.iter().map(|b| u64::from(*b)).collect(),
            nums(field("buf")),
        ),
        ("minl", vec![v.min_len as u64], vec![num(field("minl"))]),
        ("send", vec![u64::from(v.send)], vec![flag("send")]),
        ("req", vec![request_mark(v.request)], vec![num(field("req"))]),
        ("ann", vec![u64::from(v.announced)], vec![flag("ann")]),
        (
            "early",
            vec![v.early.as_ref().map_or(0, |k| u64::from(k.secret.expose()[0]))],
            vec![num(field("early"))],
        ),
        (
            "est",
            vec![v.established.as_ref().map_or(0, |e| u64::from(e.peer.bytes[0]))],
            vec![num(field("est"))],
        ),
        ("rr", vec![u64::from(v.resume_rejected)], vec![flag("rr")]),
        (
            "failed",
            vec![failure_code(v.failed.as_ref())],
            vec![num(field("failed"))],
        ),
    ];
    for (name, got, want) in fields {
        assert_eq!(
            got,
            want,
            "{}: the field {name} is {got:?}, the model's is {want:?}",
            at()
        );
    }
}

/// What `poll` handed out, as the model's triple reads it (the code is 0 for nothing).
fn poll_matches(p: &mut OutboxProbe, code: u64, data: &[u8], x: u64, at: &dyn Fn() -> String) {
    let got = p.poll();
    let ok = match (code, &got) {
        (0, None) => true,
        (1, Some(Output::Key(KeyRequest::Sign { key, .. }))) => x == 1 && *key == KeyHandle(1),
        (1, Some(Output::Key(KeyRequest::Decapsulate { key, .. }))) => x == 2 && *key == KeyHandle(2),
        (2, Some(Output::Send { data: d, min_len })) => *d == data && *min_len as u64 == x,
        (3, Some(Output::Event(Event::EarlyKeys(k)))) => u64::from(k.secret.expose()[0]) == x,
        (4, Some(Output::Event(Event::ResumeRejected))) => true,
        (5, Some(Output::Event(Event::Established(e)))) => u64::from(e.peer.bytes[0]) == x,
        (6, Some(Output::Event(Event::Failed(f)))) => failure_code(Some(f)) == x,
        _ => false,
    };
    assert!(
        ok,
        "{}: poll handed out {got:?}, the model's is code {code}, data {data:?}, x {x}",
        at()
    );
}

/// Runs one case of `file` on a fresh queue; returns the number of calls.
fn run(file: &str, case: &MbtCase, init: &Json) -> usize {
    let who = format!("{file} case {}", case.id);
    let mut p = OutboxProbe::new();
    same_state(&p.view(), init, &|| format!("{who}: the empty queue"));
    for (i, st) in case.steps.iter().enumerate() {
        let at = || format!("{who} step {i}; calls:{}", calls(case, i));
        match (st.call.as_str(), st.args.as_slice()) {
            ("CallBuild", [k, ml]) => {
                let k = num(k);
                assert_eq!(
                    p.build(num(ml) as usize, &vec![k as u8; k as usize], false),
                    Ok(()),
                    "{}",
                    at()
                );
            }
            ("CallRefuse", [w]) => {
                assert_eq!(
                    p.build(0, &vec![9u8; num(w) as usize], true),
                    Err(Failure::BadPayload(WireError::Unexpected("probe"))),
                    "{}",
                    at()
                );
            }
            ("CallClear", []) => p.clear_message(),
            ("CallResend", []) => p.resend(),
            ("CallRR", []) => p.set_resume_rejected(),
            ("CallSetRequest", [r]) => set_request(&mut p, num(r)),
            ("CallTake", [r]) => {
                let r = num(r);
                assert_eq!(p.take_request(), (r != 0).then_some(KeyHandle(r)), "{}", at());
            }
            ("CallPending", [r]) => {
                let r = num(r);
                assert_eq!(p.pending(), (r != 0).then_some(KeyHandle(r)), "{}", at());
            }
            ("CallEarly", [e]) => p.set_early(early_keys(num(e))),
            ("CallEst", [e]) => p.set_established(established(num(e))),
            ("CallFail", [f]) => p.fail(failure(num(f))),
            ("CallPoll", [t]) => {
                let t = t.arr().unwrap();
                let data: Vec<u8> = nums(&t[1]).iter().map(|b| *b as u8).collect();
                poll_matches(&mut p, num(&t[0]), &data, num(&t[2]), &at);
            }
            _ => panic!("{who}: a call the test does not know: {st}"),
        }
        same_state(&p.view(), st.state.get("ob").unwrap(), &at);
    }
    case.steps.len()
}

/// Walks every case of `file`; false when `PINC_MBT_DIR` is unset.
fn walk(file: &str) -> bool {
    let Some(cases) = mbt_cases(file) else {
        return false;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let c = head.get("constants").unwrap();
    for n in ["MLS", "FAILW", "REQS", "EARLYS", "ESTS", "FAILS"] {
        nums(c.get(n).unwrap_or_else(|| panic!("{file}: the constants have no {n}")));
    }
    assert_eq!(
        nums(c.get("KS").unwrap()),
        [1, 2],
        "{file}: the model's buffer does not hold 2 bytes"
    );
    let init = head.get("init").unwrap().get("ob").unwrap();
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        steps += run(file, &case.unwrap(), init);
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert_eq!(
        (n, steps as u64),
        (count("cases"), count("steps")),
        "{file}: the file ends early"
    );
    eprintln!(
        "mbt_outbox: {file}: {n} cases, {steps} calls, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
    true
}

#[test]
fn walk_graph() {
    // MbtOutbox.cfg
    if !walk("outbox.ndjson") {
        eprintln!("mbt_outbox: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
    }
}

/// One thing the queue handed out.
#[derive(Debug, PartialEq, Eq)]
enum Item {
    Key(bool, u64),
    Send(Vec<u8>, usize),
    Early(u8),
    ResumeRejected,
    Established(u8),
    Failed(u64),
}

impl Item {
    /// The index of its kind, in the order the module documents.
    const fn rank(&self) -> usize {
        match self {
            Self::Key(..) => 0,
            Self::Send(..) => 1,
            Self::Early(_) => 2,
            Self::ResumeRejected => 3,
            Self::Established(_) => 4,
            Self::Failed(_) => 5,
        }
    }
}

fn item(o: Option<Output<'_>>) -> Option<Item> {
    Some(match o? {
        Output::Key(KeyRequest::Sign { key, .. }) => Item::Key(false, key.0),
        Output::Key(KeyRequest::Decapsulate { key, .. }) => Item::Key(true, key.0),
        Output::Send { data, min_len } => Item::Send(data.to_vec(), min_len),
        Output::Event(Event::EarlyKeys(k)) => Item::Early(k.secret.expose()[0]),
        Output::Event(Event::ResumeRejected) => Item::ResumeRejected,
        Output::Event(Event::Established(e)) => Item::Established(e.peer.bytes[0]),
        Output::Event(Event::Failed(f)) => Item::Failed(failure_code(Some(&f))),
    })
}

/// The queue as the module doc describes it: one slot per kind, the request and whether it was announced, and the
/// message kept to send again.
#[derive(Default)]
struct Reference {
    request: Option<(bool, u64)>,
    announced: bool,
    kept: Option<(Vec<u8>, usize)>,
    send: bool,
    early: Option<u8>,
    resume_rejected: bool,
    established: Option<u8>,
    failed: Option<u64>,
}

impl Reference {
    fn poll(&mut self) -> Option<Item> {
        if !self.announced
            && let Some((decap, key)) = self.request
        {
            self.announced = true;
            return Some(Item::Key(decap, key));
        }
        if self.send {
            self.send = false;
            return self.kept.clone().map(|(d, m)| Item::Send(d, m));
        }
        if let Some(e) = self.early.take() {
            return Some(Item::Early(e));
        }
        if std::mem::take(&mut self.resume_rejected) {
            return Some(Item::ResumeRejected);
        }
        if let Some(e) = self.established.take() {
            return Some(Item::Established(e));
        }
        self.failed.take().map(Item::Failed)
    }

    fn fail(&mut self, f: u64) {
        self.send = false;
        self.request = None;
        self.early = None;
        self.established = None;
        self.resume_rejected = false;
        self.failed = Some(f);
    }
}

#[test]
fn order_without_model() {
    let mut handed = [false; 6];
    for seed in 1..=16u64 {
        let mut rng = SplitMix64::traced(seed);
        let mut p = OutboxProbe::new();
        let mut r = Reference::default();
        for step in 0..2000 {
            let at = format!("seed {seed} call {step}");
            match rng.next_u64() % 10 {
                0 => {
                    let n = 1 + (rng.next_u64() % 64) as usize;
                    // a value that is not 9, which the refused builds of the model write
                    let v = match (rng.next_u64() % 255) as u8 {
                        x if x >= 9 => x + 1,
                        x => x,
                    };
                    let min_len = (rng.next_u64() % 1500) as usize;
                    let bytes = vec![v; n];
                    assert_eq!(p.build(min_len, &bytes, false), Ok(()), "{at}");
                    r.kept = Some((bytes, min_len));
                    r.send = true;
                }
                1 => {
                    p.clear_message();
                    r.kept = None;
                    r.send = false;
                }
                2 => {
                    p.resend();
                    r.send = r.kept.is_some();
                }
                3 => {
                    let decap = rng.next_u64() % 2 == 0;
                    let key = 1 + rng.next_u64() % 3;
                    p.set_request(decap, KeyHandle(key));
                    r.request = Some((decap, key));
                    r.announced = false;
                }
                4 => {
                    let want = r.request.take().map(|(_, k)| KeyHandle(k));
                    r.announced = false;
                    assert_eq!(p.take_request(), want, "{at}");
                }
                5 => {
                    let m = 1 + rng.next_u64() % 3;
                    p.set_early(early_keys(m));
                    r.early = Some(m as u8);
                }
                6 => {
                    let m = 1 + rng.next_u64() % 3;
                    p.set_established(established(m));
                    r.established = Some(m as u8);
                }
                7 => {
                    p.set_resume_rejected();
                    r.resume_rejected = true;
                }
                8 => {
                    let f = 1 + rng.next_u64() % 2;
                    p.fail(failure(f));
                    r.fail(f);
                }
                _ => {
                    let got = item(p.poll());
                    let want = r.poll();
                    assert_eq!(
                        got, want,
                        "{at}: the item handed out is not the reference's lowest kind"
                    );
                    if let Some(i) = got {
                        handed[i.rank()] = true;
                    }
                }
            }
        }
    }
    assert!(handed.iter().all(|h| *h), "a kind was never handed out: {handed:?}");
}
