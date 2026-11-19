//! Trace generation for the version 2 statement of the topic broadcast: the real `statement::encode` of
//! `pinc-broadcast` called on field sets at the edges of every field (the CBOR head limits of the integers, the
//! topic and parent bounds, the flag bits, every algorithm tag), the order of its refusals, the widest statement, and
//! seeded random field sets. Every call is one line of `bcast/statement.ndjson` for the TLA+ trace check
//! (`TraceBroadcastStatement.tla`), which checks it against the model's `Encode`; a line carries the fields, and the
//! bytes, the content id and the signed message of an accepted call or the name of the refusal.
//!
//! The test asserts the facts it relies on itself: every statement fits `STATEMENT_MAX` and the widest one fills it,
//! the signed message is the label and the id, equal outputs come only from equal fields, and each refusal is the one
//! the inputs name. The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is
//! written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_lossless,
    unreachable_pub,
    clippy::manual_is_multiple_of
)]

use std::collections::HashSet;
use std::fmt::Write as _;

use pinc_broadcast::statement::{
    ContentId, FLAG_ISB, Fields, MAX_PARENTS, STATEMENT_MAX, StatementError, content_id, encode, signed_message,
};
use pinc_crypto::{IdentityAlg, labels};
use pinc_tests::{SplitMix64, soaking};
use pinc_wire::hlc::Hlc;

/// The values at the edges of the CBOR heads of an integer.
const EDGES: [u64; 10] = [0, 23, 24, 255, 256, 65535, 65536, u32::MAX as u64, 1 << 32, u64::MAX];
/// The same for the 32-bit counter.
const CTR_EDGES: [u32; 8] = [0, 23, 24, 255, 256, 65535, 65536, u32::MAX];

fn arr(b: &[u8]) -> String {
    let v: Vec<String> = b.iter().map(u8::to_string).collect();
    format!("[{}]", v.join(","))
}

/// A set of fields, owned.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Case {
    alg: u8,
    origin: [u8; 32],
    inc: u64,
    seq: u64,
    topic: Vec<u8>,
    wall: u64,
    ctr: u32,
    flags: u8,
    parents: Vec<ContentId>,
    body: [u8; 32],
}

impl Case {
    fn base() -> Self {
        Self {
            alg: 1,
            origin: [7; 32],
            inc: 1,
            seq: 2,
            topic: b"t".to_vec(),
            wall: 3,
            ctr: 4,
            flags: 0,
            parents: Vec::new(),
            body: [9; 32],
        }
    }

    fn with(&self, f: impl FnOnce(&mut Self)) -> Self {
        let mut c = self.clone();
        f(&mut c);
        c
    }
}

/// What the calls so far recorded and saw.
#[derive(Default)]
struct Run {
    out: String,
    outputs: HashSet<Vec<u8>>,
    fields: HashSet<Case>,
    errs: HashSet<String>,
    widest: Option<usize>,
}

impl Run {
    /// Encode `c`, record the call, and check the result is `want` when one is named (`Ok(())` for any success).
    fn go(&mut self, c: &Case, want: Option<Result<(), StatementError>>) {
        let alg = IdentityAlg::from_tag(c.alg).unwrap();
        let fields = Fields {
            origin_alg: alg,
            origin: &c.origin,
            incarnation: c.inc,
            seq: c.seq,
            topic: &c.topic,
            time: Hlc::new(c.wall, c.ctr),
            flags: c.flags,
            parents: &c.parents,
            body: &c.body,
        };
        let mut buf = [0u8; STATEMENT_MAX];
        let r = encode(&fields, &mut buf);
        let parents: Vec<String> = c.parents.iter().map(|p| arr(p)).collect();
        let mut line = format!(
            r#"{{"t":"st","op":"encode","alg":{},"origin":{},"inc":{},"seq":{},"topic":{},"wall":{},"ctr":{},"flags":{},"parents":[{}],"body":{}"#,
            c.alg,
            arr(&c.origin),
            arr(&c.inc.to_be_bytes()),
            arr(&c.seq.to_be_bytes()),
            arr(&c.topic),
            arr(&c.wall.to_be_bytes()),
            arr(&c.ctr.to_be_bytes()),
            c.flags,
            parents.join(","),
            arr(&c.body),
        );
        match r {
            Ok(n) => {
                assert!(n <= STATEMENT_MAX, "a statement of {n} bytes passes STATEMENT_MAX");
                let b = &buf[..n];
                let cid = content_id(b);
                let msg = signed_message(&cid);
                assert_eq!(&msg[..labels::STATEMENT.len()], labels::STATEMENT.as_bytes());
                assert_eq!(&msg[labels::STATEMENT.len()..], &cid[..]);
                assert_eq!(msg.len(), 54);
                if self.fields.insert(c.clone()) {
                    assert!(
                        self.outputs.insert(b.to_vec()),
                        "two different field sets made the same bytes"
                    );
                } else {
                    assert!(self.outputs.contains(b), "the same fields made other bytes");
                }
                let _ = write!(line, r#","b":{},"cid":{},"msg":{}"#, arr(b), arr(&cid), arr(&msg));
                if let Some(w) = want {
                    assert_eq!(w, Ok(()), "a case that must be refused was accepted");
                }
            }
            Err(e) => {
                let _ = write!(line, r#","err":"{e:?}""#);
                self.errs.insert(format!("{e:?}"));
                if let Some(w) = want {
                    assert_eq!(w, Err(e), "the refusal is not the one named");
                }
            }
        }
        line.push_str("}\n");
        self.out.push_str(&line);
    }

    fn ok(&mut self, c: &Case) {
        self.go(c, Some(Ok(())));
    }

    fn refused(&mut self, c: &Case, e: StatementError) {
        self.go(c, Some(Err(e)));
    }
}

/// An ascending list of `n` parents, `[x; 32]` for `x` from `from`.
fn ascending(from: u8, n: usize) -> Vec<ContentId> {
    (0..n).map(|i| [from + u8::try_from(i).unwrap(); 32]).collect()
}

fn boundaries(run: &mut Run) {
    let b = Case::base();
    for alg in 1..=4 {
        run.ok(&b.with(|c| c.alg = alg));
    }
    for v in EDGES {
        run.ok(&b.with(|c| c.inc = v));
        run.ok(&b.with(|c| c.seq = v));
        run.ok(&b.with(|c| c.wall = v));
    }
    for v in CTR_EDGES {
        run.ok(&b.with(|c| c.ctr = v));
    }
    for len in [0usize, 1, 23, 24, 255, 256] {
        let topic: Vec<u8> = (0..len).map(|i| i as u8).collect();
        if len == 256 {
            run.refused(&b.with(|c| c.topic = topic), StatementError::TopicTooLong);
        } else {
            run.ok(&b.with(|c| c.topic = topic));
        }
    }
    run.ok(&b.with(|c| c.flags = 0));
    run.ok(&b.with(|c| c.flags = FLAG_ISB));
    for f in [2u8, 3, 128, 255] {
        run.refused(&b.with(|c| c.flags = f), StatementError::ReservedFlags);
    }
    for n in [0, 1, MAX_PARENTS] {
        run.ok(&b.with(|c| c.parents = ascending(1, n)));
    }
    run.refused(
        &b.with(|c| c.parents = ascending(1, MAX_PARENTS + 1)),
        StatementError::TooManyParents,
    );
    run.refused(
        &b.with(|c| c.parents = vec![[2; 32], [1; 32]]),
        StatementError::ParentsNotAscending,
    );
    run.refused(
        &b.with(|c| c.parents = vec![[1; 32], [1; 32]]),
        StatementError::ParentsNotAscending,
    );
    run.refused(
        &b.with(|c| c.parents = vec![[1; 32], [3; 32], [2; 32]]),
        StatementError::ParentsNotAscending,
    );
    for v in [0u8, 0xff] {
        run.ok(&b.with(|c| c.origin = [v; 32]));
        run.ok(&b.with(|c| c.body = [v; 32]));
    }
}

fn refusal_order(run: &mut Run) {
    let b = Case::base();
    run.refused(
        &b.with(|c| {
            c.topic = vec![0; 256];
            c.parents = ascending(1, 9);
        }),
        StatementError::TopicTooLong,
    );
    run.refused(
        &b.with(|c| c.parents = (0..9u8).rev().map(|x| [x; 32]).collect()),
        StatementError::TooManyParents,
    );
    run.refused(
        &b.with(|c| {
            c.parents = vec![[2; 32], [1; 32]];
            c.flags = 2;
        }),
        StatementError::ParentsNotAscending,
    );
}

fn widest(run: &mut Run) {
    let c = Case {
        alg: 4,
        origin: [0xff; 32],
        inc: u64::MAX,
        seq: u64::MAX,
        topic: vec![0xff; 255],
        wall: u64::MAX,
        ctr: u32::MAX,
        flags: 1,
        parents: (0xf8..=0xffu8).map(|x| [x; 32]).collect(),
        body: [0xff; 32],
    };
    run.ok(&c);
    let alg = IdentityAlg::from_tag(c.alg).unwrap();
    let mut buf = [0u8; STATEMENT_MAX];
    let n = encode(
        &Fields {
            origin_alg: alg,
            origin: &c.origin,
            incarnation: c.inc,
            seq: c.seq,
            topic: &c.topic,
            time: Hlc::new(c.wall, c.ctr),
            flags: c.flags,
            parents: &c.parents,
            body: &c.body,
        },
        &mut buf,
    )
    .unwrap();
    run.widest = Some(n);
}

fn seeded(run: &mut Run) {
    let mut rng = SplitMix64::traced(0x5747_0001);
    for _ in 0..2000 {
        let mut c = Case::base();
        c.alg = u8::try_from(1 + rng.next_u64() % 4).unwrap();
        rng.fill(&mut c.origin);
        rng.fill(&mut c.body);
        let int = |rng: &mut SplitMix64| {
            if rng.next_u64() % 2 == 0 {
                EDGES[usize::try_from(rng.next_u64() % 10).unwrap()]
            } else {
                rng.next_u64()
            }
        };
        c.inc = int(&mut rng);
        c.seq = int(&mut rng);
        c.wall = int(&mut rng);
        c.ctr = if rng.next_u64() % 2 == 0 {
            CTR_EDGES[usize::try_from(rng.next_u64() % 8).unwrap()]
        } else {
            rng.next_u64() as u32
        };
        let len = usize::try_from(rng.next_u64() % 260).unwrap();
        c.topic = (0..len).map(|_| rng.next_u64() as u8).collect();
        c.flags = if rng.next_u64() % 4 < 3 {
            u8::try_from(rng.next_u64() % 2).unwrap()
        } else {
            rng.next_u64() as u8
        };
        let n = usize::try_from(rng.next_u64() % 10).unwrap();
        c.parents = (0..n)
            .map(|_| {
                let mut p = [0u8; 32];
                rng.fill(&mut p);
                p
            })
            .collect();
        if rng.next_u64() % 4 < 3 {
            c.parents.sort_unstable();
            c.parents.dedup();
        }
        run.go(&c, None);
    }
}

#[test]
fn statement_trace() {
    let mut run = Run::default();
    boundaries(&mut run);
    refusal_order(&mut run);
    widest(&mut run);
    assert_eq!(
        run.widest,
        Some(STATEMENT_MAX),
        "the widest statement does not fill STATEMENT_MAX"
    );
    assert_eq!(
        run.fields.len(),
        run.outputs.len(),
        "the distinct outputs and the distinct field sets differ"
    );
    let scripted = run.out.lines().count();
    seeded(&mut run);
    assert!(run.out.lines().count() > scripted + 1000);
    for e in ["TopicTooLong", "TooManyParents", "ParentsNotAscending", "ReservedFlags"] {
        assert!(run.errs.contains(e), "no call was refused with {e}");
    }
    assert!(!run.errs.contains("BufferTooSmall"));
    // the random part's size is a property of its fixed seed's draws
    if !soaking() {
        assert!(run.out.lines().count() > 2000);
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("bcast");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("statement.ndjson"), &run.out).unwrap();
    }
}
