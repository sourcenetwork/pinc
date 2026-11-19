//! Trace generation for the wire form of a node id (`pinc_connect::carrier::node`): seeded and boundary calls of the
//! real `read` and `write`, recorded as ndjson (`connect_node.ndjson`) for the TLA+ trace check
//! (`TraceConnectNodeId.tla`).
//!
//! Two kinds of event, one per call: `nrd` (`node::read` on the bytes a reader had left: every tag byte with each
//! body, with and without bytes after the id, every cut of an id, a reader that had consumed a prefix, and random
//! bytes) and `nwr` (`node::write` of every known algorithm into a slice of every room from 0 to 40, and random
//! ones).
//!
//! The test checks by itself: a read is `Ok` exactly when 33 bytes remain and the tag is known, consumes exactly 33 on
//! success and nothing on an error; a write succeeds exactly with 33 bytes of room and the bytes it writes are the tag
//! and the body; reading then writing gives the input back.
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
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_connect::carrier::node::{self, NODE_ID_LEN};
use pinc_crypto::{IdentityAlg, NodeId};
use pinc_tests::{SplitMix64, soaking};
use pinc_wire::{Reader, WireError, Writer};

fn arr(b: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, x) in b.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(s, "{x}");
    }
    s.push(']');
    s
}

/// What the events recorded.
#[derive(Default)]
struct Seen {
    ok: u32,
    trunc: u32,
    tag: u32,
    wok: u32,
    small: u32,
}

struct T {
    out: String,
    seen: Seen,
}

impl T {
    /// One `node::read` on `buf`, after a reader that already consumed `skip` bytes of it.
    fn read(&mut self, buf: &[u8], skip: usize) {
        let mut r = Reader::new(buf);
        for _ in 0..skip {
            r.read_u8().unwrap();
        }
        let input = &buf[skip..];
        let before = r.position();
        let res = node::read(&mut r);
        let used = r.position() - before;
        let known = input.first().and_then(|t| IdentityAlg::from_tag(*t));
        match res {
            Ok(id) => {
                assert!(
                    input.len() >= NODE_ID_LEN && known.is_some(),
                    "an id was read from {input:?}"
                );
                assert_eq!(used, NODE_ID_LEN);
                assert_eq!(id.bytes[..], input[1..NODE_ID_LEN]);
                let mut back = [0u8; NODE_ID_LEN];
                let mut w = Writer::new(&mut back);
                node::write(&mut w, &id).unwrap();
                assert_eq!(
                    w.written(),
                    &input[..NODE_ID_LEN],
                    "write does not give back what was read"
                );
                self.seen.ok += 1;
                let _ = writeln!(
                    self.out,
                    r#"{{"t":"nrd","in":{},"kind":"ok","alg":{},"bytes":{},"needed":0,"used":{used}}}"#,
                    arr(input),
                    id.alg.tag(),
                    arr(&id.bytes)
                );
            }
            Err(e) => {
                assert_eq!(used, 0, "a failed read consumed bytes");
                let (kind, needed) = match e {
                    WireError::Truncated { needed } => {
                        assert!(input.len() < NODE_ID_LEN, "truncated with 33 bytes left");
                        assert_eq!(needed, if input.is_empty() { 1 } else { NODE_ID_LEN - input.len() });
                        self.seen.trunc += 1;
                        ("trunc", needed)
                    }
                    WireError::Unexpected(_) => {
                        assert!(
                            input.len() >= NODE_ID_LEN && known.is_none(),
                            "an unknown tag was refused wrongly"
                        );
                        self.seen.tag += 1;
                        ("tag", 0)
                    }
                    other => panic!("read gave {other:?}"),
                };
                let _ = writeln!(
                    self.out,
                    r#"{{"t":"nrd","in":{},"kind":"{kind}","alg":0,"bytes":[],"needed":{needed},"used":{used}}}"#,
                    arr(input)
                );
            }
        }
    }

    /// One `node::write` of `id` into `room` bytes.
    fn write(&mut self, id: &NodeId, room: usize) {
        let mut buf = vec![0u8; room];
        let mut w = Writer::new(&mut buf);
        let res = node::write(&mut w, id);
        let head = format!(
            r#"{{"t":"nwr","alg":{},"bytes":{},"room":{room},"#,
            id.alg.tag(),
            arr(&id.bytes)
        );
        match res {
            Ok(()) => {
                assert!(room >= NODE_ID_LEN, "a write fit into {room} bytes");
                let mut want = vec![id.alg.tag()];
                want.extend_from_slice(&id.bytes);
                assert_eq!(w.written(), &want[..]);
                self.seen.wok += 1;
                let _ = writeln!(self.out, r#"{head}"kind":"ok","out":{},"needed":0}}"#, arr(&want));
            }
            Err(WireError::BufferTooSmall { needed }) => {
                assert!(room < NODE_ID_LEN, "a write was refused with {room} bytes of room");
                assert_eq!(needed, NODE_ID_LEN - room);
                assert!(w.written().is_empty(), "a refused write left bytes");
                self.seen.small += 1;
                let _ = writeln!(self.out, r#"{head}"kind":"small","out":[],"needed":{needed}}}"#);
            }
            Err(other) => panic!("write gave {other:?}"),
        }
    }
}

const ALGS: [u8; 4] = [1, 2, 3, 4];

fn id_of(tag: u8, body: [u8; 32]) -> NodeId {
    NodeId {
        alg: IdentityAlg::from_tag(tag).unwrap(),
        bytes: body,
    }
}

#[test]
fn node_id_wire_matches_the_model() {
    let mut rng = SplitMix64::traced(0x4E0D_E1D5);
    let mut t = T {
        out: String::new(),
        seen: Seen::default(),
    };
    let mut bodies: Vec<[u8; 32]> = vec![[0; 32], core::array::from_fn(|i| i as u8 + 1), [255; 32]];
    for _ in 0..4 {
        let mut b = [0u8; 32];
        rng.fill(&mut b);
        bodies.push(b);
    }
    let with_tag = |tag: u8, body: &[u8; 32]| {
        let mut v = vec![tag];
        v.extend_from_slice(body);
        v
    };
    // 1. every tag byte with every body, then with rests behind it
    for tag in 0..=255u8 {
        for body in &bodies {
            let ids = with_tag(tag, body);
            t.read(&ids, 0);
            for rest in [&[][..], &[0], &[9, 255]] {
                let mut v = ids.clone();
                v.extend_from_slice(rest);
                t.read(&v, 0);
            }
        }
    }
    // 2. every cut
    for tag in [0u8, 1, 2, 3, 4, 5, 127, 255] {
        for body in &bodies {
            let ids = with_tag(tag, body);
            for k in 0..=32 {
                t.read(&ids[..k], 0);
            }
        }
    }
    // 3. a reader that already consumed a prefix
    let body: [u8; 32] = core::array::from_fn(|i| i as u8 + 1);
    for tag in [1u8, 0] {
        let mut v = vec![7u8, 7];
        v.extend(with_tag(tag, &body));
        t.read(&v, 2);
    }
    // 4. every known algorithm into every room
    for alg in ALGS {
        for body in &bodies {
            let id = id_of(alg, *body);
            for room in 0..=40 {
                t.write(&id, room);
            }
        }
    }
    // 5. random reads
    for i in 0..500 {
        let len = (rng.next_u64() % 41) as usize;
        let mut v = vec![0u8; len];
        rng.fill(&mut v);
        if i % 2 == 0
            && let Some(first) = v.first_mut()
        {
            *first = (rng.next_u64() % 7) as u8;
        }
        t.read(&v, 0);
    }
    // 6. random writes
    for _ in 0..200 {
        let alg = ALGS[(rng.next_u64() % 4) as usize];
        let mut body = [0u8; 32];
        rng.fill(&mut body);
        let room = (rng.next_u64() % 41) as usize;
        t.write(&id_of(alg, body), room);
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("connect_node.ndjson"), &t.out).unwrap();
    }
    if !soaking() {
        let s = &t.seen;
        assert!(
            s.ok > 0 && s.trunc > 0 && s.tag > 0,
            "a kind of read was never recorded"
        );
        assert!(s.wok > 0 && s.small > 0, "a kind of write was never recorded");
    }
}
