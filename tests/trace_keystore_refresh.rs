//! Trace generation for the software key store's sources, reseed and refresh: stores from entropy `S1` and `S2` and on
//! the operating system run through every sequence of three calls among `random` (32 bytes), `reseed` with `Z`, `E1` or
//! `E2`, and `refresh` answering no, `Z`, `E1` or `E2`, then a final `random`. They are recorded as ndjson
//! (`keystore_refresh.ndjson`) for the TLA+ trace check (`TraceKeystoreRefresh.tla`): a "run" event has the calls,
//! every output in hex and how often `fresh` was called; a "ref" event has the first two 32-byte fills of a reference
//! `Drbg::new(seed)`; an "unseal" event says whether data one store sealed another store (or the same) unsealed.
//! `Z` is all zeros, the identity of a reseed in the model.
//!
//! The test asserts, without the model, against a plain reference generator: a generator store's outputs are the
//! reference's fills after the sealing key's (a reseed mixes in, a refresh mixes in exactly when `fresh` answered
//! true), `fresh` is called once per refresh of a generator store and never by a store on the operating system (which
//! ignores a reseed), no output repeats an earlier one, and a sealed blob opens in the same store and in a store from
//! the same entropy, and in no other. The trace is written to the directory in `PINC_TRACE_DIR` when it is set;
//! otherwise nothing is written.
#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use std::collections::HashSet;
use std::fmt::Write as _;

use pinc_crypto::Drbg;
use pinc_keystore::{KeyStore, SoftwareStore};

#[derive(Clone, Copy)]
enum Op {
    Random,
    Reseed(&'static str),
    Refresh(&'static str),
}

const OPS: [Op; 8] = [
    Op::Random,
    Op::Reseed("Z"),
    Op::Reseed("E1"),
    Op::Reseed("E2"),
    Op::Refresh("no"),
    Op::Refresh("Z"),
    Op::Refresh("E1"),
    Op::Refresh("E2"),
];

fn seed(name: &str) -> [u8; 32] {
    match name {
        "S1" => [0x51; 32],
        "S2" => [0x52; 32],
        _ => unreachable!(),
    }
}

fn ent(name: &str) -> [u8; 32] {
    match name {
        "Z" => [0; 32],
        "E1" => [0xe1; 32],
        "E2" => [0xe2; 32],
        _ => unreachable!(),
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().fold(String::new(), |mut s, x| {
        let _ = write!(s, "{x:02x}");
        s
    })
}

fn ops_json(ops: &[Op]) -> String {
    let items: Vec<String> = ops
        .iter()
        .map(|o| match o {
            Op::Random => "[\"random\"]".to_string(),
            Op::Reseed(e) => format!("[\"reseed\",\"{e}\"]"),
            Op::Refresh(a) => format!("[\"refresh\",\"{a}\"]"),
        })
        .collect();
    format!("[{}]", items.join(","))
}

/// The calls on a store: its random outputs and how often `fresh` was called.
fn run_ops(store: &mut SoftwareStore, ops: &[Op]) -> (Vec<[u8; 32]>, u32) {
    let (mut outs, mut asked) = (Vec::new(), 0);
    for op in ops {
        match *op {
            Op::Random => {
                let mut b = [0u8; 32];
                store.random(&mut b).unwrap();
                outs.push(b);
            }
            Op::Reseed(e) => store.reseed(&ent(e)),
            Op::Refresh(a) => store.refresh(&mut |bytes| {
                asked += 1;
                if a == "no" {
                    return false;
                }
                *bytes = ent(a);
                true
            }),
        }
    }
    (outs, asked)
}

/// The same calls on a plain generator: the sealing key's fill first, then each call as the docs of the store say.
fn reference(seed_name: &str, ops: &[Op]) -> (Vec<[u8; 32]>, u32) {
    let mut d = Drbg::new(&seed(seed_name));
    let mut skip = [0u8; 32];
    d.fill(&mut skip).unwrap();
    let (mut outs, mut asked) = (Vec::new(), 0);
    for op in ops {
        match *op {
            Op::Random => {
                let mut b = [0u8; 32];
                d.fill(&mut b).unwrap();
                outs.push(b);
            }
            Op::Reseed(e) => d.reseed(&ent(e)),
            Op::Refresh(a) => {
                asked += 1;
                if a != "no" {
                    d.reseed(&ent(a));
                }
            }
        }
    }
    (outs, asked)
}

fn sequences() -> Vec<Vec<Op>> {
    let mut all = Vec::new();
    for a in OPS {
        for b in OPS {
            for c in OPS {
                all.push(vec![a, b, c, Op::Random]);
            }
        }
    }
    all
}

fn outs_json(outs: &[[u8; 32]]) -> String {
    format!(
        "[{}]",
        outs.iter()
            .map(|o| format!("\"{}\"", hex(o)))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn runs(out: &mut String) {
    for ops in sequences() {
        for name in ["S1", "S2"] {
            let mut store = SoftwareStore::from_entropy(seed(name));
            let (outs, asked) = run_ops(&mut store, &ops);
            let (want, want_asked) = reference(name, &ops);
            assert_eq!(outs, want, "{name} {}", ops_json(&ops));
            assert_eq!(asked, want_asked, "{name} {}", ops_json(&ops));
            let _ = writeln!(
                out,
                "{{\"t\":\"ksr\",\"op\":\"run\",\"src\":\"drbg\",\"seed\":\"{name}\",\"ops\":{},\"outs\":{},\"asked\":{asked}}}",
                ops_json(&ops),
                outs_json(&outs)
            );
        }
        let mut store = SoftwareStore::new().unwrap();
        let (outs, asked) = run_ops(&mut store, &ops);
        assert_eq!(asked, 0, "a store on the operating system never calls fresh");
        assert_eq!(outs.len(), ops.iter().filter(|o| matches!(o, Op::Random)).count());
        let _ = writeln!(
            out,
            "{{\"t\":\"ksr\",\"op\":\"run\",\"src\":\"os\",\"ops\":{},\"outs\":{},\"asked\":0}}",
            ops_json(&ops),
            outs_json(&outs)
        );
    }
}

fn refs(out: &mut String) {
    for name in ["S1", "S2"] {
        let mut d = Drbg::new(&seed(name));
        let (mut a, mut b) = ([0u8; 32], [0u8; 32]);
        d.fill(&mut a).unwrap();
        d.fill(&mut b).unwrap();
        let _ = writeln!(
            out,
            "{{\"t\":\"ksr\",\"op\":\"ref\",\"seed\":\"{name}\",\"fills\":[\"{}\",\"{}\"]}}",
            hex(&a),
            hex(&b)
        );
    }
}

/// A store, its label (`S1`, `S2` or `os`) and its id.
struct Labelled {
    store: SoftwareStore,
    label: &'static str,
    id: u32,
}

fn unseals(out: &mut String) {
    let mut next = 0;
    let mut make = |label: &'static str| {
        next += 1;
        let store = if label == "os" {
            SoftwareStore::new().unwrap()
        } else {
            SoftwareStore::from_entropy(seed(label))
        };
        Labelled { store, label, id: next }
    };
    let mut emit = |a: &mut Labelled, b: Option<&mut Labelled>| {
        let sealed = a.store.seal(b"the sealed value").unwrap();
        let (same, bl, bid, ok) = match b {
            None => (true, a.label, a.id, a.store.unseal(&sealed).is_ok()),
            Some(b) => (false, b.label, b.id, b.store.unseal(&sealed).is_ok()),
        };
        // A key is the sealing key: the seed's, or the store's own on the operating system.
        let want = same || (a.label == bl && a.label != "os");
        assert_eq!(ok, want, "{} {} unsealed by {} {}", a.label, a.id, bl, bid);
        let _ = writeln!(
            out,
            "{{\"t\":\"ksr\",\"op\":\"unseal\",\"ok\":{ok},\"same\":{same},\"a\":\"{}\",\"aid\":{},\"b\":\"{bl}\",\"bid\":{bid}}}",
            a.label, a.id
        );
    };
    for label in ["S1", "S2", "os"] {
        for op in OPS {
            let mut a = make(label);
            run_ops(&mut a.store, &[op]);
            emit(&mut a, None);
            for other in ["S1", "S2", "os"] {
                let mut b = make(other);
                run_ops(&mut b.store, &[Op::Random, Op::Reseed("E1")]);
                emit(&mut a, Some(&mut b));
            }
        }
    }
}

#[test]
fn the_sources_reseed_and_refresh_of_a_software_store_match_the_reference() {
    let mut out = String::new();
    refs(&mut out);
    runs(&mut out);
    unseals(&mut out);
    // Every output of a run is its own: none repeats within a run.
    for line in out.lines().filter(|l| l.contains("\"op\":\"run\"")) {
        let outs = line.split("\"outs\":[").nth(1).unwrap().split(']').next().unwrap();
        let all: Vec<&str> = outs.split(',').collect();
        assert_eq!(all.len(), all.iter().collect::<HashSet<_>>().len(), "{line}");
    }
    assert_eq!(out.lines().count(), 2 + 512 * 3 + 3 * 8 * 4);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("keystore_refresh.ndjson"), out).unwrap();
    }
}
