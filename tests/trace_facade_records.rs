//! Trace generation for record discovery through the facade (`crates/pinc/src/records.rs`, `endpoint/records.rs`): two
//! endpoints publish signed records to an in-process store, a third looks them up, and the test tampers with the store
//! (a replay of an older record, a record filed under the wrong node, a forged signature). Recorded as ndjson
//! (`facade_records.ndjson`) for the TLA+ trace check `TraceFacadeRecords.tla`; the sequence numbers are wall
//! milliseconds, so a record is named by its rank among the ones its node signed. No endpoint has a relay: a lookup
//! gives what the table of known records gives. On nuclei.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod pinc_common;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use pinc::{NodeId, Records, Rendezvous};
use pinc_common::{bind, builder, within};
use pinc_connect::record::Record;
use pinc_tests::SplitMix64;

/// The most records of one node the trace instance numbers.
const MAX_RANK: usize = 64;

/// A rendezvous that keeps whatever it is given, by the node the bytes name, and checks nothing: the test can
/// overwrite what it returns.
#[derive(Clone, Default)]
struct Table {
    held: Rc<RefCell<HashMap<NodeId, Vec<u8>>>>,
}

impl Table {
    fn set(&self, node: NodeId, bytes: Vec<u8>) {
        self.held.borrow_mut().insert(node, bytes);
    }

    fn get(&self, node: &NodeId) -> Vec<u8> {
        self.held.borrow().get(node).cloned().unwrap()
    }
}

impl Rendezvous for Table {
    fn publish(&self, record: &[u8]) -> impl std::future::Future<Output = pinc::Result<()>> {
        let node = Record::parse(record).unwrap().node;
        self.held.borrow_mut().insert(node, record.to_vec());
        std::future::ready(Ok(()))
    }

    fn fetch(&self, node: &NodeId) -> impl std::future::Future<Output = Option<Vec<u8>>> {
        std::future::ready(self.held.borrow().get(node).cloned())
    }
}

fn name(i: usize) -> &'static str {
    ["n1", "n2"][i]
}

async fn run(seed: u64, out: &mut String) {
    let table = Table::default();
    let publishers = [
        bind(builder().discovery(Records::new(table.clone()))).await,
        bind(builder().discovery(Records::new(table.clone()))).await,
    ];
    let a = bind(builder().discovery(Records::new(table.clone()))).await;
    let ids = [publishers[0].id(), publishers[1].id()];
    // Every record each publisher signed, in order; rank k is the k-th.
    let mut kept: [Vec<Vec<u8>>; 2] = [Vec::new(), Vec::new()];
    let mut line = |s: String| {
        out.push_str(&s);
        out.push('\n');
    };

    macro_rules! publish {
        ($n:expr) => {{
            let n: usize = $n;
            within(30, publishers[n].publish_record()).await.unwrap();
            kept[n].push(table.get(&ids[n]));
            line(format!(
                r#"{{"op":"publish","n":"{}","rank":{}}}"#,
                name(n),
                kept[n].len()
            ));
        }};
    }
    macro_rules! tamper {
        ($n:expr, $kind:expr, $rank:expr, $by:expr) => {{
            let (n, kind, k, by): (usize, &str, usize, usize) = ($n, $kind, $rank, $by);
            let bytes = match kind {
                "replay" => kept[n][k - 1].clone(),
                "misfiled" => kept[by][k - 1].clone(),
                _ => {
                    let mut b = kept[n][k - 1].clone();
                    *b.last_mut().unwrap() ^= 1;
                    assert!(Record::parse_verified(&b).is_err(), "the forged record still verifies");
                    b
                }
            };
            table.set(ids[n], bytes);
            let by = if kind == "misfiled" { name(by) } else { "" };
            line(format!(
                r#"{{"op":"tamper","n":"{}","kind":"{kind}","rank":{k},"by":"{by}"}}"#,
                name(n)
            ));
        }};
    }
    macro_rules! lookup {
        ($n:expr) => {{
            let n: usize = $n;
            let got = within(30, a.lookup(&ids[n])).await.unwrap();
            let rank = got.map_or(0, |r| {
                assert_eq!(r.node, ids[n], "a lookup answered with another node's record");
                kept[n]
                    .iter()
                    .position(|b| Record::parse(b).unwrap().seq == r.seq)
                    .expect("the returned record is not one the node signed")
                    + 1
            });
            line(format!(r#"{{"op":"lookup","n":"{}","rank":{rank}}}"#, name(n)));
            rank
        }};
    }

    assert_eq!(lookup!(0), 0);
    assert_eq!(lookup!(1), 0);
    publish!(0);
    publish!(0);
    assert_eq!(lookup!(0), 2);
    tamper!(0, "replay", 1, 0);
    assert_eq!(lookup!(0), 2, "a rollback to an older record was believed");
    tamper!(0, "forged", 2, 0);
    assert_eq!(lookup!(0), 2, "a forged record was believed");
    tamper!(1, "misfiled", 2, 0);
    assert_eq!(lookup!(1), 0, "a record filed under another node was believed");

    let mut rng = SplitMix64::traced(seed);
    for _ in 0..300 {
        let n = (rng.next_u64() % 2) as usize;
        match rng.next_u64() % 10 {
            0..3 if kept[n].len() < MAX_RANK => publish!(n),
            3..6 => {
                let other = 1 - n;
                match rng.next_u64() % 3 {
                    0 if !kept[n].is_empty() => {
                        let k = 1 + (rng.next_u64() as usize % kept[n].len());
                        tamper!(n, "replay", k, 0);
                    }
                    1 if !kept[other].is_empty() => {
                        let k = 1 + (rng.next_u64() as usize % kept[other].len());
                        tamper!(n, "misfiled", k, other);
                    }
                    2 if !kept[n].is_empty() => {
                        let k = 1 + (rng.next_u64() as usize % kept[n].len());
                        tamper!(n, "forged", k, 0);
                    }
                    _ => {
                        lookup!(n);
                    }
                }
            }
            _ => {
                lookup!(n);
            }
        }
    }
}

#[nuclei::test]
async fn trace_facade_records() {
    let mut out = String::new();
    run(1, &mut out).await;
    for seed in 2..=4 {
        run(seed, &mut String::new()).await;
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("facade_records.ndjson"), &out).unwrap();
    }
}
