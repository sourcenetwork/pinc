//! Trace generation for the amplification ledger: scripted and seeded runs of the real `Ledger` of `pinc-core`,
//! recorded as ndjson (`ledger.ndjson`) for the TLA+ trace check (`TraceLedger.tla`).
//!
//! A run starts with a fresh ledger and makes calls to `on_receive`, `open`, `validate` and `allow_send`: a table
//! filled past its capacity, held and validated addresses, zero sizes, counters at `u64::MAX`, and 16 seeded runs (4 of
//! them over more addresses than the table holds). Every call is written with its answer, the length of the table and the entry of
//! the address called and of a second address; a `u64` is written as four 16-bit limbs (TLC cannot read a number above
//! 2^31) and an address as its id.
//!
//! The test asserts what it can itself: after every call the answer, the length and both entries equal those of a
//! naive ledger written from the module documentation, so it is meaningful without the proof tools.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::too_many_arguments,
    unreachable_pub
)]

use std::collections::HashSet;
use std::fmt::Write as _;
use std::net::SocketAddr;

use pinc_core::{DATAGRAM_OVERHEAD, FACTOR, LEDGER_ENTRIES, Ledger, LedgerEntry};
use pinc_tests::SplitMix64;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    Rx,
    Open,
    Valid,
    Tx,
}

type Call = (Op, u32, u64);

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn entry_json(e: Option<LedgerEntry>) -> String {
    match e {
        None => r#"{"has":false,"rx":[0,0,0,0],"tx":[0,0,0,0],"valid":false}"#.to_string(),
        Some(e) => format!(
            r#"{{"has":true,"rx":{},"tx":{},"valid":{}}}"#,
            limbs(e.rx),
            limbs(e.tx),
            e.validated
        ),
    }
}

fn addr(x: u32) -> SocketAddr {
    SocketAddr::from(([10, (x >> 16) as u8, (x >> 8) as u8, x as u8], 4000))
}

/// The ledger as its module documentation describes it: a list in insertion order.
struct Naive {
    v: Vec<(SocketAddr, LedgerEntry)>,
    evicted: HashSet<SocketAddr>,
    reinserted: u32,
}

impl Naive {
    fn find(&self, a: SocketAddr) -> Option<usize> {
        self.v.iter().position(|(k, _)| *k == a)
    }

    fn get(&self, a: SocketAddr) -> Option<LedgerEntry> {
        self.find(a).map(|i| self.v[i].1)
    }

    fn insert(&mut self, a: SocketAddr, e: LedgerEntry) {
        if self.v.len() == LEDGER_ENTRIES {
            let (gone, _) = self.v.remove(0);
            self.evicted.insert(gone);
        }
        if self.evicted.remove(&a) {
            self.reinserted += 1;
        }
        self.v.push((a, e));
    }

    fn on_receive(&mut self, a: SocketAddr, n: u64) -> bool {
        if let Some(i) = self.find(a) {
            let e = &mut self.v[i].1;
            e.rx = e.rx.saturating_add(n);
            return !e.validated;
        }
        self.insert(
            a,
            LedgerEntry {
                rx: n,
                tx: 0,
                validated: false,
            },
        );
        true
    }

    fn open(&mut self, a: SocketAddr) {
        match self.find(a) {
            Some(i) => self.v[i].1.validated = true,
            None => self.insert(
                a,
                LedgerEntry {
                    rx: 0,
                    tx: 0,
                    validated: true,
                },
            ),
        }
    }

    fn validate(&mut self, a: SocketAddr) {
        if let Some(i) = self.find(a) {
            self.v[i].1.validated = true;
        }
    }

    fn allow_send(&mut self, a: SocketAddr, n: u64) -> bool {
        let charge = n.saturating_add(DATAGRAM_OVERHEAD);
        let Some(i) = self.find(a) else {
            self.insert(
                a,
                LedgerEntry {
                    rx: 0,
                    tx: charge,
                    validated: true,
                },
            );
            return true;
        };
        let e = &mut self.v[i].1;
        if e.validated {
            e.tx = e.tx.saturating_add(charge);
            return true;
        }
        let Some(tx) = e.tx.checked_add(charge) else {
            return false;
        };
        if u128::from(tx) > u128::from(e.rx) * u128::from(FACTOR) {
            return false;
        }
        e.tx = tx;
        true
    }
}

#[derive(Default)]
struct Stats {
    calls: u32,
    held_tx: u32,
    reinserted: u32,
    saturated: u32,
}

fn line(
    out: &mut String,
    op: &str,
    a: u32,
    n: u64,
    res: bool,
    len: usize,
    e: Option<LedgerEntry>,
    q: u32,
    qe: Option<LedgerEntry>,
) {
    let _ = writeln!(
        out,
        r#"{{"t":"ledger","op":"{op}","a":{a},"n":{},"res":{res},"len":{len},"e":{},"q":{q},"qe":{}}}"#,
        limbs(n),
        entry_json(e),
        entry_json(qe),
    );
}

/// One run on a fresh ledger: every call is made on the real ledger and on the naive one and compared.
fn run(seed: u64, calls: &[Call], out: &mut String, st: &mut Stats) {
    let mut ledger = Ledger::new(seed);
    let mut naive = Naive {
        v: Vec::new(),
        evicted: HashSet::new(),
        reinserted: 0,
    };
    line(out, "new", 0, 0, false, 0, None, 0, None);
    let mut ids: Vec<u32> = Vec::new();
    for (c, &(op, x, n)) in calls.iter().enumerate() {
        let a = addr(x);
        let (res, want, name, size) = match op {
            Op::Rx => (ledger.on_receive(a, n), naive.on_receive(a, n), "rx", n),
            Op::Open => {
                ledger.open(a);
                naive.open(a);
                (false, false, "open", 0)
            }
            Op::Valid => {
                ledger.validate(a);
                naive.validate(a);
                (false, false, "valid", 0)
            }
            Op::Tx => (ledger.allow_send(a, n), naive.allow_send(a, n), "tx", n),
        };
        assert_eq!(
            res, want,
            "call {c} ({name} {x} {n}): the answer differs from the naive ledger"
        );
        assert_eq!(ledger.len(), naive.v.len(), "call {c}: the length differs");
        assert!(
            ledger.len() <= LEDGER_ENTRIES,
            "call {c}: the table is over its capacity"
        );
        ids.push(x);
        let q = ids[c - c / 2];
        assert_eq!(ledger.get(&a), naive.get(a), "call {c}: the entry of {x} differs");
        assert_eq!(
            ledger.get(&addr(q)),
            naive.get(addr(q)),
            "call {c}: the entry of {q} differs"
        );
        if op == Op::Tx && !res {
            st.held_tx += 1;
        }
        if naive.get(a).is_some_and(|e| e.rx == u64::MAX || e.tx == u64::MAX) {
            st.saturated += 1;
        }
        st.calls += 1;
        line(
            out,
            name,
            x,
            size,
            res,
            ledger.len(),
            ledger.get(&a),
            q,
            ledger.get(&addr(q)),
        );
    }
    st.reinserted += naive.reinserted;
    // an address that is not validated never had more than three times its bytes charged
    for &x in &ids {
        for e in [naive.get(addr(x)), ledger.get(&addr(x))].into_iter().flatten() {
            if !e.validated {
                assert!(
                    u128::from(e.tx) <= 3 * u128::from(e.rx),
                    "address {x} held and over three times its bytes: {e:?}"
                );
            }
        }
    }
}

fn rx(x: u32, n: u64) -> Call {
    (Op::Rx, x, n)
}
fn tx(x: u32, n: u64) -> Call {
    (Op::Tx, x, n)
}
fn open(x: u32) -> Call {
    (Op::Open, x, 0)
}
fn valid(x: u32) -> Call {
    (Op::Valid, x, 0)
}

/// 1: fill and evict.
fn fill_and_evict() -> Vec<Call> {
    let mut v: Vec<Call> = (1..=1030).map(|x| tx(x, 100)).collect();
    v.extend((1..=6).map(|x| rx(x, 50)));
    v.extend([rx(13, 50), rx(14, 50), tx(1, 151), tx(1, 122)]);
    v
}

/// 2 to 5: held then validated, never sent then received, dial after a receive, zero sizes.
fn held_and_validated() -> Vec<Call> {
    vec![
        rx(1, 1200),
        tx(1, 1172),
        tx(1, 2372),
        tx(1, 0),
        rx(1, 1),
        tx(1, 100_000),
        valid(1),
        tx(1, 100_000),
        valid(9),
        tx(9, 100),
        rx(2, 10),
        rx(2, 10),
        tx(2, 32),
        tx(2, 1),
        rx(3, 5),
        open(3),
        tx(3, 5000),
        open(4),
        tx(4, 1),
        rx(5, 0),
        tx(5, 0),
        tx(6, 0),
    ]
}

/// 6: saturation, and the end of the counter of an entry not validated.
fn saturation() -> Vec<Call> {
    let m = u64::MAX;
    vec![
        rx(7, m),
        rx(7, m),
        tx(7, m - 27),
        tx(7, m),
        tx(7, m),
        rx(7, 1),
        tx(7, m),
        tx(8, m),
        rx(9, m / 3 + 1),
        tx(9, m - 28),
        tx(9, 0),
        // the counter's end: a charge that would pass it is held, one that reaches it exactly is charged
        rx(10, m),
        tx(10, m - 56),
        tx(10, 0),
        tx(10, 0),
        rx(11, m),
        tx(11, m - 38),
        tx(11, 0),
    ]
}

/// 7: a seeded run of 180 calls over `ids` addresses.
fn seeded(seed: u64, ids: u64) -> Vec<Call> {
    const EDGE: [u64; 7] = [0, 1, 27, 28, 29, u64::MAX - 28, u64::MAX];
    let mut rng = SplitMix64::traced(seed);
    (0..180)
        .map(|_| {
            let op = match rng.next_u64() % 100 {
                0..40 => Op::Rx,
                40..78 => Op::Tx,
                78..88 => Op::Open,
                _ => Op::Valid,
            };
            let x = 1 + (rng.next_u64() % ids) as u32;
            let n = if rng.next_u64().is_multiple_of(16) {
                EDGE[(rng.next_u64() % 7) as usize]
            } else {
                rng.next_u64() % 1501
            };
            (op, x, n)
        })
        .collect()
}

#[test]
fn trace_ledger() {
    let mut out = String::new();
    let mut st = Stats::default();
    run(0x6c65_6467_6572_0101, &fill_and_evict(), &mut out, &mut st);
    run(0x6c65_6467_6572_0102, &held_and_validated(), &mut out, &mut st);
    run(0x6c65_6467_6572_0103, &saturation(), &mut out, &mut st);
    for k in 0..16u64 {
        let seed = 0x6c65_6467_6572_0001 + k;
        run(seed, &seeded(seed, if k < 12 { 40 } else { 1100 }), &mut out, &mut st);
    }
    assert!(st.calls <= 4500, "the trace grew to {} calls", st.calls);
    assert!(
        st.held_tx > 0 && st.reinserted > 0 && st.saturated > 0,
        "held sends {} evicted then re-inserted {} saturated {}",
        st.held_tx,
        st.reinserted,
        st.saturated
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("ledger.ndjson"), &out).unwrap();
    }
}
