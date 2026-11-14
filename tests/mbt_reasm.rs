//! Model-based tests of the handshake fragment reassembly: a real `Reassembly` (`vinc-transport`, built with the
//! `trace` feature, as `ReasmProbe`) driven along every edge of the state graph of `proofs/tla/MbtReasm.tla`.
//!
//! TLC enumerates every state the operators of `ReasmOps.tla` reach with the calls of that module at the code's own
//! sizes (8 runs, the largest message) and writes the graph; `scripts/mbt.py` turns it into paths from the empty
//! reassembly that take every edge, which `scripts/proofs.sh` writes to the directory `VINC_MBT_DIR` as
//! `reasm.ndjson`. This test runs each path on a fresh reassembly: after every call the length it returns must be the
//! model's `out`, and the state (`view`: the runs and the message length being assembled) must be the model's. The
//! bytes are not in the model, so the test checks them itself: a fragment carries the bytes of a message of its length
//! (a function of the length and the position), and after every call the buffer inside each run is those bytes, and
//! at a completed message its whole prefix is. It stops at the first difference and names the file, the case, the
//! step and the calls that led there. Without `VINC_MBT_DIR` it checks nothing.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_tests::{Json, MbtCase, mbt_cases};
use vinc_transport::conn::{ReasmProbe, ReasmView};

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

fn index(v: &Json) -> usize {
    usize::try_from(num(v)).unwrap()
}

/// The byte at `pos` of the message of `total` bytes that the fragments of a case cut up.
fn byte(total: usize, pos: usize) -> u8 {
    (pos.wrapping_mul(31).wrapping_add(total.wrapping_mul(7)).wrapping_add(1) & 0xff) as u8
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

/// The model's state `r` against the real one.
fn same(v: &ReasmView, r: &Json, at: &dyn Fn() -> String) {
    let runs: Vec<(usize, usize)> = r
        .get("runs")
        .unwrap()
        .arr()
        .unwrap()
        .iter()
        .map(|p| {
            let p = p.arr().unwrap();
            (index(&p[0]), index(&p[1]))
        })
        .collect();
    assert_eq!(v.runs, runs, "{}: the runs differ", at());
    assert_eq!(
        v.total,
        index(r.get("total").unwrap()),
        "{}: the message length differs",
        at()
    );
}

/// Runs one case on a fresh reassembly; returns the number of calls.
fn run(file: &str, case: &MbtCase, init: &Json) -> usize {
    let mut p = ReasmProbe::new();
    let who = format!("{file} case {}", case.id);
    same(&p.view(), init.get("r").unwrap(), &|| {
        format!("{who}: the empty reassembly")
    });
    for (i, st) in case.steps.iter().enumerate() {
        let at = || format!("{who} after step {i}; calls:{}", calls(case, i));
        let ("CallAdd", [total, off, len, out]) = (st.call.as_str(), st.args.as_slice()) else {
            panic!("{who}: a call the test does not know: {st}");
        };
        let (total, off, len) = (index(total), index(off), index(len));
        let data: Vec<u8> = (off..off + len).map(|pos| byte(total, pos)).collect();
        let got = p.add(total, off, &data);
        let want = match out {
            Json::Int(-1) => None,
            n => Some(index(n)),
        };
        assert_eq!(got, want, "{}: the call returned {got:?}", at());
        if let Some(t) = got {
            // a completed message is, byte for byte, the message that was cut
            assert!(
                (0..t).all(|pos| p.buffer()[pos] == byte(t, pos)),
                "{}: the completed message has bytes that were not sent",
                at()
            );
        }
        let v = p.view();
        same(&v, st.state.get("r").unwrap(), &at);
        for &(s, e) in &v.runs {
            assert!(
                (s..e).all(|pos| p.buffer()[pos] == byte(v.total, pos)),
                "{}: a run holds bytes that were not sent",
                at()
            );
        }
    }
    case.steps.len()
}

#[test]
fn the_reassembly_follows_every_edge_of_the_model() {
    let Some(cases) = mbt_cases("reasm.ndjson") else {
        eprintln!("mbt_reasm: VINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
        return;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let c = head.get("constants").unwrap();
    let k = |n: &str| index(c.get(n).unwrap());
    assert_eq!(
        (k("NR"), k("MX")),
        (ReasmProbe::RUNS, ReasmProbe::MAX_MESSAGE),
        "the model's sizes are not the code's"
    );
    let init = head.get("init").unwrap();
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        steps += run("reasm.ndjson", &case.unwrap(), init);
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert_eq!(
        (n, steps as u64),
        (count("cases"), count("steps")),
        "reasm.ndjson: the file ends early"
    );
    eprintln!(
        "mbt_reasm: {n} cases, {steps} calls, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
}
