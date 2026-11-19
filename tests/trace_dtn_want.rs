//! Trace generation for the request rule of a receiving transfer (`Dtn::want`) over every state of a small bundle,
//! recorded as ndjson (`dtn_want.ndjson`) for the TLA+ trace check (`TraceDtnWant.tla`).
//!
//! The bundle has two blocks of two data symbols and one parity symbol (`k = 2`, `m = 1`, 16 KiB slices, so a request
//! takes at most 4 symbols). Each of its 6 symbols is, for the receiver, neither held nor lost from this holder, held,
//! lost, or both: 4096 states, each asked at every cursor the receiver can hold in it.
//!
//! The test asserts, without the model: the answer does not depend on the cursor; an ask never holds a symbol that is
//! held or lost, never runs past 4 symbols, and takes the parity of a block only when a data symbol of that block is
//! lost and not held; the answer is `decodable` exactly when both blocks hold 2 symbols. The trace is written to the
//! directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]

use std::fmt::Write as _;

use pinc_node::dtn_want_probe::{Answer, Probe, want};

const K: u8 = 2;
const M: u8 = 1;
const SLICE_LOG: u8 = 4;
const SYMBOLS: u64 = 6;

fn list(v: &[u64]) -> String {
    format!("[{}]", v.iter().map(u64::to_string).collect::<Vec<_>>().join(","))
}

/// The payload length that makes two blocks of `(2, 3)`.
fn payload_len() -> u64 {
    let mut len = 4 * 16384u64;
    loop {
        if let Some(p) = want(K, M, SLICE_LOG, len, 0, &[], &[])
            && p.blocks == 2
            && p.shape == [(2, 3), (2, 3)]
        {
            assert_eq!(p.max, 4);
            return len;
        }
        assert!(
            len > 16,
            "no payload length makes two blocks of two data symbols and one parity"
        );
        len -= 16;
    }
}

#[test]
fn dtn_want_traces() {
    let len = payload_len();
    let mut out = String::new();
    for state in 0..4u64.pow(SYMBOLS as u32) {
        let digit = |s: u64| (state >> (2 * s)) & 3;
        let held: Vec<u64> = (0..SYMBOLS).filter(|s| digit(*s) & 1 != 0).collect();
        let lost: Vec<u64> = (0..SYMBOLS).filter(|s| digit(*s) & 2 != 0).collect();
        let per = |b: u64| held.iter().filter(|s| **s / 3 == b).count();
        let first_short = (0..2).find(|b| per(*b) < 2).unwrap_or(2);
        let mut answers: Vec<Probe> = Vec::new();
        for cursor in 0..=first_short {
            answers.push(want(K, M, SLICE_LOG, len, cursor, &held, &lost).unwrap());
        }
        assert!(
            answers.windows(2).all(|p| p[0] == p[1]),
            "the answer depends on the cursor: {held:?} {lost:?}"
        );
        let p = &answers[0];
        let (kind, a, e) = match p.answer {
            Answer::Ask(a, e) => ("ask", a, e),
            Answer::Decodable => ("decodable", 0, 0),
            Answer::Stuck => ("stuck", 0, 0),
        };
        assert_eq!(
            kind == "decodable",
            per(0) >= 2 && per(1) >= 2,
            "decodable out of step: {held:?} {lost:?}"
        );
        if kind == "ask" {
            assert!(e - a <= 4, "a run of {} symbols: {held:?} {lost:?}", e - a);
            for s in a..e {
                assert!(
                    !held.contains(&s) && !lost.contains(&s),
                    "asked for {s}: {held:?} {lost:?}"
                );
                if s % 3 == 2 {
                    assert!(
                        ((s - 2)..s).any(|d| lost.contains(&d) && !held.contains(&d)),
                        "parity {s} asked with no data symbol lost: {held:?} {lost:?}"
                    );
                }
            }
        }
        // One event for each cursor the receiver can hold in this state; the model has no cursor.
        for _ in &answers {
            writeln!(
                out,
                r#"{{"t":"want","k":{K},"m":{M},"blocks":{},"max":{},"have":{},"lost":{},"kind":"{kind}","a":{a},"e":{e}}}"#,
                p.blocks,
                p.max,
                list(&held),
                list(&lost)
            )
            .unwrap();
        }
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("dtn_want.ndjson"), out).unwrap();
    }
}
