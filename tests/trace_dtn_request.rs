//! Trace generation for whole DTN transfers from one holder whose copy is corrupt in some symbols: the destination's
//! DTN trace events of each transfer, recorded as ndjson (`dtn_request.ndjson`) for the TLA+ trace check
//! (`TraceDtnRequest.tla`).
//!
//! The bundle has two blocks of two data symbols and one parity symbol (`k = 2`, `m = 1`, 4 KiB slices). The source's
//! copy is corrupted before the contact in no symbol (`none`), in symbols 1 and 3 (`one`: each block loses one symbol
//! and parity takes its place), in symbols 3 and 5 (`two`: block 1 loses `m + 1` symbols and is stuck) and in every
//! symbol (`allbad`). Each case runs with three seeds, which only change the network timing.
//!
//! The test asserts, without the model: `none` and `one` complete with the payload intact and `none` traces no lost
//! symbol and no parity; `two` and `allbad` trace at least two refusals, all with reason 4, and no completion;
//! `allbad` loses exactly 2 symbols of block 0 per offer. The trace is written to the directory in `PINC_TRACE_DIR`
//! when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod layers_common;

use std::fmt::Write as _;

use layers_common::{LWorld, big, secs};
use pinc_node::dtn_want_probe::want;
use pinc_node::{Body, DtnPlan, Enabled, NodeEvent, NodeTrace};
use pinc_sim::NodeId as SimId;
use pinc_tests::{LayerApps, NCmd, SplitMix64};

const SLICE: usize = 4096;
/// The bad-proof refusal code on the wire.
const BAD_PROOF: u64 = 4;

/// The payload length that makes two blocks of two data symbols and one parity symbol at 4 KiB slices.
fn payload_len() -> usize {
    let mut len = 4 * SLICE;
    loop {
        if let Some(p) = want(2, 1, 2, len as u64, 0, &[], &[])
            && p.blocks == 2
            && p.shape == [(2, 3), (2, 3)]
        {
            assert_eq!(p.max, 16);
            return len;
        }
        assert!(
            len > 16,
            "no payload length makes two blocks of two data symbols and one parity"
        );
        len -= 16;
    }
}

fn world(seed: u64, len: usize) -> (LWorld, SimId, SimId, Vec<u8>) {
    let mut w = LWorld::build_with(seed, 1, 2, 0, true, |tag| {
        let mut apps = LayerApps::new(
            tag,
            Enabled {
                dtn: true,
                ..Enabled::NONE
            },
        );
        apps.dtn.policy.max_sends = 60;
        apps
    });
    let (src, dst) = (w.members[0], w.members[1]);
    let dst_id = w.id(dst);
    w.apps(src).dtn.windows = Some(vec![(dst_id, 6_000, 300_000)]);
    let keys = w.apps(dst).dtn.keys();
    let mut payload = vec![0u8; len];
    SplitMix64::new(seed).fill(&mut payload);
    w.sim.command(
        secs(2),
        src,
        NCmd::DtnSend {
            to: Box::new(keys),
            payload: payload.clone(),
            plan: DtnPlan {
                lifetime_ms: 300_000,
                copies: 2,
                k: 2,
                m: 1,
                slice_log: 2,
            },
        },
    );
    w.run(secs(4));
    (w, src, dst, payload)
}

/// Flip a byte of each of `symbols` in the source's copy.
fn corrupt(w: &mut LWorld, src: SimId, symbols: &[u64]) {
    let bundles = &mut w.apps(src).dtn.bundles;
    assert_eq!(bundles.len(), 1, "the source holds the one bundle");
    let (sealed, _) = bundles.values_mut().next().unwrap();
    let total = sealed.len();
    assert!(total > 3 * SLICE, "the copy is {total} bytes, not over three slices");
    for s in symbols.iter().filter(|s| (**s as usize) * SLICE < total) {
        sealed[*s as usize * SLICE] ^= 0x01;
    }
}

fn received(w: &LWorld, dst: SimId) -> Vec<Vec<u8>> {
    w.node_events(dst)
        .into_iter()
        .filter_map(|(_, e)| match e {
            NodeEvent::DtnReceived { payload, .. } => Some(payload),
            _ => None,
        })
        .collect()
}

fn run_case(out: &mut String, case: &'static str, seed: u64, len: usize) {
    let (mut w, src, dst, payload) = world(seed, len);
    let bad: Vec<u64> = match case {
        "none" => vec![],
        "one" => vec![1, 3],
        "two" => vec![3, 5],
        _ => (0..64).collect(),
    };
    corrupt(&mut w, src, &bad);
    w.run(secs(300));

    writeln!(out, r#"{{"t":"case","case":"{case}","k":2,"m":1,"blocks":2,"max":16}}"#).unwrap();
    let (mut refused, mut complete, mut lost, mut parity) = (0, false, 0, 0);
    let mut offer_lost: Vec<Vec<u64>> = vec![Vec::new()];
    for (_, item) in &w.sim.node(dst).traces {
        let Body::Node(t) = &item.body else { continue };
        match *t {
            NodeTrace::DtnSymbols { first, .. } => writeln!(out, r#"{{"t":"sym","first":{first}}}"#).unwrap(),
            NodeTrace::DtnLost { symbol, .. } => {
                lost += 1;
                offer_lost.last_mut().unwrap().push(symbol);
                writeln!(out, r#"{{"t":"lost","symbol":{symbol}}}"#).unwrap();
            }
            NodeTrace::DtnParity { symbols, .. } => {
                parity += 1;
                writeln!(out, r#"{{"t":"parity","n":{symbols}}}"#).unwrap();
            }
            NodeTrace::DtnRefused { reason, .. } => {
                refused += 1;
                assert_eq!(reason, BAD_PROOF, "{case}: a refusal for another reason");
                offer_lost.push(Vec::new());
                writeln!(out, r#"{{"t":"refused","reason":{reason}}}"#).unwrap();
            }
            NodeTrace::DtnComplete { .. } => {
                complete = true;
                writeln!(out, r#"{{"t":"complete"}}"#).unwrap();
            }
            _ => continue,
        }
        if complete || refused == 3 {
            break;
        }
    }
    match case {
        "none" | "one" => {
            assert!(complete, "{case}: the transfer did not complete");
            assert_eq!(received(&w, dst), vec![payload], "{case}: the payload is not intact");
            if case == "none" {
                assert_eq!(
                    (lost, parity),
                    (0, 0),
                    "an honest holder lost symbols or asked for parity"
                );
            }
        }
        _ => {
            assert!(refused >= 2, "{case}: {refused} refusals");
            assert!(!complete, "{case}: a corrupt holder completed");
            if case == "allbad" {
                for o in offer_lost.iter().filter(|o| !o.is_empty()).take(refused) {
                    assert_eq!(o, &[0, 1], "allbad: an offer loses 2 symbols of block 0, one per ask");
                }
            }
        }
    }
}

#[test]
fn dtn_request_traces() {
    let out = big(|| {
        let len = payload_len();
        let mut out = String::new();
        for case in ["none", "one", "two", "allbad"] {
            for seed in 1..=3u64 {
                run_case(&mut out, case, seed, len);
            }
        }
        out
    });
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("dtn_request.ndjson"), out).unwrap();
    }
}
