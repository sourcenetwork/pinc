//! Trace generation for the transcripts: what every `Transcript` of the workspace absorbs, in order, recorded as
//! ndjson (`transcript.ndjson`) for the TLA+ trace check (`TraceTranscript.tla`) and the Lean replay
//! (`Vinc.TraceTranscript`).
//!
//! With the `trace` feature of `vinc-crypto` armed on the thread, every `snapshot` of a transcript is one `tr` line:
//! the transcript's label and, for each field absorbed so far, the tag the call site gave it and its length, in
//! absorption order. The checkers hold the field list of every kind of transcript (the handshake, the resumption,
//! the ticket context, the sub-session context, the key roll id, the prekey hash, the chain, and the delay-tolerant
//! delivery transcripts) and require each line to be a prefix of the list of its label, field by field, and each
//! kind to be seen in full. The kinds are driven through the public API: full, short and resumed handshakes with
//! the Ed25519 and the hybrid identities, `sub_session_secret`, `request_id`, `prekey_hash`, and a sealed bundle
//! with its head, its identifier and a custody ack. The record layer and the credit record absorb nothing into a
//! transcript. A line is written once however often it repeats.
//!
//! Every kind is asserted here against the field list, so the test is meaningful without the proof tools. The trace
//! is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod dtn_common;
mod sec_common;

use std::collections::HashSet;
use std::fmt::Write as _;

use vinc_crypto::transcript::trace;
use vinc_crypto::{IdentityAlg, Secret};
use vinc_dtn::custody::CustodyAck;
use vinc_dtn::hlc::Hlc;
use vinc_security::keyroll::request_id;
use vinc_security::{prekey_hash, sub_session_secret};

use sec_common::{ALPN, World, big_stack};

/// Drive every kind of transcript of the workspace once or more.
fn drive() {
    for alg in [IdentityAlg::Ed25519, IdentityAlg::Hybrid] {
        let mut w = World::new(alg, alg, false, false);
        w.full();
        // the short Initial, then a resumption against the ticket the full handshake left
        let dial = w.dial();
        let mut i = w.initiator_with(dial, ALPN, true, false);
        let mut r = w.responder();
        assert!(w.run(&mut i, &mut r, None).both_established());
        let mut i = w.initiator_with(dial, ALPN, false, true);
        let mut r = w.responder();
        let out = w.run(&mut i, &mut r, None);
        assert!(out.both_established() && out.i_est().unwrap().resumed);
    }
    let parent = Secret::new([5u8; 32]);
    let _ = sub_session_secret(&parent, ALPN, b"client", b"server");
    let _ = request_id(&[7u8; 32]);
    let _ = prekey_hash(&[9u8; 1184]);
    for (i, alg) in dtn_common::ALGS.into_iter().enumerate() {
        let sender = dtn_common::keypair(alg, 100 + i as u64);
        let to = dtn_common::recipient(IdentityAlg::Ed25519, 200, 1);
        let s = dtn_common::make(
            &sender,
            &to,
            dtn_common::plan(3, 2, 0),
            &dtn_common::bytes(7, 5_000),
            300,
        );
        let ack = CustodyAck::sign(s.signed.head().id, to.id.node_id(), 1, Hlc::new(2_000, 0), &sender).unwrap();
        ack.verify().unwrap();
    }
}

/// The distinct snapshots recorded, in order of first appearance, as `tr` lines.
fn lines(records: Vec<trace::Record>) -> String {
    let mut seen = HashSet::new();
    let mut out = String::new();
    for r in records {
        if !seen.insert(r.clone()) {
            continue;
        }
        let fields = r
            .fields
            .iter()
            .map(|(tag, len)| format!("[\"{tag}\",{len}]"))
            .collect::<Vec<_>>()
            .join(",");
        let _ = writeln!(out, r#"{{"t":"tr","label":"{}","fields":[{fields}]}}"#, r.label);
    }
    out
}

#[test]
fn transcript_traces() {
    let trace = big_stack(|| {
        trace::arm();
        drive();
        lines(trace::take())
    });
    // every kind was recorded, in its full form
    let labels = [
        "VINC 2026 v1 handshake",
        "VINC 2026 v1 resume handshake",
        "VINC 2026 v1 ticket",
        "VINC 2026 v1 sub session context",
        "VINC 2026 v1 key roll id",
        "VINC 2026 v1 prekey hash",
        "VINC 2026 v1 chain",
        "VINC 2026 v1 dtn transcript",
        "VINC 2026 v1 dtn chain",
        "VINC 2026 v1 dtn bundle id",
        "VINC 2026 v1 dtn head",
        "VINC 2026 v1 dtn custody ack",
    ];
    for l in labels {
        assert!(trace.contains(&format!("\"label\":\"{l}\"")), "no transcript of {l}");
    }
    // a full handshake absorbs 20 fields; a resumption 14
    assert!(trace.contains(r#""label":"VINC 2026 v1 handshake","fields":[["label",22],["version",1],["alpn",6]"#));
    assert!(
        trace
            .lines()
            .any(|l| l.contains("v1 handshake\"") && l.matches("],[").count() == 19)
    );
    assert!(
        trace
            .lines()
            .any(|l| l.contains("resume handshake\"") && l.matches("],[").count() == 13)
    );
    let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
        return;
    };
    std::fs::write(std::path::Path::new(&dir).join("transcript.ndjson"), trace).unwrap();
}
