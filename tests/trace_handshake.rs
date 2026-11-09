//! Trace generation for the handshake: real runs of the `Initiator`, the `Responder` and the `ClientTickets` store
//! through the public API, recorded step by step as ndjson for the TLA+ trace check and the Lean replay.
//!
//! A world is one test scenario: one dialing node, three responder nodes (two honest, the third with the attacker's
//! identity; each with its own caches), a client ticket store, a clock, and any number of sessions. Every step of
//! either machine (start, receive a message, answer a key request, send again, shed) and of the stores (hand tickets
//! to the client, time passing, export, restore, restart) is one `hs` line: the input message (type, id, length,
//! and for a tampered input the id of the original and the field that changed), the outcome (`ok`, `drop`,
//! `fatal`), the outputs (messages with the ids of their public values and their lengths, the key request and its
//! transcript hash), the events, and key fingerprint ids at `Established` and `EarlyKeys`. An id stands for one
//! distinct byte string (equal bytes, equal id), so the checkers never see a hash function: they check that the
//! recorded ids relate exactly as the model's symbolic terms do.
//!
//! The tampers flip a bit in the first and the last byte of every field of every message of every flow, and cut and
//! extend every message; a flip of a length byte or of several fields at once is not a tamper of one field and is
//! left out.
//!
//! Every scenario is asserted here, so the test is meaningful without the proof tools. The trace is written to
//! `handshake.ndjson` in the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::assert_is_empty,
    clippy::manual_assert_eq,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    clippy::struct_excessive_bools,
    clippy::fn_params_excessive_bools,
    unreachable_pub
)]

#[path = "trace_hs/scen.rs"]
mod scen;
mod sec_common;
#[path = "trace_hs/sim.rs"]
mod sim;
#[path = "trace_hs/tamper.rs"]
mod tamper;

use scen::{Ctx, scenarios};
use sec_common::big_stack;
use sim::Sim;
use tamper::{Class, Tamper, tamper_cases};

/// The messages of a flow in delivery order, from a dry run, and the setup it needs.
#[derive(Clone, Copy)]
enum Flow {
    Full,
    ShortMiss,
    ShortHit,
    Resume,
    ResumeReject,
}

impl Flow {
    fn run(self, sim: &mut Sim<'_>, tamper: Option<&Tamper>) -> Vec<Vec<u8>> {
        match self {
            Self::Full => {
                let (is, first) = sim.start(1, 1, false, false);
                sim.drive(is, first, tamper, 1, 1)
            }
            Self::ShortMiss => {
                let (is, first) = sim.start(1, 1, true, false);
                sim.drive(is, first, tamper, 1, 1)
            }
            Self::ShortHit => {
                sim.setup_full(1);
                let (is, first) = sim.start(1, 1, true, false);
                sim.drive(is, first, tamper, 1, 1)
            }
            Self::Resume | Self::ResumeReject => {
                sim.setup_full(1);
                let (is, first) = sim.start(1, 1, false, true);
                sim.drive(is, first, tamper, 1, if matches!(self, Self::Resume) { 1 } else { 2 })
            }
        }
    }
}

/// Every message delivered by a flow, in order.
fn flow_messages(flow: Flow) -> Vec<Vec<u8>> {
    let mut ids = sim::Ids::default();
    let mut sim = Sim::new(&mut ids, 0, false);
    flow.run(&mut sim, None)
}

/// Tampered and cut messages in each flow.
fn tampers(c: &mut Ctx) {
    for flow in [
        Flow::Full,
        Flow::ShortMiss,
        Flow::ShortHit,
        Flow::Resume,
        Flow::ResumeReject,
    ] {
        let msgs = flow_messages(flow);
        for (k, msg) in msgs.iter().enumerate() {
            for (bytes, class) in tamper_cases(msg) {
                let tamper = (k, bytes, class);
                c.wid += 1;
                let mut sim = Sim::new(&mut c.ids, c.wid, false);
                flow.run(&mut sim, Some(&tamper));
                let (ty, last_i) = (msg[0], sim.inits.len());
                if let Class::Field(f) = tamper.2 {
                    let i_est = sim.ests.contains_key(&('I', last_i));
                    match (ty, f) {
                        (4 | 7, "sealed" | "conf" | "tids" | "sc" | "e" | "ct") => assert!(!i_est, "{ty} {f}"),
                        (5, "sealed") => assert!(!sim.ests.contains_key(&('R', sim.resps.len()))),
                        (6, "binder" | "tid" | "e") => {
                            assert!(sim.ests.iter().filter(|(k, _)| k.0 == 'R').all(|(_, e)| !e.resumed));
                        }
                        _ => {}
                    }
                }
                sim.finish(&mut c.trace);
            }
        }
    }
}

#[test]
fn handshake_traces() {
    big_stack(|| {
        let mut c = Ctx::default();
        scenarios(&mut c);
        tampers(&mut c);
        let (hs, wid) = (c.trace, c.wid);
        let lines = hs.lines().count();
        assert!(lines > 1500, "{lines} handshake events");
        assert!(wid > 100, "{wid} worlds");
        for needle in [
            r#""op":"begin""#,
            r#""op":"start""#,
            r#""op":"recv""#,
            r#""op":"key""#,
            r#""op":"retx""#,
            r#""op":"shed""#,
            r#""op":"accept""#,
            r#""op":"expire""#,
            r#""op":"export""#,
            r#""op":"restore""#,
            r#""op":"restart""#,
            r#""scope":"srv""#,
            r#""scope":"cli""#,
            r#""ok":false"#,
            r#""ia":true"#,
            r#""mode":"resume""#,
            r#""mode":"short""#,
            r#""peer":"A""#,
            r#""evs":["early","est"]"#,
            r#""evs":["rejected"]"#,
            r#""res":"fatal""#,
            r#""imal":true"#,
            r#""ifld":"binder""#,
            r#""ifld":"sealed""#,
            r#""ifld":"of""#,
            r#""ifld":"dc""#,
            r#""ifld":"cr""#,
            r#""ifld":"conf""#,
            r#""kind":"fail""#,
            r#""alpn":2"#,
        ] {
            assert!(hs.contains(needle), "the runs never produce {needle}");
        }
        let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
            return;
        };
        let dir = std::path::PathBuf::from(dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("handshake.ndjson"), hs).unwrap();
    });
}
