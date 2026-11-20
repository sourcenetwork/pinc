//! Trace generation for path validation and migration: seeded and fixed runs of the dialing side of real established
//! sessions (`pinc-transport`, built with the `trace` and `inject` features), recorded as ndjson (`path_move.ndjson`)
//! for the TLA+ trace check (`TracePathMove.tla`).
//!
//! The test drives the connection `a` through its host calls (`add_path`, `rebind_path`, `remove_path`, `path_lost`,
//! `set_active`, `set_path_info`, `probe`, `punch_known`, `path_returned`), through packets handed to it on any path
//! (`inject_payload`: answers to its real challenges, to replaced ones, forged ones, on the wrong path and after a
//! rebind, challenges, and data with and without WAKE, the highest numbered or older), through its built datagrams
//! (thrown away) and through its timers (the 15 s silence and one nanosecond past it, probes due, the third probe
//! timeout in a row and later ones, thin and not). Paths added as relayed run through a node that carries the relay
//! role. After the session is established the peer is never driven again. Every call is recorded with the path table
//! before and after it (`Connection::trace_paths`), challenge bytes numbered in the order they are first seen.
//!
//! The test asserts by itself that no path id is held twice, that the active slot holds a path, that a forged answer
//! validates nothing, and the checks of each fixed run; the model reads the rest. The trace is written to
//! `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::similar_names,
    unreachable_pub,
    clippy::redundant_closure_for_method_calls,
    clippy::unused_self
)]

#[path = "trace_path_move/common.rs"]
mod common;
#[path = "trace_path_move/runs.rs"]
mod runs;

use common::PmTrace;
use pinc_tests::*;
use runs::{fixed_runs, random_runs};

#[test]
fn path_moves_match_the_model() {
    big_stack(|| {
        let mut tr = PmTrace::default();
        fixed_runs(&mut tr);
        random_runs(&mut tr);
        for op in [
            "init", "add", "rebind", "remove", "lost", "set", "info", "probe", "punch", "returned", "resp", "chal",
            "data", "send", "timer",
        ] {
            assert!(tr.seen.contains(op), "no `{op}` event was recorded");
        }
        for r in [
            "ok",
            "toomany",
            "unknown",
            "exists",
            "active",
            "notvalidated",
            "nopath",
            "true",
            "false",
        ] {
            assert!(tr.seen.contains(&format!("r:{r}")), "no event had the result `{r}`");
        }
        for s in ["pto3", "pto4", "thin", "nonthin"] {
            assert!(tr.seen.contains(s), "no timer event of kind `{s}`");
        }
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("path_move.ndjson"), &tr.out).unwrap();
        }
    });
}
