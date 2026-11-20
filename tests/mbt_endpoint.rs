//! Model-based tests of the endpoint's use of its tables: a real endpoint (`pinc-core`, built with the `trace` feature)
//! driven along every edge of the state graphs of `proofs/tla/MbtEndpoint.tla`.
//!
//! TLC enumerates the states the calls of the endpoint reach (a forged first flight, a later part of a first message,
//! a timer, a call on a stale session id, strays, dials to the node itself, reading events) within the bounds of a
//! config and writes the graph; `scripts/mbt.py` turns it into paths from the empty endpoint that take every edge,
//! which `scripts/proofs.sh` writes to the directory `PINC_MBT_DIR`: `endpoint.ndjson` from `MbtEndpoint.cfg`,
//! `endpoint_life.ndjson` from `MbtEndpoint_life.cfg` and `endpoint_stall.ndjson` from `MbtEndpoint_stall.cfg`. This
//! test runs each path on a fresh endpoint and, after every call, compares what the model keeps (the sessions with the
//! time, id and source that made them, the held parts, the length of the event queue) with what the endpoint holds,
//! read through the `trace` views, and checks what the model cannot see: the heap deadline, the routing entries and
//! the first id of each session in the table, none of them for a free slot, the counters, the timer, and the refusal of
//! every command on an id that names no live session with nothing changed. It stops at the first difference and names
//! the file, the case, the step and the calls that led there. Without `PINC_MBT_DIR` it checks nothing but the two plain
//! tests below.
//!
//! The model's numbers stand for the code's as `MbtEndpoint.tla` says: model time `t` is `origin + t * MS_NS` (the
//! largest model time is `u64::MAX`), where `origin` is `2 * HALF_OPEN_LIFE` or an odd millisecond past
//! `5 * HALF_OPEN_LIFE`, by case; a model id is an 8-byte destination id and a model source an address; a model part
//! length of 1 is 200 bytes and of 2 is 1501; the model's queue lengths `S - 1` and `S` are the real `2K + 960` and
//! `2K + 961`. The table of connection ids has `D = 10 K` entries, as the endpoint needs.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    unreachable_pub,
    clippy::needless_range_loop
)]

#[path = "mbt_endpoint/common.rs"]
mod common;

use common::{World, expired, plain_map, records, refused, sessions_at, slots, walk};
use pinc_core::HALF_OPEN_LIFE;
use pinc_tests::big_stack;

#[test]
fn the_endpoint_keeps_its_tables_in_step_on_every_edge_of_the_model() {
    // MbtEndpoint.cfg, MbtEndpoint_life.cfg, MbtEndpoint_stall.cfg
    let walked = big_stack(|| {
        [
            walk::<2, 20>("endpoint.ndjson"),
            walk::<2, 20>("endpoint_life.ndjson"),
            walk::<1, 10>("endpoint_stall.ndjson"),
        ]
    });
    if walked == [false; 3] {
        eprintln!("mbt_endpoint: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
    }
}

#[test]
fn a_timer_at_the_largest_time_frees_every_forged_session() {
    big_stack(|| {
        let origin = 2 * HALF_OPEN_LIFE;
        let mut table = slots::<2>();
        let mut w = World::<2, 20>::new(origin, &mut table, plain_map());
        let first = w.flood(origin, 1, 1);
        let second = w.flood(u64::MAX, 2, 2);
        assert_eq!(
            sessions_at(&first, 0).len() + sessions_at(&second, 0).len(),
            2,
            "both floods make a session"
        );
        w.ep.handle_timeout(u64::MAX);
        let ev = records(&mut *w.ep);
        assert_eq!(expired(&ev).len(), 2, "two sessions expire at the largest time: {ev:?}");
        assert!(
            (0..2).all(|i| w.ep.half_open_slot(i).is_none()),
            "a session is still held at the largest time"
        );
        assert_eq!(w.ep.poll_timeout(), None, "a timer is still due with no session held");
    });
}

#[test]
fn a_command_on_a_freed_session_changes_nothing() {
    big_stack(|| {
        let origin = 2 * HALF_OPEN_LIFE;
        let mut table = slots::<1>();
        let mut w = World::<1, 10>::new(origin, &mut table, plain_map());
        let ev = w.flood(origin, 1, 1);
        assert_eq!(sessions_at(&ev, 0).len(), 1, "the flood makes a session");
        let old = w.ep.sessions().next().unwrap();
        let now = origin + HALF_OPEN_LIFE + 1;
        w.ep.handle_timeout(now);
        assert!(w.ep.sessions().next().is_none(), "the session outlived its end");
        records(&mut *w.ep);
        let at = || "a command on a freed session".to_owned();
        refused(&mut w.ep, &[old], now, &at);
        let ev = w.flood(now, 2, 1);
        assert_eq!(sessions_at(&ev, 0).len(), 1, "the second flood makes a session");
        let new = w.ep.sessions().next().unwrap();
        assert_ne!(new, old, "the slot's new session has the old id");
        refused(&mut w.ep, &[old], now, &at);
    });
}
