//! Trace generation for the endpoint's half-open cap and the lifetime of an unauthenticated session: seeded runs of a
//! real endpoint (`vinc-core`, built with the `trace` feature), recorded as ndjson (`halfopen.ndjson`) for the TLA+
//! trace check (`TraceHalfOpen.tla`) and the Lean replay (`Vinc/TraceHalfOpen.lean`).
//!
//! The runs feed the endpoint first flights of every message type at, below and above the size floors, garbage, later
//! parts and datagrams too long to be read; fill the half-open table to its cap with forgeries that arrive at staggered
//! times and keep offering more; dial it for real (a full handshake, then a resumption while the table is full, then
//! replays of the used Hello); close a half-open session; leave it with no protocol registered and with a full slot
//! table; stall it by leaving events unread; and step the clock to just before, onto and past the end of each
//! session's 30 s, and back. One line is written per call of the endpoint that decided something or changed the
//! bookkeeping, and for every datagram and timer call: the inputs the decision used (the message type and length the
//! test reads off the datagram, how many sessions held its id, whether the event queue was stalled), the decisions the
//! endpoint recorded in its own trace ring during the call (admissions, sessions made, established, expired and freed)
//! and the slots whose bookkeeping changed, read through the `trace` view `half_open_slot`, with the count, the stall
//! and `poll_timeout` after the call.
//!
//! The host's clock ticks in milliseconds, so every time of a call and every creation time is a whole millisecond:
//! `halfopen.ndjson` writes times in milliseconds (a deadline rounded up, which keeps every comparison of a deadline
//! with a creation time, an end of life or a call exact), so TLC reads every number; `halfopen_ns.ndjson`, read by the
//! Lean replay only, has the same lines in nanoseconds.
//!
//! The test compares every call with a naive reading of the rules: the count is the number of counted sessions and at
//! most 256, a counted session is unauthenticated, an unauthenticated session's deadline is at most 30 s after its
//! creation and `poll_timeout` is the earliest deadline (none while stalled), a timer call leaves no session past its
//! 30 s, an admission is `len >= floor && (resume || count < 256)`, a refused first flight changes no slot and counts
//! one dropped (or stalled) datagram, and a session leaves the count only by being established or freed.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::large_stack_arrays,
    clippy::too_many_arguments,
    clippy::struct_excessive_bools,
    clippy::panic,
    unreachable_pub
)]

#[path = "trace_halfopen/common.rs"]
mod common;
#[path = "trace_halfopen/duo.rs"]
mod duo;
#[path = "trace_halfopen/rec.rs"]
mod rec;
#[path = "trace_halfopen/runs.rs"]
mod runs;

use rec::{Seen, add};
use runs::{big_run, room_run, small_run};
use vinc_tests::*;

#[test]
fn the_half_open_cap_matches_the_models() {
    let (ms, ns, seen) = big_stack(|| {
        let (mut ms, mut ns, mut seen) = (String::new(), String::new(), Seen::default());
        for (run, seed) in [(1u32, 0x686f_0001u64), (2, 0x686f_0002)] {
            let (a, b, s) = big_run(run, seed);
            ms.push_str(&a);
            ns.push_str(&b);
            add(&mut seen, &s);
        }
        for run in 5..9u32 {
            let (a, b, s) = room_run(run, 0x686f_0200 + u64::from(run));
            ms.push_str(&a);
            ns.push_str(&b);
            add(&mut seen, &s);
        }
        for run in 10..50u32 {
            let (a, b, s) = small_run(run, 0x686f_0100 + u64::from(run));
            ms.push_str(&a);
            ns.push_str(&b);
            add(&mut seen, &s);
        }
        (ms, ns, seen)
    });
    eprintln!("{seen:?}");
    assert!(
        seen.refused_floor > 0 && seen.admitted_at_floor > 0,
        "the floors were not met at their edges"
    );
    assert!(
        seen.cap_reached > 0 && seen.refused_cap > 0,
        "the cap was not reached and pressed"
    );
    assert!(seen.resume_at_cap > 0, "no resumption was admitted at the cap");
    assert!(
        seen.rejected > 0,
        "no forged or replayed first packet was answered without a session"
    );
    assert!(
        seen.refused_half > 0,
        "no first flight was refused at half a room smaller than twice the cap"
    );
    assert!(
        seen.accept_failed > 0,
        "no admitted first flight failed to make a session"
    );
    assert!(seen.stalled > 0 && seen.stalled_timer > 0, "the queue never stalled");
    assert!(seen.not_first > 0);
    assert!(
        seen.expired > 0 && seen.expired_at_end > 0,
        "no session expired at its end"
    );
    assert!(seen.spared_at_limit > 0, "no timer ran at a session's limit itself");
    assert!(
        seen.left_by_est > 0 && seen.left_uncounted_by_est > 0,
        "no session was established"
    );
    assert!(
        seen.left_by_free > 0,
        "no counted session was freed other than by its end"
    );
    assert!(seen.clock_back > 0, "the clock never stepped back");
    assert!(
        seen.second_holder > 0,
        "no first message got a session beside a damaged one"
    );
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("halfopen.ndjson"), &ms).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("halfopen_ns.ndjson"), &ns).unwrap();
    }
}
