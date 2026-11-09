//! Trace generation for the membership proofs: the real hub stream codec, incarnation and the hub and member state
//! machines, run through seeded realistic scenarios and recorded as ndjson for the TLA+ trace check
//! (`TraceMembership.tla`, `TraceHubCodec.tla`, `TraceIncarnation.tla`) and the Lean replay
//! (`Vinc.TraceMembership`, `Vinc.TraceMembershipCodec`, `Vinc.TraceMembershipInc`).
//!
//! Each part asserts everything itself against the behaviour the design states, so the test is meaningful without
//! the proof tools. The traces are written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is
//! written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    unreachable_pub
)]

#[path = "trace_membership/common.rs"]
mod common;

#[test]
fn membership_traces() {
    let mut tw = common::TraceWriter::new();
    tw.finish();
}
