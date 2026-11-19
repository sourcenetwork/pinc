//! Trace generation for the membership proofs: the real hub stream codec, incarnation and the hub and member state
//! machines, run through seeded realistic scenarios and recorded as ndjson for the TLA+ trace check
//! (`TraceMembership.tla`, `TraceHubCodec.tla`, `TraceIncarnation.tla`) and the Lean replay
//! (`Pinc.TraceMembership`, `Pinc.TraceMembershipCodec`, `Pinc.TraceMembershipInc`).
//!
//! Each part asserts everything itself against the behaviour the design states, so the test is meaningful without
//! the proof tools. The traces are written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is
//! written.
#![allow(
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
    clippy::trivially_copy_pass_by_ref,
    clippy::manual_is_multiple_of,
    clippy::single_match_else,
    clippy::match_wildcard_for_single_variants,
    clippy::cast_lossless,
    clippy::doc_markdown,
    clippy::unused_self,
    clippy::redundant_closure_for_method_calls,
    dead_code,
    unreachable_pub
)]

#[path = "trace_membership/codec.rs"]
mod codec;
#[path = "trace_membership/common.rs"]
mod common;
#[path = "trace_membership/inc.rs"]
mod inc;
#[path = "trace_membership/node.rs"]
mod node;
#[path = "trace_membership/node_rec.rs"]
mod node_rec;
#[path = "membership_world.rs"]
mod world;

#[test]
fn membership_traces() {
    let mut tw = common::TraceWriter::new();
    codec::run(&mut tw);
    inc::run(&mut tw);
    node::run(&mut tw);
    tw.finish();
}
