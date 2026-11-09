//! Grading in the scenario suite: every gate (a pass and a fail), every term on hand-built recordings with known
//! values, the fair rule, the score and its floors, the noise floor against the reference harness's own numbers, the
//! delivery check and the trace hash.
//!
//! The reference vectors in `data/reference_terms.txt` are the per-seed terms of the reference model, four seeds for
//! each of 24 variants, current and fair; the expected numbers asserted below were computed from them by the reference
//! harness itself (`CPython`) and recorded here.
#![allow(
    clippy::indexing_slicing,
    clippy::panic,
    clippy::assert_is_empty,
    clippy::unreadable_literal,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::semicolon_if_nothing_returned,
    clippy::cast_precision_loss,
    clippy::too_many_lines,
    unreachable_pub
)]

#[path = "scenario_grade/common.rs"]
mod common;
#[path = "scenario_grade/gates.rs"]
mod gates;
#[path = "scenario_grade/score.rs"]
mod score;
#[path = "scenario_grade/terms.rs"]
mod terms;
