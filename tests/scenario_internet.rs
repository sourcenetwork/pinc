//! Scenario target covering S2, S5, S15. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(["S2", "S5", "S15"]);
