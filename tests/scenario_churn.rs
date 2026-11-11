//! Scenario target covering S13. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(
    ["S13"],
    "S13 seed 81313 fails G-LIVE: a publish to a late joiner is never repaired; the run takes a different course from the reference's before the repair window is asked"
);
