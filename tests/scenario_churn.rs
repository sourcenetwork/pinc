//! Scenario target covering S13. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(
    ["S13"],
    "S13 seed 81313 fails G-AWARE: a view still lists departed members; the carriers of a cut-off side are reset by the library later and one hub at a time, where the reference resets all of them within seconds and its hubs confirm the members down together"
);
