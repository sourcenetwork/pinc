//! Scenario target covering S2, S5, S6, S15. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(
    ["S2", "S5", "S6", "S15"],
    "S6 seed 86017 fails G-ORDER and G-LIVE: the handshake of a 2G node with one hub stalls for 30 s; S15 seed 81503 fails G-LIVE: the two ends of a session end on different address families, where the reference's do not"
);
