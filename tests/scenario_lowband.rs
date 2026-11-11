//! Scenario target covering S6. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(
    ["S6"],
    "S6 seed 86017 fails G-INT, G-ORDER and G-LIVE: the handshake of a 2G node with one hub stalls for 30 s on a thin link and a fetch never completes"
);
