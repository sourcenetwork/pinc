//! Scenario target covering S6. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(
    ["S6"],
    "S6 seed 86017 fails G-INT and G-LIVE: a fetch and two echoes of nodes on a 2G link finish late once a session dialed to a hub acknowledges every 4th packet; with every 2nd it passes every gate"
);
