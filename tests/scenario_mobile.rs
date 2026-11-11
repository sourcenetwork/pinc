//! Scenario target covering S3. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(
    ["S3"],
    "S3 seed 31337 fails G-INT, G-ORDER, G-LIVE and G-CONNECT: echoes, docsyncs and fetches toward nodes that moved never connect or complete"
);
