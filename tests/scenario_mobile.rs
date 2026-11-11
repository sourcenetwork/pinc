//! Scenario target covering S3. See `scenario_support` for the seed selection and the full-run switch.
#![allow(missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

#[macro_use]
mod scenario_support;

scenario_target!(
    ["S3"],
    "S3 seed 31337 fails G-ORDER, G-LIVE, G-AWARE and G-CONNECT: echoes and docsyncs toward nodes that moved never connect, and a few live members are reported suspected"
);
