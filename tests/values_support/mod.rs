//! The in-memory multi-provider harness of the value tests.
//!
//! A deterministic discrete-event simulation: one requester running a [`Fetch`] against any number of providers, each
//! with a [`Server`] over its own store, a link with a rate, a latency, optional loss and reordering, and faults (a
//! lying store, a cut, a silent stall). Time is virtual nanoseconds; the only randomness is a seeded generator, so a run
//! repeats exactly. The harness implements the abstract session traits of `pinc-values`, holding received stream bytes
//! until the value layer consumes them, exactly as the real session will.
#![allow(
    unused_imports,
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::missing_panics_doc
)]

mod net;
mod slots;
mod stores;

pub use net::*;
pub use slots::slot_runs;
pub use stores::*;
