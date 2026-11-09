//! VINC values: verified streaming of values of any size from one or many providers.
//!
//! A value is named by its BLAKE3 root and cut into 16 KiB groups. A requester asks providers for byte ranges
//! ([`wire::Req`]); a provider answers with GROUP frames whose proofs let every group be checked against the root as it
//! arrives, so only verified bytes reach the store. This crate holds the whole protocol as sans-IO machines over static
//! generic host traits, with no allocation, no `dyn` and no unsafe code:
//!
//! - [`wire`]: the request, the group frame and the two range-proof extension frames, parsed in place.
//! - [`session`]: the abstract connection layer a later step wires to the transport.
//! - [`store`]: the host value store (`ValueRead` to serve, `ValueStore` to fetch).
//! - [`fetch`]: the multi-provider fetcher (stripe, steal, liar eviction, head hold, stall redial, write-through).
//! - [`server`] and [`source`]: the server and the store-reading stream source (GHOST_FLIGHT).
//! - [`verify`]: the incremental group verifier, where the caller keeps the packets.
//! - [`plan`]: the closed-form geometry of a response, shared by both ends.
//! - [`trace`]: the events and the trace records every machine reports.
#![no_std]
#![forbid(unsafe_code)]
#![allow(
    clippy::doc_markdown,
    reason = "the rule names (HEAD_HOLD, LIAR_EVICT) are protocol names, not code"
)]

pub mod fetch;
pub mod knobs;
pub mod plan;
pub mod server;
pub mod session;
pub mod source;
pub mod span;
pub mod store;
pub mod trace;
pub mod verify;
pub mod wire;
