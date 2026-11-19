//! The application and the harness protocols.
//!
//! [`Stack`] is the application of one node together with the four harness protocols (PUSHLOG, DOCSYNC, MANAGE,
//! ECHO), written only against the [`host`] contract: it turns scenario intents into work, frames real bytes on
//! streams, and records every intent and delivery in the shared recorder. The layers above the endpoint that are
//! not harness-owned (broadcast, values, reconcile) plug in through [`ontop::OnTop`]. [`durable::Durable`] is the
//! database state that survives a restart.
//!
//! Invariants: message bodies are the registry's real bytes, framed as `[type:1][len:4][id:8]` + body and read back
//! from arbitrary pieces with bounded buffers; the creator of every body is decoded from its first block and checked
//! against the session peer; all times are the node's local time.

mod app;
pub mod body;
pub mod durable;
mod echo;
pub mod frame;
pub mod host;
pub mod ontop;
mod pushlog;
mod reqresp;
mod stack;

pub use app::stall_fraction;
pub use durable::{Durable, MsgIntents};
pub use ontop::{Command, OnTop, OnTopEvent, ValueIds};
pub use stack::{ALPN_DOCSYNC, ALPN_ECHO, ALPN_MANAGE, ALPN_PUSHLOG, Stack};
