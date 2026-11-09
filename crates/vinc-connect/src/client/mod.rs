//! The client side of connectivity: every rule a node follows to reach its relays and its peers.
//!
//! Each module is a small pure state machine or decision function that takes time and observations as arguments and
//! returns what to do, so each rule is testable at its boundary numbers:
//! - [`link`]: one relay carrier (dial, retry, watchdog, keepalive, lease);
//! - [`netcheck`]: address discovery, the home relay and the reachability class;
//! - [`lookup`]: the lookup client and the verification of a record;
//! - [`dial`]: pending dials (DIAL_PRUNE) and the first-flight rules;
//! - [`tunnel`]: the member side of the hub tunnel, SPLICE_LIVE and THIN_SPLICE;
//! - [`punch`]: REACH_OUT and the punch timer.

#![allow(clippy::doc_markdown, reason = "rule names are written as the rules call them")]

mod carriers;
pub mod conn;
pub mod dial;
mod drive;
pub mod link;
pub mod lookup;
pub mod netcheck;
pub mod punch;
mod timers;
pub mod tunnel;

pub use conn::{Config, Connectivity, Io, Kind, Notice, RelayCfg};
