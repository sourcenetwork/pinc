//! The client side of connectivity: every rule a node follows to reach its relays and its peers.
//!
//! Each module is a small pure state machine or decision function that takes time and observations as arguments and
//! returns what to do, so each rule is testable at its boundary numbers:
//! - [`link`]: one relay carrier (dial, retry, watchdog, keepalive, lease);
//! - [`netcheck`]: address discovery, the home relay and the reachability class;
//! - [`lookup`]: the lookup client and the verification of a record;
//! - [`dial`]: pending dials (DIAL_PRUNE) and the first-flight rules;
//! - `flight`: the candidate paths of a dial's flights, the dial and the answer of a lookup;
//! - [`tunnel`]: the member side of the hub tunnel, SPLICE_LIVE and THIN_SPLICE;
//! - [`punch`]: REACH_OUT and the punch timer;
//! - [`queue`]: the packets a closed carrier holds.

#![allow(
    clippy::large_stack_arrays,
    clippy::needless_pass_by_value,
    clippy::unused_self,
    clippy::wrong_self_convention,
    clippy::match_same_arms,
    reason = "the machines hold their buffers inline by design; the host boxes them"
)]
#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::too_many_lines,
    reason = "rule names are written as the rules call them; the machines read well in small scopes"
)]

mod carriers;
pub mod conn;
pub mod dial;
mod drive;
mod flight;
pub mod link;
pub mod lookup;
mod mapped;
pub mod netcheck;
pub mod punch;
pub mod queue;
mod signing;
mod timers;
pub mod tunnel;

pub use conn::{Config, Connectivity, Io, Kind, Notice, RelayCfg};
pub use drive::Port;
#[cfg(feature = "trace")]
pub use flight::FlightProbe;
#[cfg(feature = "trace")]
pub use timers::PublishProbe;
