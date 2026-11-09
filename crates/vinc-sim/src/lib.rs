//! `vinc-sim`: a deterministic network simulator for VINC tests and benches.
//!
//! One event queue orders everything by virtual time (nanoseconds) and then by scheduling order. Nodes implement the
//! static [`Node`] trait and are driven through datagrams, timers and commands; the network between them is built from
//! per-direction [links](LinkConfig), [NATs](NatConfig) and scheduled faults. The same seed and the same scenario
//! calls give a byte-identical run and trace. Std is used freely: this crate is for tests and benches only and is
//! never a dependency of a library crate.
//!
//! Start with [`Sim::new`], add nodes and links, schedule commands and faults, then [`Sim::run_until`].
#![forbid(unsafe_code)]
#![allow(
    // Ids come from the simulator and index its tables; times and sizes are converted between integer widths.
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::cast_lossless
)]

mod adversary;
mod clock;
mod config;
mod faults;
mod ids;
mod link;
mod metrics;
mod nat;
mod net;
mod node;
#[cfg(feature = "reference")]
pub mod reference;
mod rng;
mod sim;
mod stream;
mod tcp;
mod topology;
pub mod toy;
pub mod toy_stream;

pub use adversary::{FloodPayload, FloodSpec, ObsRecord, Observer};
pub use clock::Clock;
pub use config::{Call, CostModel, Cpu, Driver, FlatCost, LanConfig, LanDir, NodeState, SimConfig, StreamPolicy};
pub use ids::{HostId, IfaceId, LanId, NatId, NodeId, ObsId, SiteId};
pub use link::{LinkChange, LinkConfig, Loss, reference_queue_bytes};
pub use metrics::{DropReason, Latency, Metrics, NodeMetrics};
pub use nat::{NatConfig, NatKind, PortPolicy};
pub use node::{IfaceEvent, Node, StreamEvent, StreamId, StreamKind, StreamOp, Transmit, Work};
pub use rng::{Random, Rng, Stream};
pub use sim::{Sim, SiteRef};

/// Virtual time in nanoseconds.
pub type Time = u64;
/// One microsecond.
pub const US: Time = 1_000;
/// One millisecond.
pub const MS: Time = 1_000_000;
/// One second.
pub const SEC: Time = 1_000_000_000;
/// The wall clock reading, in nanoseconds since the Unix epoch, of a node whose clock has no skew at time 0.
pub const WALL_EPOCH: u64 = 1_700_000_000 * SEC;
