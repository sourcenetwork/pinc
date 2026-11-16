//! The distributed test harness of VINC: one binary that builds a real or emulated network, runs VINC, iroh and
//! rust-libp2p nodes on it, injects faults, measures from the programs and from the kernel, and writes results.
//!
//! - [`scenario`]: the scenario files (topology, stacks, workload, faults, repetitions) and their validation.
//! - [`plan`]: every address, interface, route, translation rule, shaper and CPU set of a scenario, as data.
//! - [`backend`]: where nodes run; [`helper`] holds the root a backend needs, nothing else does.
//! - [`orchestrate`]: one run from start to teardown, as events.
//! - [`node`]: what runs inside each node.
//! - [`serve`]: the dashboard.
//! - [`metrics`], [`results`]: the kernel's numbers, and the result files and tables.
//! - [`workloads`]: the real workloads (publish and subscribe, syncing a value, reconciling sets) of a scenario;
//!   [`dtn`]: the delay-tolerant workload and the rules it checks.
//! - [`quiet`]: no measurement on a busy machine.
//!
//! Invariants: a run always tears down what it created (also on a signal or a failed node) and refuses to start over
//! leftovers; a number that was not measured is reported as such; the machine, the CPU sets and the MTU are stated with
//! every result.

pub mod backend;
pub mod docker;
pub mod dtn;
pub mod error;
pub mod helper;
pub mod metrics;
pub mod node;
pub mod orchestrate;
pub mod plan;
pub mod quiet;
pub mod results;
pub mod scenario;
pub mod scenario_transport;
pub mod serve;
pub mod vinc_endpoints;
pub mod workloads;
