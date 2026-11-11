//! The transport tests in a node: the comparison benches' scenario code (`benches/benches/compare/`), compiled into
//! this binary unchanged, so a test between two nodes of a network is the same code as the loopback comparison.

#[path = "../../../benches/benches/compare/mod.rs"]
mod compare;

// Counts allocations only when a transport test asks for it (`--count-allocs`); otherwise one relaxed load per call.
#[global_allocator]
static ALLOC: compare::Counting = compare::Counting;

use crate::scenario::Stack;

/// Run the server or the client of a transport test for `stack` (arguments as the comparison binaries take them).
pub fn run(stack: Stack, args: Vec<String>) {
    match stack {
        Stack::Vinc => compare::run_args::<compare::vinc::Vinc1>(args),
        Stack::Iroh => compare::run_args::<compare::iroh::Iroh>(args),
        // The comparison's libp2p runs over QUIC unless told `--variant=tcp`.
        Stack::Libp2p => compare::run_args::<compare::libp2p::Libp2p>(args),
    }
}
