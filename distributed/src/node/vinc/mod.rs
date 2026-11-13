//! The VINC node program: `vinc_node::Node` on real sockets, driven by one task on the nuclei runtime.
//!
//! - [`core`]: the host without a runtime (duties, the node's inputs and outputs); `hub` is the relay a hub runs for its
//!   members and `keys` answers key requests.
//! - [`apps`]: the value and set stores; [`dtn`]: the bundle store of delay-tolerant delivery.
//! - [`net`]: the UDP socket and TCP streams.
//! - [`agent`]: the workload commands and the loop that owns the node.
//!
//! This is the first real-socket host of the composition: it owns the sockets and the timers and calls the node; the
//! node starts no thread and takes no lock. The size of the endpoint's tables is a compile-time shape, so the program
//! picks the smallest of a few shapes that holds the scenario's nodes.

pub mod agent;
pub mod apps;
pub mod core;
pub mod dtn;
pub mod dtnlog;
mod hub;
mod keys;
pub mod net;
pub mod tracelog;

use crate::node::app::for_each_request;
use crate::node::proto::Init;

pub use self::core::{HubAddr, Spec, node_id};

fn block<const K: usize, const D: usize>(init: Init) -> Result<(), String> {
    let rt = nuclei::Builder::new()
        .build()
        .map_err(|e| format!("the runtime did not start: {e}"))?;
    let (tx, rx) = nuclei::sync::mpsc::unbounded_channel();
    std::thread::Builder::new()
        .name("requests".into())
        .spawn(move || for_each_request(|r| tx.send(r).is_ok()))
        .map_err(|e| format!("the input thread did not start: {e}"))?;
    rt.block_on(agent::serve::<K, D>(init, rx))
}

/// Run the VINC node program for `init` until it is told to stop.
///
/// # Errors
/// The node or its sockets could not start, or failed.
pub fn run(init: Init) -> Result<(), String> {
    // The node holds its buffers inline, so it runs on a thread with room for them.
    let sessions = init.sessions;
    let h = std::thread::Builder::new()
        .name("vinc".into())
        .stack_size(512 << 20)
        .spawn(move || match sessions {
            0..=16 => block::<16, 160>(init),
            17..=64 => block::<64, 640>(init),
            65..=256 => block::<256, 2560>(init),
            _ => block::<1024, 10240>(init),
        })
        .map_err(|e| format!("the VINC thread did not start: {e}"))?;
    h.join()
        .map_err(|_| "the VINC thread stopped unexpectedly".to_owned())?
}
