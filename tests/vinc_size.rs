//! What an endpoint with the default builder (no port mapping) costs per pending call: the size of the future of
//! `accept`, `run` and `close`, against the same endpoint before port mapping existed.
//!
//! The figures were measured in a detached worktree of the commit this branch was cut from (74351b87), with the same
//! test and a separate build folder: `accept` 1272 bytes, `run` 1272, `close` 1256. The port-mapping exchange is state
//! in the shared core, so the driving call holds nothing for it; the sizes are not larger than master's (they are 104
//! bytes smaller, because an operation slot of the carriers keeps its version and flag in one word).
#![allow(clippy::unwrap_used, missing_docs)]

use std::net::SocketAddr;
use std::time::Instant;

use vinc::Vinc;

const ACCEPT: usize = 1272;
const RUN: usize = 1272;
const CLOSE: usize = 1256;

#[tokio::test(flavor = "current_thread")]
async fn a_default_endpoint_is_not_larger_than_before_port_mapping() {
    let ep = Vinc::builder()
        .alpn(b"size/test".to_vec())
        .local_addr("192.168.1.5:4433".parse().unwrap())
        .build(
            async |_buf: &mut [u8]| std::future::pending::<std::io::Result<(usize, SocketAddr)>>().await,
            async |pkt: &[u8], _to: SocketAddr| Ok(pkt.len()),
            async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
        )
        .unwrap();
    let (a, r, c) = (
        std::mem::size_of_val(&ep.accept()),
        std::mem::size_of_val(&ep.run()),
        std::mem::size_of_val(&ep.close()),
    );
    println!("sizes: accept {a} (was {ACCEPT}), run {r} (was {RUN}), close {c} (was {CLOSE})");
    assert!(a <= ACCEPT, "accept is {a} bytes, master {ACCEPT}");
    assert!(r <= RUN, "run is {r} bytes, master {RUN}");
    assert!(c <= CLOSE, "close is {c} bytes, master {CLOSE}");
}

/// The sizes of the facade's event and the node's event, which every queued message occupies, measured at 01d367ac:
/// an endpoint that does not ask for envelopes pays nothing for them.
#[cfg(target_pointer_width = "64")]
const EVENT: usize = 120;
#[cfg(target_pointer_width = "64")]
const NODE_EVENT: usize = 128;

#[cfg(target_pointer_width = "64")]
#[test]
fn the_events_are_as_large_as_before_envelopes() {
    let (e, n) = (
        std::mem::size_of::<vinc::Event>(),
        std::mem::size_of::<vinc_node::NodeEvent>(),
    );
    println!("sizes: vinc::Event {e}, vinc_node::NodeEvent {n}");
    assert_eq!(e, EVENT);
    assert_eq!(n, NODE_EVENT);
}
