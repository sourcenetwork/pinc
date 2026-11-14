//! What an endpoint with the default builder (no port mapping) costs per pending call: the size of the future of
//! `accept`, `run` and `close`, against the same endpoint before port mapping existed.
//!
//! The figures were measured in a detached worktree of the commit this branch was cut from (74351b87), with the same
//! test and a separate build folder: `accept` 1272 bytes, `run` 1272, `close` 1256. The port-mapping step of the
//! driver may keep one boxed future in a slot of the driving call (one pointer to a trait object); nothing else.
#![allow(clippy::unwrap_used, missing_docs)]

use std::future::Future;
use std::net::SocketAddr;
use std::pin::Pin;
use std::time::Instant;

use vinc::Vinc;

const ACCEPT: usize = 1272;
const RUN: usize = 1272;
const CLOSE: usize = 1256;

#[tokio::test(flavor = "current_thread")]
async fn a_default_endpoint_pays_one_pointer_for_the_port_mapping_step() {
    let ep = Vinc::builder()
        .alpn(b"size/test".to_vec())
        .local_addr("192.168.1.5:4433".parse().unwrap())
        .build(
            async |_buf: &mut [u8]| std::future::pending::<std::io::Result<(usize, SocketAddr)>>().await,
            async |pkt: &[u8], _to: SocketAddr| Ok(pkt.len()),
            async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
        )
        .unwrap();
    let slot = size_of::<Option<Pin<Box<dyn Future<Output = Option<Vec<u8>>>>>>>();
    let (a, r, c) = (
        std::mem::size_of_val(&ep.accept()),
        std::mem::size_of_val(&ep.run()),
        std::mem::size_of_val(&ep.close()),
    );
    println!("sizes: accept {a} (was {ACCEPT}), run {r} (was {RUN}), close {c} (was {CLOSE}), slot {slot}");
    assert!(a <= ACCEPT + slot, "accept grew from {ACCEPT} to {a} bytes");
    assert!(r <= RUN + slot, "run grew from {RUN} to {r} bytes");
    assert!(c <= CLOSE + slot, "close grew from {CLOSE} to {c} bytes");
}
