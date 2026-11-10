//! Thread-per-core: an endpoint on each of two nuclei workers, each with its own socket and polled on its own worker,
//! exchange streams and datagrams.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

#[macro_use]
mod vinc_common;

use nuclei::RuntimeHandle;
use nuclei::runtime::worker_index;
use nuclei::sync::oneshot;
use vinc::NodeAddr;
use vinc_common::{ECHO, serve_conn, within};

#[nuclei::test(threads = 2)]
async fn endpoints_on_different_workers_exchange_streams_and_datagrams() {
    within(60, async {
        let handle = RuntimeHandle::try_current().unwrap();
        assert_eq!(handle.workers(), 2);
        let (addr_tx, addr_rx) = oneshot::channel::<(NodeAddr, Option<usize>)>();
        let (go_tx, go_rx) = oneshot::channel::<NodeAddr>();

        // Worker 1: the server, its endpoint and everything it serves stay on this worker.
        let server = handle
            .spawn_local_on_worker(1, move || {
                let worker = worker_index();
                async move {
                    let b = lo_endpoint!(vinc_common::builder().alpn(ECHO));
                    addr_tx.send((b.addr(), worker)).ok().unwrap();
                    let a_addr = go_rx.await.unwrap();
                    let s = b.clone();
                    nuclei::spawn_local(async move {
                        while let Some(i) = s.accept().await {
                            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
                        }
                    })
                    .detach();
                    // A datagram each way, on a session this endpoint dials.
                    let back = b.connect(a_addr, ECHO).await.unwrap();
                    let (mut tx, _rx) = back.open_bi().await.unwrap();
                    tx.write_all(b"x").await.unwrap();
                    back.send_datagram(b"across workers").await.unwrap();
                    assert_eq!(back.read_datagram().await.unwrap(), b"and back");
                    worker
                }
            })
            .unwrap();

        // Worker 0: the client.
        let (b_addr, wb) = addr_rx.await.unwrap();
        let client = handle
            .spawn_local_on_worker(0, move || {
                let worker = worker_index();
                async move {
                    let a = lo_endpoint!(vinc_common::builder().alpn(ECHO));
                    go_tx.send(a.addr()).ok().unwrap();
                    let conn = a.connect(b_addr, ECHO).await.unwrap();
                    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                    let payload: Vec<u8> = (0..200_000u32).map(|i| (i % 249) as u8).collect();
                    tx.write_all(&payload).await.unwrap();
                    tx.finish().await.unwrap();
                    assert_eq!(rx.read_to_end(1 << 20).await.unwrap(), payload);
                    let inc = a.accept().await.unwrap().into_connection();
                    assert_eq!(inc.read_datagram().await.unwrap(), b"across workers");
                    inc.send_datagram(b"and back").await.unwrap();
                    worker
                }
            })
            .unwrap();
        assert_eq!((client.await, server.await, wb), (Some(0), Some(1), Some(1)));
    })
    .await;
}
