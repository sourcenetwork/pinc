//! Thread-per-core: an endpoint on each of two nuclei workers, each with its own socket and its driver on its own worker,
//! exchange streams and datagrams.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::items_after_statements,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

mod vinc_common;

use nuclei::RuntimeHandle;
use nuclei::runtime::worker_index;
use nuclei::sync::oneshot;
use vinc::{Endpoint, Vinc};
use vinc_common::{ECHO, lo, serve_conn, within};
use vinc_nuclei::spawn_on_worker;

/// Build an endpoint on `worker` and run its driver there; the endpoint and the worker the driver runs on come back.
fn on_worker(handle: &RuntimeHandle, worker: usize) -> oneshot::Receiver<(Endpoint, Option<usize>)> {
    let (up, ready) = oneshot::channel();
    spawn_on_worker(handle, worker, async move {
        let (ep, driver) = Vinc::builder().alpn(ECHO).bind_nuclei(lo()).await.unwrap();
        up.send((ep, worker_index())).ok().unwrap();
        driver.run().await
    })
    .unwrap()
    .detach();
    ready
}

#[nuclei::test(threads = 2)]
async fn endpoints_on_different_workers_exchange_streams_and_datagrams() {
    within(60, async {
        let handle = RuntimeHandle::try_current().unwrap();
        assert_eq!(handle.workers(), 2);
        let ((a, wa), (b, wb)) = (
            on_worker(&handle, 0).await.unwrap(),
            on_worker(&handle, 1).await.unwrap(),
        );
        assert_eq!((wa, wb), (Some(0), Some(1)), "each driver runs on its own worker");

        let s = b.clone();
        nuclei::spawn(async move {
            while let Some(i) = s.accept().await {
                nuclei::spawn(serve_conn(i.into_connection())).detach();
            }
        })
        .detach();

        let conn = a.connect(b.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        let payload: Vec<u8> = (0..200_000u32).map(|i| (i % 249) as u8).collect();
        tx.write_all(&payload).await.unwrap();
        tx.finish().await.unwrap();
        assert_eq!(rx.read_to_end(1 << 20).await.unwrap(), payload);

        // A datagram each way, on a session the first endpoint accepts.
        let back = b.connect(a.addr(), ECHO).await.unwrap();
        let (mut tx3, _rx3) = back.open_bi().await.unwrap();
        tx3.write_all(b"x").await.unwrap();
        let inc = a.accept().await.unwrap().into_connection();
        back.send_datagram(b"across workers").await.unwrap();
        assert_eq!(inc.read_datagram().await.unwrap(), b"across workers");
        inc.send_datagram(b"and back").await.unwrap();
        assert_eq!(back.read_datagram().await.unwrap(), b"and back");
    })
    .await;
}
