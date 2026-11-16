//! One endpoint per worker on a shared port, as the comparison's per-core server runs (`benches/benches/compare/vinc.rs`):
//! two endpoints of one identity, each on a socket of its own on one port (`SO_REUSEPORT`) and on a worker of its own.
//! The kernel hands every peer's datagrams to the endpoint its address hashes to: many clients are spread over both,
//! each served by exactly one, and a client that dials again from the same socket reaches the same endpoint and resumes.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

#[macro_use]
mod vinc_common;

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use nuclei::RuntimeHandle;
use nuclei::net::UdpSocketBuilder;
use nuclei::sync::oneshot;
use vinc::{Limits, NodeAddr};
use vinc_common::{ECHO, serve_conn, within};

const SEED: [u8; 32] = [7; 32];

/// The endpoint of `$builder` over a new loopback UDP socket on `$port` that other sockets of the process share.
macro_rules! shared_endpoint {
    ($builder:expr, $port:expr) => {{
        let b = UdpSocketBuilder::new_v4().unwrap();
        b.set_reuseport(true).unwrap();
        let sock = ::std::sync::Arc::new(b.bind(([127, 0, 0, 1], $port).into()).unwrap());
        let (r, s) = (::std::sync::Arc::clone(&sock), ::std::sync::Arc::clone(&sock));
        $builder
            .local_addr(sock.local_addr().unwrap())
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                async move |pkt: &[u8], to: ::std::net::SocketAddr| s.send_to(pkt, to).await,
                async |at: ::std::time::Instant| ::nuclei::time::sleep_until_precise(at).await,
            )
            .unwrap()
    }};
}

/// A group of two endpoints of one identity on one port, one per worker; the count of sessions each accepted.
struct Group {
    addr: NodeAddr,
    served: [Arc<AtomicUsize>; 2],
    _tasks: Vec<nuclei::Task<()>>,
}

async fn group() -> Group {
    let handle = RuntimeHandle::try_current().unwrap();
    assert_eq!(handle.workers(), 2);
    // The first socket of the group picks the port and leaves once both endpoints have theirs.
    let probe = UdpSocketBuilder::new_v4().unwrap();
    probe.set_reuseport(true).unwrap();
    let probe = probe.bind(([127, 0, 0, 1], 0).into()).unwrap();
    let port = probe.local_addr().unwrap().port();
    let served = [Arc::new(AtomicUsize::new(0)), Arc::new(AtomicUsize::new(0))];
    let (mut tasks, mut addrs) = (Vec::new(), Vec::new());
    for (w, count) in served.iter().enumerate() {
        let (tx, rx) = oneshot::channel::<NodeAddr>();
        let count = Arc::clone(count);
        tasks.push(
            handle
                .spawn_local_on_worker(w, move || async move {
                    let ep = shared_endpoint!(vinc_common::builder().seed(&SEED).unwrap().alpn(ECHO), port);
                    tx.send(ep.addr()).ok().unwrap();
                    let runner = ep.clone();
                    nuclei::spawn_local(async move {
                        let _ = runner.run().await;
                    })
                    .detach();
                    while let Some(inc) = ep.accept().await {
                        count.fetch_add(1, Relaxed);
                        nuclei::spawn_local(serve_conn(inc.into_connection())).detach();
                    }
                })
                .unwrap(),
        );
        addrs.push(rx.await.unwrap());
    }
    drop(probe);
    assert_eq!(
        addrs[0], addrs[1],
        "one identity on one port: the two endpoints have one address"
    );
    Group {
        addr: addrs.swap_remove(0),
        served,
        _tasks: tasks,
    }
}

async fn client() -> vinc::Endpoint<impl vinc::Hosted> {
    vinc_common::bind(vinc_common::builder().alpn(ECHO).limits(Limits {
        connections: 1,
        ..Limits::default()
    }))
    .await
}

async fn echo_once<H: vinc::Hosted + 'static>(conn: &vinc::Connection<H>) {
    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
    tx.write_all(b"ping").await.unwrap();
    tx.finish().await.unwrap();
    let mut got = [0u8; 4];
    rx.read_exact(&mut got).await.unwrap();
    assert_eq!(&got, b"ping");
}

#[nuclei::test(threads = 2)]
async fn sixty_four_clients_are_spread_over_two_endpoints_of_one_identity_each_served_by_one() {
    within(120, async {
        let g = group().await;
        // Held to the end, so every client has a socket, and a port, of its own.
        let mut clients = Vec::new();
        for _ in 0..64 {
            let ep = client().await;
            let conn = ep.connect(g.addr.clone(), ECHO).await.unwrap();
            assert_eq!(conn.remote(), g.addr.node, "the dial reached the group's identity");
            echo_once(&conn).await;
            clients.push((ep, conn));
        }
        let (a, b) = (g.served[0].load(Relaxed), g.served[1].load(Relaxed));
        assert_eq!(
            a + b,
            64,
            "every connection was accepted by exactly one endpoint ({a} and {b})"
        );
        assert!(
            a > 0 && b > 0,
            "the kernel spread the clients over both endpoints ({a} and {b})"
        );
    })
    .await;
}

#[nuclei::test(threads = 2)]
async fn a_client_resuming_from_the_same_socket_reaches_the_same_endpoint_and_resumes() {
    within(60, async {
        let g = group().await;
        let ep = client().await;
        let first = ep.connect(g.addr.clone(), ECHO).await.unwrap();
        assert!(!first.resumed(), "the first dial has no ticket");
        echo_once(&first).await;
        first.close(0).await;
        let _ = first.closed().await;
        let again = ep.connect(g.addr.clone(), ECHO).await.unwrap();
        again.answered().await.unwrap();
        assert!(again.resumed(), "the redial from the same socket resumed");
        echo_once(&again).await;
        let counts = [g.served[0].load(Relaxed), g.served[1].load(Relaxed)];
        assert!(
            counts == [2, 0] || counts == [0, 2],
            "both dials were served by one endpoint, not {counts:?}"
        );
    })
    .await;
}
