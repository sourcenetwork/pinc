//! The same closures shape under other executors: an echo on tokio and one on smol, with no change to the facade.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Instant;

use vinc::Vinc;

const ALPN: &[u8] = b"hosts/echo";

#[tokio::test(flavor = "current_thread")]
async fn an_echo_on_tokio() {
    async fn bind() -> vinc::Endpoint<impl vinc::Hosted> {
        let sock = Arc::new(tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap());
        let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
        Vinc::builder()
            .alpn(ALPN)
            .local_addr(sock.local_addr().unwrap())
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
                async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
            )
            .unwrap()
    }
    let (server, client) = (bind().await, bind().await);
    let addr = server.addr();
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async move {
            let serve = tokio::task::spawn_local(async move {
                let conn = server.accept().await.unwrap().into_connection();
                let (mut tx, mut rx) = conn.accept_bi().await.unwrap();
                let got = rx.read_to_end(1 << 16).await.unwrap();
                tx.write_all(&got).await.unwrap();
                tx.finish().await.unwrap();
                conn.closed().await;
            });
            let conn = client.connect(addr, ALPN).await.unwrap();
            let (mut tx, mut rx) = conn.open_bi().await.unwrap();
            tx.write_all(b"hello, tokio").await.unwrap();
            tx.finish().await.unwrap();
            assert_eq!(rx.read_to_end(100).await.unwrap(), b"hello, tokio");
            conn.close(0).await;
            serve.await.unwrap();
        })
        .await;
}

#[test]
fn an_echo_on_smol() {
    fn bind() -> vinc::Endpoint<impl vinc::Hosted> {
        let sock = Arc::new(smol::Async::<std::net::UdpSocket>::bind(([127, 0, 0, 1], 0)).unwrap());
        let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
        Vinc::builder()
            .alpn(ALPN)
            .local_addr(sock.get_ref().local_addr().unwrap())
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
                async |at: Instant| {
                    smol::Timer::at(at).await;
                },
            )
            .unwrap()
    }
    smol::block_on(async {
        let (server, client) = (bind(), bind());
        let addr = server.addr();
        let ex = smol::LocalExecutor::new();
        let serve = ex.spawn(async move {
            let conn = server.accept().await.unwrap().into_connection();
            let (mut tx, mut rx) = conn.accept_bi().await.unwrap();
            let got = rx.read_to_end(1 << 16).await.unwrap();
            tx.write_all(&got).await.unwrap();
            tx.finish().await.unwrap();
            conn.closed().await;
        });
        ex.run(async move {
            let conn = client.connect(addr, ALPN).await.unwrap();
            let (mut tx, mut rx) = conn.open_bi().await.unwrap();
            tx.write_all(b"hello, smol").await.unwrap();
            tx.finish().await.unwrap();
            assert_eq!(rx.read_to_end(100).await.unwrap(), b"hello, smol");
            conn.close(0).await;
            serve.await;
        })
        .await;
    });
}

/// A host that batches: the send closure gets whole transmits (it splits them here, as a host without segmentation
/// offload would have to, and counts the calls), the receive closure reports one datagram per call.
#[tokio::test(flavor = "current_thread")]
async fn a_batching_host_gets_whole_transmits() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    async fn bind(calls: Arc<AtomicUsize>, datagrams: Arc<AtomicUsize>) -> vinc::Endpoint<impl vinc::Hosted> {
        let sock = Arc::new(tokio::net::UdpSocket::bind("127.0.0.1:0").await.unwrap());
        let (r, s) = (Arc::clone(&sock), Arc::clone(&sock));
        Vinc::builder()
            .alpn(ALPN)
            .batch(8)
            .local_addr(sock.local_addr().unwrap())
            .build_batched(
                async move |buf: &mut [u8]| r.recv_from(buf).await.map(|(n, from)| (n, from, n)),
                async move |pkt: &[u8], to: SocketAddr, segment: usize| {
                    calls.fetch_add(1, Ordering::Relaxed);
                    let mut sent = 0;
                    for d in pkt.chunks(segment) {
                        s.send_to(d, to).await?;
                        sent += 1;
                    }
                    datagrams.fetch_add(sent, Ordering::Relaxed);
                    Ok(sent)
                },
                async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
            )
            .unwrap()
    }
    let (calls, datagrams) = (Arc::new(AtomicUsize::new(0)), Arc::new(AtomicUsize::new(0)));
    let (server, client) = (
        bind(Arc::new(AtomicUsize::new(0)), Arc::new(AtomicUsize::new(0))).await,
        bind(Arc::clone(&calls), Arc::clone(&datagrams)).await,
    );
    let addr = server.addr();
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async move {
            let serve = tokio::task::spawn_local(async move {
                let conn = server.accept().await.unwrap().into_connection();
                let (mut tx, mut rx) = conn.accept_bi().await.unwrap();
                let got = rx.read_to_end(1 << 20).await.unwrap();
                tx.write_all(&got).await.unwrap();
                tx.finish().await.unwrap();
                conn.closed().await;
            });
            let conn = client.connect(addr, ALPN).await.unwrap();
            let (mut tx, mut rx) = conn.open_bi().await.unwrap();
            let payload: Vec<u8> = (0..300_000u32).map(|i| (i % 251) as u8).collect();
            tx.write_all(&payload).await.unwrap();
            tx.finish().await.unwrap();
            assert_eq!(rx.read_to_end(1 << 20).await.unwrap(), payload);
            conn.close(0).await;
            serve.await.unwrap();
        })
        .await;
    let (c, d) = (calls.load(Ordering::Relaxed), datagrams.load(Ordering::Relaxed));
    assert!(
        c < d,
        "{c} send calls for {d} datagrams: no transmit carried more than one"
    );
}

/// A host that coalesces: each receive hands the endpoint a whole transmit of its peer, several datagrams with their
/// segment size, as a socket with receive offload does. Everything arrives, in order, and batches did hold more than
/// one datagram.
#[tokio::test(flavor = "current_thread")]
async fn a_coalescing_host_delivers_several_datagrams_in_one_receive() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use smol::channel::{Receiver, Sender, unbounded};

    type Wire = (Vec<u8>, SocketAddr, usize);
    fn bind(
        me: SocketAddr,
        rx: Receiver<Wire>,
        tx: Sender<Wire>,
        coalesced: Arc<AtomicUsize>,
    ) -> vinc::Endpoint<impl vinc::Hosted> {
        Vinc::builder()
            .alpn(ALPN)
            .batch(8)
            .local_addr(me)
            .build_batched(
                async move |buf: &mut [u8]| {
                    let (d, from, segment) = rx.recv().await.map_err(|_| std::io::ErrorKind::BrokenPipe)?;
                    buf[..d.len()].copy_from_slice(&d);
                    if d.len() > segment {
                        coalesced.fetch_add(1, Ordering::Relaxed);
                    }
                    Ok((d.len(), from, segment))
                },
                async move |pkt: &[u8], _to: SocketAddr, segment: usize| {
                    let _ = tx.send((pkt.to_vec(), me, segment)).await;
                    Ok(pkt.len().div_ceil(segment.max(1)))
                },
                async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
            )
            .unwrap()
    }
    let (a, b): (SocketAddr, SocketAddr) = ("10.0.0.1:7".parse().unwrap(), "10.0.0.2:7".parse().unwrap());
    let ((to_a, at_a), (to_b, at_b)) = (unbounded(), unbounded());
    let coalesced = Arc::new(AtomicUsize::new(0));
    let server = bind(a, at_a, to_b, Arc::clone(&coalesced));
    let client = bind(b, at_b, to_a, Arc::new(AtomicUsize::new(0)));
    let addr = server.addr();
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async move {
            let serve = tokio::task::spawn_local(async move {
                let conn = server.accept().await.unwrap().into_connection();
                let (mut tx, mut rx) = conn.accept_bi().await.unwrap();
                let got = rx.read_to_end(1 << 20).await.unwrap();
                tx.write_all(&got).await.unwrap();
                tx.finish().await.unwrap();
                conn.closed().await;
            });
            let conn = client.connect(addr, ALPN).await.unwrap();
            let (mut tx, mut rx) = conn.open_bi().await.unwrap();
            let payload: Vec<u8> = (0..300_000u32).map(|i| (i % 251) as u8).collect();
            tx.write_all(&payload).await.unwrap();
            tx.finish().await.unwrap();
            assert_eq!(rx.read_to_end(1 << 20).await.unwrap(), payload);
            conn.close(0).await;
            serve.await.unwrap();
        })
        .await;
    assert!(
        coalesced.load(Ordering::Relaxed) > 0,
        "no receive held more than one datagram: the batch path was not exercised"
    );
}
