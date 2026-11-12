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

/// One transmit on the in-memory wire: its bytes, its sender and its segment size.
type Wire = (Vec<u8>, SocketAddr, usize);

/// An endpoint whose host is a pair of in-memory queues: a send puts the whole transmit on the peer's queue, a receive
/// hands a whole transmit back with its segment size, as a socket with segmentation and receive offload does.
/// `coalesced` counts the receives that held more than one datagram; with `lose` above zero every `lose`th transmit
/// is lost on the wire.
fn wired_end(
    me: SocketAddr,
    rx: smol::channel::Receiver<Wire>,
    tx: smol::channel::Sender<Wire>,
    coalesced: Arc<std::sync::atomic::AtomicUsize>,
    lose: usize,
) -> vinc::Endpoint<impl vinc::Hosted> {
    let sent = std::cell::Cell::new(0usize);
    Vinc::builder()
        .alpn(ALPN)
        .batch(8)
        .local_addr(me)
        .build_batched(
            async move |buf: &mut [u8]| {
                let (d, from, segment) = rx.recv().await.map_err(|_| std::io::ErrorKind::BrokenPipe)?;
                buf[..d.len()].copy_from_slice(&d);
                if d.len() > segment {
                    coalesced.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                }
                Ok((d.len(), from, segment))
            },
            async move |pkt: &[u8], _to: SocketAddr, segment: usize| {
                sent.set(sent.get() + 1);
                if lose == 0 || !sent.get().is_multiple_of(lose) {
                    let _ = tx.send((pkt.to_vec(), me, segment)).await;
                }
                Ok(pkt.len().div_ceil(segment.max(1)))
            },
            async |at: Instant| tokio::time::sleep_until(tokio::time::Instant::from_std(at)).await,
        )
        .unwrap()
}

/// Two endpoints wired to each other in memory; `coalesced` counts the first one's receives of several datagrams.
fn wired_pair(
    coalesced: Arc<std::sync::atomic::AtomicUsize>,
) -> (vinc::Endpoint<impl vinc::Hosted>, vinc::Endpoint<impl vinc::Hosted>) {
    wired_pair_losing(coalesced, 0)
}

/// As [`wired_pair`], with every `lose`th transmit of the second endpoint lost (none if zero).
fn wired_pair_losing(
    coalesced: Arc<std::sync::atomic::AtomicUsize>,
    lose: usize,
) -> (vinc::Endpoint<impl vinc::Hosted>, vinc::Endpoint<impl vinc::Hosted>) {
    let (a, b): (SocketAddr, SocketAddr) = ("10.0.0.1:7".parse().unwrap(), "10.0.0.2:7".parse().unwrap());
    let ((to_a, at_a), (to_b, at_b)) = (smol::channel::unbounded(), smol::channel::unbounded());
    (
        wired_end(a, at_a, to_b, coalesced, 0),
        wired_end(b, at_b, to_a, Arc::new(std::sync::atomic::AtomicUsize::new(0)), lose),
    )
}

/// A host that coalesces: each receive hands the endpoint a whole transmit of its peer, several datagrams with their
/// segment size, as a socket with receive offload does. Everything arrives, in order, and batches did hold more than
/// one datagram.
#[tokio::test(flavor = "current_thread")]
async fn a_coalescing_host_delivers_several_datagrams_in_one_receive() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let coalesced = Arc::new(AtomicUsize::new(0));
    let (server, client) = wired_pair(Arc::clone(&coalesced));
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

/// A reader that borrows: the stream lends its bytes in place, consumes what the reader says it used and lends the
/// rest again; a reader that uses nothing gets the same bytes back; the end of the stream is `None`.
#[tokio::test(flavor = "current_thread")]
async fn a_stream_lends_its_bytes_to_the_reader_in_place() {
    let (server, client) = wired_pair(Arc::new(std::sync::atomic::AtomicUsize::new(0)));
    let addr = server.addr();
    let payload: Vec<u8> = (0..100_000u32).map(|i| (i % 249) as u8).collect();
    let sent = payload.clone();
    let local = tokio::task::LocalSet::new();
    local
        .run_until(async move {
            let serve = tokio::task::spawn_local(async move {
                let conn = server.accept().await.unwrap().into_connection();
                let mut rx = conn.accept_uni().await.unwrap();
                let mut got = Vec::new();
                // The first bytes are looked at and left where they are: they come again.
                let mut first = Vec::new();
                assert_eq!(
                    rx.read_with(|b| {
                        first = b.to_vec();
                        0
                    })
                    .await
                    .unwrap(),
                    Some(0)
                );
                assert_ne!(first.len(), 0);
                let mut again = Vec::new();
                assert_eq!(
                    rx.read_with(|b| {
                        again = b.to_vec();
                        3
                    })
                    .await
                    .unwrap(),
                    Some(3)
                );
                assert_eq!(&again[..first.len()], &first[..], "bytes left unused were lent again");
                got.extend_from_slice(&again[..3]);
                // Then at most 1000 bytes of each loan are used, so most loans are used in parts.
                let (mut loans, mut largest) = (0usize, 0usize);
                while let Some(n) = rx
                    .read_with(|b| {
                        let n = b.len().min(1000);
                        got.extend_from_slice(&b[..n]);
                        largest = largest.max(b.len());
                        n
                    })
                    .await
                    .unwrap()
                {
                    assert!(n > 0, "a loan is never empty");
                    loans += 1;
                }
                assert_eq!(
                    rx.read_with(|_| unreachable!("nothing is lent after the end"))
                        .await
                        .unwrap(),
                    None
                );
                assert!(
                    largest > 1000 && loans >= 100,
                    "{loans} loans, the largest {largest} bytes"
                );
                conn.close(0).await;
                got
            });
            let conn = client.connect(addr, ALPN).await.unwrap();
            let mut tx = conn.open_uni().await.unwrap();
            tx.write_all(&sent).await.unwrap();
            tx.finish().await.unwrap();
            // The client's endpoint runs while one of its futures is awaited: this one, until the reader closes.
            conn.closed().await;
            assert_eq!(serve.await.unwrap(), payload);
        })
        .await;
}

/// A body is sent from where it is: each kind of buffer arrives whole and in order, an empty one ends its stream at
/// once, and when the wire loses transmits the lost ranges are read from the body again. A stream that already
/// carries written bytes refuses a body.
#[tokio::test(flavor = "current_thread")]
async fn a_stream_sends_an_owned_body_whole_and_again_after_loss() {
    let large: Vec<u8> = (0..300_000u32).map(|i| (i % 241) as u8).collect();
    let shared: std::rc::Rc<[u8]> = (0..50_000u32).map(|i| (i % 239) as u8).collect();
    let fixed: &'static [u8] = b"ten bytes!";
    for lose in [0, 9] {
        let (server, client) = wired_pair_losing(Arc::new(std::sync::atomic::AtomicUsize::new(0)), lose);
        let addr = server.addr();
        let (large, shared) = (large.clone(), std::rc::Rc::clone(&shared));
        let local = tokio::task::LocalSet::new();
        local
            .run_until(async move {
                let serve = tokio::task::spawn_local(async move {
                    let conn = server.accept().await.unwrap().into_connection();
                    let mut got = Vec::new();
                    for _ in 0..4 {
                        let mut rx = conn.accept_uni().await.unwrap();
                        got.push(rx.read_to_end(1 << 20).await.unwrap());
                    }
                    conn.close(0).await;
                    // Under loss a later stream may be heard of first: the bodies differ in length.
                    got.sort_by_key(Vec::len);
                    got
                });
                let conn = client.connect(addr, ALPN).await.unwrap();
                let bodies = [
                    vinc::Body::from(large.clone()),
                    vinc::Body::from(std::rc::Rc::clone(&shared)),
                    vinc::Body::from(fixed),
                    vinc::Body::from(Vec::new()),
                ];
                for body in bodies {
                    let mut tx = conn.open_uni().await.unwrap();
                    tx.send_owned(body).await.unwrap();
                }
                // A stream that was written to keeps its buffer: it takes no body.
                let mut written = conn.open_uni().await.unwrap();
                written.write_all(b"x").await.unwrap();
                assert!(written.send_owned(vec![1u8]).await.is_err());
                written.reset(0).await;
                conn.closed().await;
                let got = serve.await.unwrap();
                assert_eq!(got.len(), 4);
                assert_eq!(got[0].len(), 0);
                assert_eq!(got[1], fixed);
                assert_eq!(got[2], &shared[..]);
                assert_eq!(got[3], large, "losing every {lose}th transmit");
            })
            .await;
    }
}
