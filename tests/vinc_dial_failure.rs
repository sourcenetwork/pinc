//! Dials to one peer and protocol are independent: the failure of one does not end another.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::semicolon_if_nothing_returned
)]

mod vinc_common;

use std::net::{SocketAddr, UdpSocket};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use vinc::NodeAddr;

// ------------------------------------------------------------------------------------------------ claim 2

/// A UDP relay to `to` that drops every datagram until `open` is set.
fn gate_proxy(to: SocketAddr, open: Arc<AtomicBool>, stop: Arc<AtomicBool>) -> SocketAddr {
    let s = UdpSocket::bind("127.0.0.1:0").unwrap();
    s.set_read_timeout(Some(Duration::from_millis(20))).unwrap();
    let addr = s.local_addr().unwrap();
    std::thread::spawn(move || {
        let mut client: Option<SocketAddr> = None;
        let mut buf = vec![0u8; 65_536];
        while !stop.load(Ordering::Relaxed) {
            let Ok((n, from)) = s.recv_from(&mut buf) else {
                continue;
            };
            if from != to {
                client = Some(from);
            }
            if !open.load(Ordering::Relaxed) {
                continue;
            }
            if from == to {
                if let Some(c) = client {
                    let _ = s.send_to(&buf[..n], c);
                }
            } else {
                let _ = s.send_to(&buf[..n], to);
            }
        }
    });
    addr
}

/// One dial's failure ends only that dial: a second dial to the same peer and protocol, started later, still connects.
#[nuclei::test]
async fn c2_one_dials_failure_ends_another_dial_to_the_same_peer() {
    vinc_common::within(150, async {
        let server = vinc_common::node().await;
        let s_addr = server.addr();
        let s_udp = s_addr.direct[0];
        let client = vinc_common::bind(
            vinc_common::builder()
                .alpn(vinc_common::ECHO)
                .connect_timeout(Duration::from_secs(40)),
        )
        .await;
        // Dial 1 goes to an address that never answers: its handshake gives up after 30 s (ConnectFailed{Timeout}).
        let hole = UdpSocket::bind("127.0.0.1:0").unwrap();
        let (open, stop) = (Arc::new(AtomicBool::new(false)), Arc::new(AtomicBool::new(false)));
        // Dial 2 goes through a relay that lets nothing through until just after dial 1 gave up, then works.
        let proxy = gate_proxy(s_udp, Arc::clone(&open), Arc::clone(&stop));
        let t0 = Instant::now();
        let (c1, n1) = (
            client.clone(),
            NodeAddr {
                node: s_addr.node,
                direct: vec![hole.local_addr().unwrap()],
                relays: vec![],
            },
        );
        let d1 = nuclei::spawn_local(async move {
            let r = c1.connect(n1, vinc_common::ECHO).await;
            (
                t0.elapsed(),
                r.map(|_| ()).map_err(|e| format!("{:?}: {}", e.kind(), e.message())),
            )
        });
        nuclei::time::sleep(Duration::from_secs(27)).await;
        let (c2, n2) = (
            client.clone(),
            NodeAddr {
                node: s_addr.node,
                direct: vec![proxy],
                relays: vec![],
            },
        );
        let d2 = nuclei::spawn_local(async move {
            let r = c2.connect(n2, vinc_common::ECHO).await;
            let at = t0.elapsed();
            let out = match r {
                Ok(conn) => {
                    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                    tx.write_all(b"alive").await.unwrap();
                    tx.finish().await.unwrap();
                    Ok(rx.read_to_end(100).await.unwrap())
                }
                Err(e) => Err(format!("{:?}: {}", e.kind(), e.message())),
            };
            (at, out)
        });
        nuclei::time::sleep_until(t0 + Duration::from_millis(30_500)).await;
        open.store(true, Ordering::Relaxed);
        let r2 = d2.await;
        let r1 = d1.await;
        assert!(r1.1.is_err(), "dial 1 went to a dead address: {r1:?}");
        stop.store(true, Ordering::Relaxed);
        assert!(r2.1.is_ok(), "dial 2 was ended by dial 1's failure: {r2:?}");
    })
    .await;
}

/// Control for c2: the relay path alone, opened 3.5 s after the dial, gives a working session.
#[nuclei::test]
async fn c2_control_the_relay_path_alone_connects() {
    vinc_common::within(60, async {
        let server = vinc_common::node().await;
        let s_addr = server.addr();
        let client = vinc_common::bind(
            vinc_common::builder()
                .alpn(vinc_common::ECHO)
                .connect_timeout(Duration::from_secs(40)),
        )
        .await;
        let (open, stop) = (Arc::new(AtomicBool::new(false)), Arc::new(AtomicBool::new(false)));
        let proxy = gate_proxy(s_addr.direct[0], Arc::clone(&open), Arc::clone(&stop));
        let t0 = Instant::now();
        let c2 = client.clone();
        let n2 = NodeAddr {
            node: s_addr.node,
            direct: vec![proxy],
            relays: vec![],
        };
        let d2 = nuclei::spawn_local(async move {
            let r = c2.connect(n2, vinc_common::ECHO).await;
            (t0.elapsed(), r.is_ok())
        });
        nuclei::time::sleep(Duration::from_millis(3_500)).await;
        open.store(true, Ordering::Relaxed);
        let r2 = d2.await;
        stop.store(true, Ordering::Relaxed);
        assert!(r2.1);
    })
    .await;
}

// ------------------------------------------------------------------------------------------------ claim 3
