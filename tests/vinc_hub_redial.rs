//! A dial to a peer that restarted on the same address, with and without a hub named as relay.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::needless_continue)]

#[macro_use]
mod vinc_common;

use std::net::SocketAddr;
use std::time::Duration;

use vinc::{NodeAddr, Relay};
use vinc_common::{ECHO, echo_stream, within};

/// An endpoint bound at `addr`, so a restarted peer can come back on the same address.
macro_rules! endpoint_at {
    ($builder:expr, $addr:expr) => {{
        let sock = ::std::sync::Arc::new(::nuclei::Handle::<::std::net::UdpSocket>::bind($addr).await.unwrap());
        let (r, s) = (::std::sync::Arc::clone(&sock), ::std::sync::Arc::clone(&sock));
        $builder
            .local_addr(sock.local_addr().unwrap())
            .build(
                async move |buf: &mut [u8]| r.recv_from(buf).await,
                async move |pkt: &[u8], to: SocketAddr| s.send_to(pkt, to).await,
                async |at: ::std::time::Instant| ::nuclei::time::sleep_until_precise(at).await,
            )
            .unwrap()
    }};
}

/// Run `ep` and echo every stream of every session it accepts.
macro_rules! serve_echo {
    ($ep:expr) => {{
        let (run, acc) = ($ep.clone(), $ep.clone());
        nuclei::spawn_local(async move {
            let serve = async move {
                let mut open = Vec::new();
                while let Some(inc) = acc.accept().await {
                    let conn = inc.into_connection();
                    if let Ok((tx, rx)) = conn.accept_bi().await {
                        echo_stream(tx, rx).await;
                    }
                    open.push(conn);
                }
            };
            nuclei::select! {
                _r = run.run() => {},
                () = serve => {},
            }
        })
    }};
}

/// Dial `to` and echo one message on a fresh stream; whether the echo came back within 3 s.
macro_rules! echoes {
    ($a:expr, $to:expr) => {{
        nuclei::time::timeout(Duration::from_secs(3), async {
            let conn = $a.connect($to, ECHO).await?;
            let (mut tx, mut rx) = conn.open_bi().await?;
            tx.write_all(b"ping").await?;
            tx.finish().await?;
            let mut got = [0u8; 4];
            rx.read_exact(&mut got).await?;
            Ok::<_, vinc::Error>(got == *b"ping")
        })
        .await
        .map_or(false, |r| r.inspect_err(|e| eprintln!("echo: {e}")).unwrap_or(false))
    }};
}

async fn redial_after_restart(hub: bool) -> bool {
    let relays = if hub {
        let h = endpoint_at!(vinc_common::builder().seed(&[10; 32]).unwrap().hub(), vinc_common::lo());
        let relay = Relay::new(h.id()).with_udp(h.local_addr());
        let run = h.clone();
        nuclei::spawn_local(async move {
            let _ = run.run().await;
        })
        .detach();
        std::mem::forget(h);
        vec![relay]
    } else {
        Vec::new()
    };
    let b = endpoint_at!(
        vinc_common::builder()
            .seed(&[2; 32])
            .unwrap()
            .alpn(ECHO)
            .relays(relays.clone()),
        vinc_common::lo()
    );
    let b_addr = b.local_addr();
    let b_id = b.id();
    let b_task = serve_echo!(b);
    let a = endpoint_at!(
        vinc_common::builder()
            .seed(&[1; 32])
            .unwrap()
            .alpn(ECHO)
            .relays(relays.clone()),
        vinc_common::lo()
    );
    let run = a.clone();
    nuclei::spawn_local(async move {
        let _ = run.run().await;
    })
    .detach();
    let mut to = NodeAddr::new(b_id);
    to.direct = vec![b_addr];
    // As a node does: a topic both joined.
    assert!(echoes!(a, to.clone()), "the first dial echoes");
    if hub {
        a.join(b"t", &[]).await.unwrap();
        b.join(b"t", &[]).await.unwrap();
        a.publish(b"t", b"x", None).await.unwrap();
        nuclei::time::sleep(Duration::from_secs(1)).await;
    }
    // The peer stops without a word, as a process that is killed.
    drop(b_task);
    drop(b);
    // Its tasks end and let the socket go.
    nuclei::time::sleep(Duration::from_millis(300)).await;
    // A dial while the peer is down, as a replicator's retry makes. It fails, or the connection it hands back (reported
    // early, with a cached allow) ends within the early bound and fails what was written on it.
    let at = std::time::Instant::now();
    let down = nuclei::time::timeout(Duration::from_secs(5), async {
        let conn = a.connect(to.clone(), ECHO).await?;
        let (mut tx, mut rx) = conn.open_bi().await?;
        tx.write_all(b"ping").await?;
        let mut got = [0u8; 4];
        let read = rx.read_exact(&mut got).await;
        // What was written before the connection failed is reported as failed, not taken as sent.
        if read.is_err() {
            assert!(tx.finish().await.is_err(), "the stream of a failed connection finished");
        }
        read
    })
    .await;
    eprintln!("down: {down:?} after {:?}", at.elapsed());
    assert!(
        matches!(&down, Ok(Err(e)) if matches!(e.kind(), vinc::ErrorKind::TimedOut | vinc::ErrorKind::Unreachable)),
        "a dial to a peer that stopped did not fail with TimedOut or Unreachable within 5 s: {down:?}"
    );
    // The same peer comes back on the same address.
    let b = endpoint_at!(
        vinc_common::builder().seed(&[2; 32]).unwrap().alpn(ECHO).relays(relays),
        b_addr
    );
    let _b_task = serve_echo!(b);
    if hub {
        b.join(b"t", &[]).await.unwrap();
    }
    // Retried every second for 10 s, as a replicator retries.
    let mut ok = false;
    for _ in 0..10 {
        if echoes!(a, to.clone()) {
            ok = true;
            break;
        }
        nuclei::time::sleep(Duration::from_secs(1)).await;
    }
    a.close().await;
    b.close().await;
    ok
}

#[nuclei::test]
async fn a_redial_reaches_a_restarted_peer_without_a_hub() {
    within(90, async { assert!(redial_after_restart(false).await) }).await;
}

#[nuclei::test]
async fn a_redial_reaches_a_restarted_peer_with_a_hub_named() {
    within(90, async {
        assert!(
            redial_after_restart(true).await,
            "the redial did not reach the restarted peer"
        );
    })
    .await;
}
