//! Shared pieces of the facade tests, which run on the nuclei runtime and nothing else: endpoints bound with
//! `bind_nuclei` and driven by `nuclei::spawn`, the services a peer runs, and helpers that bound a wait.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::zombie_processes,
    clippy::useless_conversion,
    clippy::manual_assert_eq,
    clippy::items_after_statements,
    dead_code,
    clippy::needless_continue,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::missing_panics_doc,
    clippy::missing_errors_doc,
    clippy::must_use_candidate
)]

use std::future::Future;
use std::net::SocketAddr;
use std::pin::pin;
use std::sync::Arc;
use std::time::{Duration, Instant};

use vinc::{Admission, Builder, Connection, Discovery, Endpoint, Protocol, RecvStream, SendStream, Vinc};
use vinc_keystore::KeyStore;
use vinc_tests::SplitMix64;

pub const ECHO: &[u8] = b"t/echo";
pub const SINK: &[u8] = b"t/sink";
pub const GEN: &[u8] = b"t/gen";

pub fn lo() -> SocketAddr {
    ([127, 0, 0, 1], 0).into()
}

/// The bytes of the pattern stream `seed` at `offset`.
pub fn pattern(seed: u64, offset: u64, out: &mut [u8]) {
    let mut at = offset & !7;
    let mut rng = SplitMix64::new(seed ^ at.wrapping_mul(0x9E37_79B9_7F4A_7C15));
    let mut word = rng.next_u64().to_le_bytes();
    let mut i = (offset - at) as usize;
    for b in out.iter_mut() {
        if i == 8 {
            at += 8;
            rng = SplitMix64::new(seed ^ at.wrapping_mul(0x9E37_79B9_7F4A_7C15));
            word = rng.next_u64().to_le_bytes();
            i = 0;
        }
        *b = word[i];
        i += 1;
    }
}

pub fn pattern_hash(seed: u64, len: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    let mut buf = vec![0u8; 64 * 1024];
    let mut at = 0;
    while at < len {
        let n = buf.len().min((len - at) as usize);
        pattern(seed, at, &mut buf[..n]);
        h.update(&buf[..n]);
        at += n as u64;
    }
    *h.finalize().as_bytes()
}

// ---- the services (async) ----

pub async fn echo_stream(mut tx: SendStream, mut rx: RecvStream) {
    let mut buf = vec![0u8; 16 * 1024];
    while let Ok(Some(n)) = rx.read(&mut buf).await {
        if tx.write_all(&buf[..n]).await.is_err() {
            return;
        }
    }
    let _ = tx.finish().await;
}

pub async fn sink_stream(mut tx: SendStream, mut rx: RecvStream) {
    let mut h = blake3::Hasher::new();
    let mut total = 0u64;
    let mut buf = vec![0u8; 64 * 1024];
    while let Ok(Some(n)) = rx.read(&mut buf).await {
        h.update(&buf[..n]);
        total += n as u64;
    }
    let mut reply = total.to_le_bytes().to_vec();
    reply.extend_from_slice(h.finalize().as_bytes());
    let _ = tx.write_all(&reply).await;
    let _ = tx.finish().await;
}

pub async fn gen_stream(mut tx: SendStream, mut rx: RecvStream) {
    let mut req = [0u8; 16];
    if rx.read_exact(&mut req).await.is_err() {
        return;
    }
    let seed = u64::from_le_bytes(req[..8].try_into().unwrap());
    let len = u64::from_le_bytes(req[8..].try_into().unwrap());
    let mut buf = vec![0u8; 64 * 1024];
    let mut at = 0;
    while at < len {
        let n = buf.len().min((len - at) as usize);
        pattern(seed, at, &mut buf[..n]);
        if tx.write_all(&buf[..n]).await.is_err() {
            return;
        }
        at += n as u64;
    }
    let _ = tx.finish().await;
}

/// Serve one session of any test protocol.
pub async fn serve_conn(conn: Connection) {
    while let Ok((tx, rx)) = conn.accept_bi().await {
        let alpn = conn.alpn().to_vec();
        nuclei::spawn(async move {
            match alpn.as_slice() {
                ECHO => echo_stream(tx, rx).await,
                SINK => sink_stream(tx, rx).await,
                _ => gen_stream(tx, rx).await,
            }
        })
        .detach();
    }
}

pub struct Svc(pub &'static [u8]);

impl Protocol for Svc {
    fn alpn(&self) -> &'static [u8] {
        self.0
    }

    async fn serve(self: Arc<Self>, conn: Connection) {
        serve_conn(conn).await;
    }
}

/// Register `protocol` and serve each session it gets, on nuclei tasks.
pub async fn register<D: Discovery, A: Admission, P: Protocol>(
    ep: &Endpoint<D, A>,
    protocol: Arc<P>,
) -> vinc::Result<()> {
    let registered = ep.register(protocol).await?;
    nuclei::spawn(async move {
        while let Some(conn) = registered.accept().await {
            nuclei::spawn(registered.protocol().serve(conn)).detach();
        }
    })
    .detach();
    Ok(())
}

/// Bind `builder` on loopback and spawn its driver on the nuclei runtime.
pub async fn bind<S: KeyStore + 'static, D: Discovery, A: Admission>(builder: Builder<S, D, A>) -> Endpoint<D, A> {
    let (ep, driver) = builder.bind_nuclei(lo()).await.unwrap();
    nuclei::spawn(driver.run()).detach();
    ep
}

/// An endpoint serving the test protocols, accepting and serving every session it gets.
pub async fn node() -> Endpoint {
    let ep = bind(Vinc::builder().alpn(ECHO).alpn(SINK).alpn(GEN)).await;
    let s = ep.clone();
    nuclei::spawn(async move {
        while let Some(i) = s.accept().await {
            nuclei::spawn(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    ep
}

/// A client endpoint that serves nothing.
pub async fn client() -> Endpoint {
    bind(Vinc::builder().alpn(ECHO)).await
}

/// Fail the test if `f` does not finish in `secs`: a stuck await must fail loudly.
pub async fn within<T>(secs: u64, f: impl Future<Output = T>) -> T {
    nuclei::time::timeout(Duration::from_secs(secs), f)
        .await
        .unwrap_or_else(|_| panic!("the test did not finish in {secs} s"))
}

/// Await `f` for at most `polls` rounds of 2 ms, then drop it if it is still pending. `Some` is its output when it
/// finished first.
pub async fn poll_drop<F: Future>(f: F, polls: usize) -> Option<F::Output> {
    let mut f = pin!(f);
    nuclei::select! {
        biased;
        r = f.as_mut() => Some(r),
        () = async {
            for _ in 0..polls {
                nuclei::time::sleep(Duration::from_millis(2)).await;
            }
        } => None,
    }
}

/// Retry `check` with a bounded backoff until it holds or `secs` pass.
pub async fn eventually<F: Future<Output = bool>>(secs: u64, what: &str, mut check: impl FnMut() -> F) {
    let end = Instant::now() + Duration::from_secs(secs);
    let mut wait = Duration::from_millis(1);
    while !check().await {
        assert!(Instant::now() < end, "not reached in {secs} s: {what}");
        nuclei::time::sleep(wait).await;
        wait = (wait * 2).min(Duration::from_millis(100));
    }
}

/// Run all of `futs` as nuclei tasks; the outputs come back in order.
pub async fn join_all<T: Send + 'static>(
    futs: impl IntoIterator<Item = impl Future<Output = T> + Send + 'static>,
) -> Vec<T> {
    let tasks: Vec<_> = futs.into_iter().map(nuclei::spawn).collect();
    let mut out = Vec::with_capacity(tasks.len());
    for t in tasks {
        out.push(t.await);
    }
    out
}
