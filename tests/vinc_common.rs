//! Shared pieces of the facade tests: a std-only test executor, the services a peer process runs, and the parent's side
//! of the two-process harness.
//!
//! The two-process tests run the test binary itself again as the peer (`VINC_CHILD` set), which binds a socket on
//! 127.0.0.1, prints one `VINC-READY <ticket>` line and serves until its stdin closes.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::zombie_processes,
    clippy::useless_conversion,
    clippy::manual_assert_eq,
    clippy::items_after_statements,
    dead_code,
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

use std::collections::VecDeque;
use std::future::Future;
use std::io::{BufRead, BufReader, Read};
use std::net::SocketAddr;
use std::pin::Pin;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Condvar, Mutex};
use std::task::{Context, Poll, Wake, Waker};
use std::thread;
use std::time::Duration;

use vinc::{Connection, NodeAddr, Protocol, RecvStream, SendStream, Task, Vinc};
use vinc_tests::SplitMix64;

pub const ECHO: &[u8] = b"t/echo";
pub const SINK: &[u8] = b"t/sink";
pub const GEN: &[u8] = b"t/gen";

pub fn lo() -> SocketAddr {
    ([127, 0, 0, 1], 0).into()
}

/// Abort the process if a test hangs: a stuck await must fail loudly, not run into the harness timeout.
pub fn watchdog(secs: u64) {
    thread::spawn(move || {
        thread::sleep(Duration::from_secs(secs));
        eprintln!("watchdog: the test did not finish in {secs} s");
        std::process::exit(101);
    });
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

// ---- the executor ----

struct Cell {
    fut: Mutex<Option<Pin<Box<dyn Future<Output = ()> + Send>>>>,
    exec: Arc<ExecInner>,
}

struct ExecInner {
    queue: Mutex<VecDeque<Arc<Cell>>>,
    cv: Condvar,
}

impl Wake for Cell {
    fn wake(self: Arc<Self>) {
        self.exec.queue.lock().unwrap().push_back(Arc::clone(&self));
        self.exec.cv.notify_one();
    }
}

/// A std-only executor: `workers` threads poll spawned tasks; `block_on` parks the calling thread.
#[derive(Clone)]
pub struct Exec(Arc<ExecInner>);

impl Exec {
    pub fn new(workers: usize) -> Self {
        let inner = Arc::new(ExecInner {
            queue: Mutex::new(VecDeque::new()),
            cv: Condvar::new(),
        });
        for _ in 0..workers {
            let inner = Arc::clone(&inner);
            thread::spawn(move || {
                loop {
                    let cell = {
                        let mut q = inner.queue.lock().unwrap();
                        loop {
                            if let Some(c) = q.pop_front() {
                                break c;
                            }
                            q = inner.cv.wait(q).unwrap();
                        }
                    };
                    let waker = Waker::from(Arc::clone(&cell));
                    let mut cx = Context::from_waker(&waker);
                    let mut slot = cell.fut.lock().unwrap();
                    if let Some(mut f) = slot.take()
                        && f.as_mut().poll(&mut cx).is_pending()
                    {
                        *slot = Some(f);
                    }
                }
            });
        }
        Self(inner)
    }

    pub fn spawn_task(&self, f: impl Future<Output = ()> + Send + 'static) {
        let cell = Arc::new(Cell {
            fut: Mutex::new(Some(Box::pin(f))),
            exec: Arc::clone(&self.0),
        });
        cell.wake();
    }

    pub fn block_on<T: Send + 'static>(&self, f: impl Future<Output = T> + Send + 'static) -> T {
        let out = Arc::new((Mutex::new(None), Condvar::new()));
        let o = Arc::clone(&out);
        self.spawn_task(async move {
            let v = f.await;
            *o.0.lock().unwrap() = Some(v);
            o.1.notify_all();
        });
        let mut g = out.0.lock().unwrap();
        loop {
            if let Some(v) = g.take() {
                return v;
            }
            g = out.1.wait(g).unwrap();
        }
    }
}

impl vinc::Spawn for Exec {
    fn spawn(&self, task: Task) {
        self.spawn_task(task);
    }
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
        thread::spawn(move || {
            vinc::block_on(async move {
                match alpn.as_slice() {
                    ECHO => echo_stream(tx, rx).await,
                    SINK => sink_stream(tx, rx).await,
                    _ => gen_stream(tx, rx).await,
                }
            });
        });
    }
}

pub struct Svc(pub &'static [u8]);

impl Protocol for Svc {
    fn alpn(&self) -> &'static [u8] {
        self.0
    }

    fn serve(self: Arc<Self>, conn: Connection) -> Task {
        Box::pin(serve_conn(conn))
    }
}

// ---- the child process ----

pub fn is_child() -> bool {
    std::env::var("VINC_CHILD").is_ok()
}

/// The peer process: serve until stdin closes. `async_mode` serves through registered protocols on a test executor,
/// otherwise through the blocking accept loop.
pub fn run_child(async_mode: bool) {
    watchdog(300);
    let builder = Vinc::builder().seed(&[0x5A; 32]).unwrap().bind_addr(lo());
    let ep = if async_mode {
        let exec = Exec::new(2);
        let ep = builder.spawn_on(exec.clone()).unwrap();
        let e2 = ep.clone();
        exec.block_on(async move {
            for a in [ECHO, SINK, GEN] {
                e2.register(Arc::new(Svc(a))).await.unwrap();
            }
        });
        ep
    } else {
        let ep = builder.alpn(ECHO).alpn(SINK).alpn(GEN).bind_blocking().unwrap();
        let b = ep.blocking();
        thread::spawn(move || {
            while let Some((_, _, conn)) = b.accept() {
                thread::spawn(move || vinc::block_on(serve_conn(conn.as_async().clone())));
            }
        });
        ep
    };
    println!("VINC-READY {}", ep.addr().ticket());
    let mut sink = Vec::new();
    let _ = std::io::stdin().read_to_end(&mut sink);
}

pub struct Peer {
    pub child: Child,
    pub addr: NodeAddr,
}

impl Drop for Peer {
    fn drop(&mut self) {
        drop(self.child.stdin.take());
        let _ = self.child.wait();
    }
}

/// Start the test binary again as the peer process, running the test function `name`.
pub fn spawn_peer(name: &str) -> Peer {
    let exe = std::env::current_exe().unwrap();
    let mut child = Command::new(exe)
        .args(["--exact", name, "--nocapture"])
        .env("VINC_CHILD", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut lines = BufReader::new(child.stdout.take().unwrap()).lines();
    loop {
        let line = lines.next().expect("the peer exited before it was ready").unwrap();
        if let Some(t) = line.strip_prefix("VINC-READY ") {
            let addr = NodeAddr::parse(t).unwrap();
            thread::spawn(move || for _ in lines {});
            return Peer { child, addr };
        }
    }
}

/// Poll all of `futs` together until each is done; the outputs come back in order.
pub async fn join_all<T>(mut futs: Vec<Pin<Box<dyn Future<Output = T> + Send>>>) -> Vec<T> {
    let mut out: Vec<Option<T>> = futs.iter().map(|_| None).collect();
    std::future::poll_fn(|cx| {
        let mut pending = false;
        for (f, o) in futs.iter_mut().zip(out.iter_mut()) {
            if o.is_none() {
                match f.as_mut().poll(cx) {
                    Poll::Ready(v) => *o = Some(v),
                    Poll::Pending => pending = true,
                }
            }
        }
        if pending { Poll::Pending } else { Poll::Ready(()) }
    })
    .await;
    out.into_iter().map(Option::unwrap).collect()
}
