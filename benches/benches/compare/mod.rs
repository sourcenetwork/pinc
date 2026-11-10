//! The shared harness of the comparison benches (`compare_vinc`, `compare_iroh`, `compare_libp2p`).
//!
//! One library is measured per binary, and a binary is either the server or the client of a scenario:
//!
//! - `<bin> server [--count-allocs]` binds on 127.0.0.1, prints `ADDR <text>` and serves until it is killed.
//! - `<bin> client <addr> <scenario> [numbers]` runs one scenario against it and prints one JSON line per result.
//!
//! The wire protocol is the same for every library: a bidirectional stream starts with a mode byte. `H` is answered
//! with `k` (the first byte of a connection), `S` is a sink that answers the byte count, `E` echoes everything it reads
//! until the end of the stream, and `T` answers the server's own resource counters (resident memory, CPU time,
//! allocations) so the client can read what the server paid for a phase. The scenarios are written once against the
//! [`Lib`] trait; each library file only maps its own endpoint, connection and stream types onto it.
//!
//! Invariants: nothing here is specific to one library; a number is printed only when it was measured in this run;
//! a failure is counted and printed, never dropped.

#![allow(unreachable_pub, dead_code, unsafe_code)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::future::Future;
use std::io;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
use std::time::{Duration, Instant};

use futures::StreamExt;
use futures::channel::mpsc;

/// The chunk every library moves bulk data in.
pub const CHUNK: usize = 64 * 1024;

/// A global allocator that counts calls and bytes once [`count_allocs`] turned counting on.
pub struct Counting;

static ENABLED: AtomicBool = AtomicBool::new(false);
static ALLOCS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);

fn bump(size: usize) {
    if ENABLED.load(Relaxed) {
        ALLOCS.fetch_add(1, Relaxed);
        BYTES.fetch_add(size as u64, Relaxed);
    }
}

// SAFETY: every method forwards to the system allocator with the arguments it was given.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        bump(l.size());
        unsafe { System.alloc(l) }
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        bump(l.size());
        unsafe { System.alloc_zeroed(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        bump(new);
        unsafe { System.realloc(p, l, new) }
    }
}

/// Turn allocation counting on for the rest of the process.
pub fn count_allocs() {
    ENABLED.store(true, Relaxed);
}

/// What one process has used so far.
#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    /// Resident memory in KiB.
    pub rss_kb: u64,
    /// User plus system CPU time in clock ticks (the kernel counts 100 per second).
    pub cpu_ticks: u64,
    /// Allocation calls since counting was turned on.
    pub allocs: u64,
    /// Bytes asked of the allocator since counting was turned on.
    pub alloc_bytes: u64,
}

impl Stats {
    /// Read this process.
    pub fn now() -> Self {
        let rss_kb = std::fs::read_to_string("/proc/self/status")
            .ok()
            .and_then(|s| {
                s.lines()
                    .find_map(|l| l.strip_prefix("VmRSS:"))
                    .and_then(|v| v.split_whitespace().next()?.parse().ok())
            })
            .unwrap_or(0);
        let cpu_ticks = std::fs::read_to_string("/proc/self/stat")
            .ok()
            .and_then(|s| {
                // After the closing parenthesis of the command name: state is field 3, utime 14 and stime 15.
                let rest = s.get(s.rfind(')')? + 2..)?;
                let f: Vec<&str> = rest.split_whitespace().collect();
                Some(f.get(11)?.parse::<u64>().ok()? + f.get(12)?.parse::<u64>().ok()?)
            })
            .unwrap_or(0);
        Self {
            rss_kb,
            cpu_ticks,
            allocs: ALLOCS.load(Relaxed),
            alloc_bytes: BYTES.load(Relaxed),
        }
    }

    fn to_bytes(self) -> [u8; 32] {
        let mut b = [0u8; 32];
        for (c, v) in b
            .chunks_mut(8)
            .zip([self.rss_kb, self.cpu_ticks, self.allocs, self.alloc_bytes])
        {
            c.copy_from_slice(&v.to_le_bytes());
        }
        b
    }

    fn from_bytes(b: &[u8; 32]) -> Self {
        let v: Vec<u64> = b
            .chunks(8)
            .map(|c| u64::from_le_bytes(c.try_into().unwrap_or([0; 8])))
            .collect();
        Self {
            rss_kb: v[0],
            cpu_ticks: v[1],
            allocs: v[2],
            alloc_bytes: v[3],
        }
    }

    /// CPU seconds between two readings.
    pub fn cpu_secs_since(self, before: Self) -> f64 {
        self.cpu_ticks.saturating_sub(before.cpu_ticks) as f64 / 100.0
    }
}

/// One JSON line of results.
pub struct Rec(String);

impl Rec {
    /// Start a line for `lib` and `scenario`.
    pub fn new(lib: &str, scenario: &str) -> Self {
        Self(format!("{{\"lib\":\"{lib}\",\"scenario\":\"{scenario}\""))
    }
    /// Add a text field (no quotes or backslashes in `v`).
    pub fn s(mut self, k: &str, v: &str) -> Self {
        self.0
            .push_str(&format!(",\"{k}\":\"{}\"", v.replace(['"', '\\', '\n'], "'")));
        self
    }
    /// Add a number field; a number that is not finite is written as null.
    pub fn n(mut self, k: &str, v: f64) -> Self {
        if v.is_finite() {
            self.0.push_str(&format!(",\"{k}\":{v:.4}"));
        } else {
            self.0.push_str(&format!(",\"{k}\":null"));
        }
        self
    }
    /// Print the line.
    pub fn emit(self) {
        println!("{}}}", self.0);
    }
}

/// The send half of a stream.
pub trait Tx: 'static {
    /// Write all of `b`.
    fn write_all(&mut self, b: &[u8]) -> impl Future<Output = io::Result<()>>;
    /// End the send half.
    fn finish(&mut self) -> impl Future<Output = io::Result<()>>;
}

/// The receive half of a stream.
pub trait Rx: 'static {
    /// Read into `b`: the byte count, 0 at the end of the stream.
    fn read(&mut self, b: &mut [u8]) -> impl Future<Output = io::Result<usize>>;
}

/// Fill `b` or fail.
pub async fn read_exact<R: Rx>(r: &mut R, mut b: &mut [u8]) -> io::Result<()> {
    while !b.is_empty() {
        let n = r.read(b).await?;
        if n == 0 {
            return Err(io::ErrorKind::UnexpectedEof.into());
        }
        b = &mut b[n..];
    }
    Ok(())
}

/// A library under test, mapped onto what the scenarios need.
pub trait Lib: Sized + 'static {
    /// The name in the results.
    fn name() -> &'static str;
    /// Whether the library resumes a connection with data in the first flight.
    const RESUMES: bool;
    /// An endpoint (a socket, an identity and the library's state).
    type Ep: 'static;
    /// An established connection.
    type Conn: Clone + 'static;
    /// The send half of a stream.
    type Tx: Tx;
    /// The receive half of a stream.
    type Rx: Rx;

    /// Run `f` to the end on the library's runtime.
    fn run<T>(f: impl Future<Output = T>) -> T;
    /// Start `f` on the runtime.
    fn spawn(f: impl Future<Output = ()> + 'static);
    /// Wait.
    fn sleep(d: Duration) -> impl Future<Output = ()>;
    /// Bind a server on loopback, start serving [`handle`] on every stream, return its address as text.
    fn serve() -> impl Future<Output = io::Result<String>>;
    /// A fresh client endpoint: new identity, no tickets, no cached session.
    fn client() -> impl Future<Output = io::Result<Self::Ep>>;
    /// Dial `addr`.
    fn connect(ep: &Self::Ep, addr: &str) -> impl Future<Output = io::Result<Self::Conn>>;
    /// Open a bidirectional stream.
    fn open(conn: &Self::Conn) -> impl Future<Output = io::Result<(Self::Tx, Self::Rx)>>;
    /// Close one connection.
    fn close(ep: &Self::Ep, conn: &Self::Conn) -> impl Future<Output = ()>;
    /// Stop an endpoint and free what it holds.
    fn shutdown(ep: Self::Ep) -> impl Future<Output = ()>;
    /// Dial `addr` and exchange the first byte; `resumed` asks for the library's resumption path when it has one.
    fn hello(ep: &Self::Ep, addr: &str, resumed: bool) -> impl Future<Output = io::Result<Self::Conn>> {
        let _ = resumed;
        async move {
            let c = Self::connect(ep, addr).await?;
            say_hello::<Self>(&c).await?;
            Ok(c)
        }
    }
    /// A line about the library's state after a setup scenario (for example how many resumptions were accepted).
    fn note() -> String {
        String::new()
    }
}

/// The first byte of a connection: send `H`, wait for `k`.
pub async fn say_hello<L: Lib>(c: &L::Conn) -> io::Result<()> {
    let (mut tx, mut rx) = L::open(c).await?;
    tx.write_all(b"H").await?;
    read_exact(&mut rx, &mut [0u8; 1]).await
}

/// Serve one stream by its mode byte.
///
/// # Errors
/// The error of the stream.
pub async fn handle<T: Tx, R: Rx>(mut tx: T, mut rx: R) -> io::Result<()> {
    let mut mode = [0u8; 1];
    read_exact(&mut rx, &mut mode).await?;
    match mode[0] {
        b'H' => {
            tx.write_all(b"k").await?;
            tx.finish().await
        }
        b'T' => {
            tx.write_all(&Stats::now().to_bytes()).await?;
            tx.finish().await
        }
        b'S' => {
            let mut buf = vec![0u8; CHUNK];
            let mut total = 0u64;
            loop {
                let n = rx.read(&mut buf).await?;
                if n == 0 {
                    break;
                }
                total += n as u64;
            }
            tx.write_all(&total.to_le_bytes()).await?;
            tx.finish().await
        }
        b'E' => {
            let mut buf = vec![0u8; CHUNK];
            loop {
                let n = rx.read(&mut buf).await?;
                if n == 0 {
                    break;
                }
                tx.write_all(&buf[..n]).await?;
            }
            tx.finish().await
        }
        _ => Ok(()),
    }
}

/// The server's counters, asked over the connection.
async fn server_stats<L: Lib>(c: &L::Conn) -> io::Result<Stats> {
    let (mut tx, mut rx) = L::open(c).await?;
    tx.write_all(b"T").await?;
    let mut b = [0u8; 32];
    read_exact(&mut rx, &mut b).await?;
    Ok(Stats::from_bytes(&b))
}

/// Send `total` bytes on a new stream to the sink and wait for its count.
async fn upload<L: Lib>(c: &L::Conn, total: u64) -> io::Result<()> {
    let (mut tx, mut rx) = L::open(c).await?;
    tx.write_all(b"S").await?;
    let chunk = vec![0x5au8; CHUNK];
    let mut left = total;
    while left > 0 {
        let n = left.min(CHUNK as u64) as usize;
        tx.write_all(&chunk[..n]).await?;
        left -= n as u64;
    }
    tx.finish().await?;
    let mut ack = [0u8; 8];
    read_exact(&mut rx, &mut ack).await?;
    if u64::from_le_bytes(ack) == total {
        Ok(())
    } else {
        Err(io::Error::other("the sink counted a different number of bytes"))
    }
}

fn pct(v: &[f64], p: f64) -> f64 {
    v.get(((v.len() as f64 * p) as usize).min(v.len().saturating_sub(1)))
        .copied()
        .unwrap_or(f64::NAN)
}

fn us(d: Duration) -> f64 {
    d.as_secs_f64() * 1e6
}

/// Time to the first byte of a new connection, or of a resumed one, over `n` fresh endpoints.
async fn setup<L: Lib>(addr: &str, n: usize, resumed: bool) {
    let name = if resumed { "resume" } else { "setup" };
    if resumed && !L::RESUMES {
        Rec::new(L::name(), name)
            .s("status", "not measured: the library has no resumption with early data")
            .emit();
        return;
    }
    let (mut v, mut failed, mut why) = (Vec::with_capacity(n), 0u32, String::new());
    for _ in 0..n {
        let ep = match L::client().await {
            Ok(ep) => ep,
            Err(e) => {
                failed += 1;
                why = e.to_string();
                continue;
            }
        };
        if resumed {
            if let Ok(c) = L::hello(&ep, addr, false).await {
                L::close(&ep, &c).await;
            }
            // The tickets of the first connection arrive after its handshake.
            L::sleep(Duration::from_millis(50)).await;
        }
        let t = Instant::now();
        match L::hello(&ep, addr, resumed).await {
            Ok(c) => {
                v.push(us(t.elapsed()));
                L::close(&ep, &c).await;
            }
            Err(e) => {
                failed += 1;
                why = e.to_string();
            }
        }
        L::shutdown(ep).await;
    }
    v.sort_by(f64::total_cmp);
    Rec::new(L::name(), name)
        .n("samples", v.len() as f64)
        .n("failed", f64::from(failed))
        .n("min_us", pct(&v, 0.0))
        .n("p50_us", pct(&v, 0.5))
        .n("p99_us", pct(&v, 0.99))
        .n("mean_us", v.iter().sum::<f64>() / v.len() as f64)
        .s("note", &if resumed { L::note() } else { String::new() })
        .s("last_error", &why)
        .emit();
}

/// Upload `total` bytes over `streams` concurrent streams of one connection.
async fn throughput<L: Lib>(addr: &str, total: u64, streams: usize) {
    let name = format!("throughput_{streams}s");
    let Ok(ep) = L::client().await else {
        Rec::new(L::name(), &name).s("status", "failed: no endpoint").emit();
        return;
    };
    let Ok(conn) = L::hello(&ep, addr, false).await else {
        Rec::new(L::name(), &name).s("status", "failed: no connection").emit();
        return;
    };
    let Ok(s0) = server_stats::<L>(&conn).await else {
        Rec::new(L::name(), &name)
            .s("status", "failed: no server counters")
            .emit();
        return;
    };
    let c0 = Stats::now();
    let t = Instant::now();
    let (done, mut results) = mpsc::unbounded();
    for _ in 0..streams {
        let (c, done) = (conn.clone(), done.clone());
        L::spawn(async move {
            let _ = done.unbounded_send(upload::<L>(&c, total / streams as u64).await.is_ok());
        });
    }
    drop(done);
    let mut ok = 0;
    while let Some(r) = results.next().await {
        ok += usize::from(r);
    }
    let secs = t.elapsed().as_secs_f64();
    let (c1, s1) = (Stats::now(), server_stats::<L>(&conn).await.unwrap_or(s0));
    let moved = (total / streams as u64) * ok as u64;
    let (cc, sc) = (c1.cpu_secs_since(c0), s1.cpu_secs_since(s0));
    Rec::new(L::name(), &name)
        .n("bytes", moved as f64)
        .n("streams_ok", ok as f64)
        .n("streams", streams as f64)
        .n("secs", secs)
        .n("mib_s", moved as f64 / secs / 1048576.0)
        .n("client_cpu_s", cc)
        .n("server_cpu_s", sc)
        .n("cpu_ns_per_byte", (cc + sc) * 1e9 / moved as f64)
        .emit();
    L::close(&ep, &conn).await;
    L::shutdown(ep).await;
}

/// `count` request and response round trips of `size` bytes on one echo stream.
async fn latency<L: Lib>(addr: &str, size: usize, count: usize) {
    let name = format!("latency_{size}b");
    let Ok(ep) = L::client().await else {
        Rec::new(L::name(), &name).s("status", "failed: no endpoint").emit();
        return;
    };
    let Ok(conn) = L::hello(&ep, addr, false).await else {
        Rec::new(L::name(), &name).s("status", "failed: no connection").emit();
        return;
    };
    let Ok((mut tx, mut rx)) = L::open(&conn).await else {
        Rec::new(L::name(), &name).s("status", "failed: no stream").emit();
        return;
    };
    let (req, mut resp) = (vec![0xa5u8; size], vec![0u8; size]);
    let ok = async {
        tx.write_all(b"E").await?;
        for _ in 0..count.min(1000) {
            tx.write_all(&req).await?;
            read_exact(&mut rx, &mut resp).await?;
        }
        io::Result::Ok(())
    }
    .await;
    if let Err(e) = ok {
        Rec::new(L::name(), &name)
            .s("status", &format!("failed in warm-up: {e}"))
            .emit();
        return;
    }
    let (s0, c0) = (server_stats::<L>(&conn).await.unwrap_or_default(), Stats::now());
    let mut v = Vec::with_capacity(count);
    let wall = Instant::now();
    let mut err = None;
    for _ in 0..count {
        let t = Instant::now();
        let r = async {
            tx.write_all(&req).await?;
            read_exact(&mut rx, &mut resp).await
        }
        .await;
        match r {
            Ok(()) => v.push(us(t.elapsed())),
            Err(e) => {
                err = Some(e.to_string());
                break;
            }
        }
    }
    let secs = wall.elapsed().as_secs_f64();
    let (c1, s1) = (Stats::now(), server_stats::<L>(&conn).await.unwrap_or(s0));
    v.sort_by(f64::total_cmp);
    let n = v.len().max(1) as f64;
    let mut r = Rec::new(L::name(), &name)
        .n("round_trips", v.len() as f64)
        .n("size", size as f64)
        .n("min_us", pct(&v, 0.0))
        .n("p50_us", pct(&v, 0.5))
        .n("p99_us", pct(&v, 0.99))
        .n("p999_us", pct(&v, 0.999))
        .n("mean_us", v.iter().sum::<f64>() / n)
        .n("rate_per_s", n / secs)
        .n("client_cpu_us_per_rt", c1.cpu_secs_since(c0) * 1e6 / n)
        .n("server_cpu_us_per_rt", s1.cpu_secs_since(s0) * 1e6 / n)
        .n("client_allocs_per_rt", c1.allocs.saturating_sub(c0.allocs) as f64 / n)
        .n("server_allocs_per_rt", s1.allocs.saturating_sub(s0.allocs) as f64 / n);
    if let Some(e) = err {
        r = r.s("status", &format!("stopped early: {e}"));
    }
    r.emit();
    drop((tx, rx));
    L::close(&ep, &conn).await;
    L::shutdown(ep).await;
}

/// Allocations per bulk message: upload `total` bytes in [`CHUNK`] writes with counting on at both ends.
async fn bulk_allocs<L: Lib>(addr: &str, total: u64) {
    let Ok(ep) = L::client().await else { return };
    let Ok(conn) = L::hello(&ep, addr, false).await else {
        Rec::new(L::name(), "allocs_bulk")
            .s("status", "failed: no connection")
            .emit();
        return;
    };
    let (s0, c0) = (server_stats::<L>(&conn).await.unwrap_or_default(), Stats::now());
    let ok = upload::<L>(&conn, total).await.is_ok();
    let (c1, s1) = (Stats::now(), server_stats::<L>(&conn).await.unwrap_or(s0));
    let msgs = (total / CHUNK as u64).max(1) as f64;
    Rec::new(L::name(), "allocs_bulk")
        .n("messages", msgs)
        .n(
            "client_allocs_per_msg",
            c1.allocs.saturating_sub(c0.allocs) as f64 / msgs,
        )
        .n(
            "server_allocs_per_msg",
            s1.allocs.saturating_sub(s0.allocs) as f64 / msgs,
        )
        .n(
            "client_alloc_bytes_per_msg",
            c1.alloc_bytes.saturating_sub(c0.alloc_bytes) as f64 / msgs,
        )
        .n(
            "server_alloc_bytes_per_msg",
            s1.alloc_bytes.saturating_sub(s0.alloc_bytes) as f64 / msgs,
        )
        .s("status", if ok { "ok" } else { "upload failed" })
        .emit();
    L::close(&ep, &conn).await;
    L::shutdown(ep).await;
}

/// `n` clients, each with its own endpoint, connect at once and move `each` bytes; the server's memory and CPU are read
/// while every connection is still open.
async fn many<L: Lib>(addr: &str, n: usize, each: u64) {
    let Ok(ctl_ep) = L::client().await else { return };
    let Ok(ctl) = L::hello(&ctl_ep, addr, false).await else {
        Rec::new(L::name(), "many")
            .s("status", "failed: no control connection")
            .emit();
        return;
    };
    let s_base = server_stats::<L>(&ctl).await.unwrap_or_default();
    let c_base = Stats::now();
    let mut eps = Vec::with_capacity(n);
    let mut no_endpoint = 0u32;
    for _ in 0..n {
        match L::client().await {
            Ok(e) => eps.push(e),
            Err(_) => no_endpoint += 1,
        }
    }
    let c_made = Stats::now();
    let t = Instant::now();
    let (done, mut results) = mpsc::unbounded();
    for ep in eps {
        let (addr, done) = (addr.to_owned(), done.clone());
        L::spawn(async move {
            let r = async {
                let c = L::hello(&ep, &addr, false).await?;
                let up = t.elapsed();
                upload::<L>(&c, each).await?;
                io::Result::Ok((up, c))
            }
            .await;
            let _ = done.unbounded_send((ep, r.map_err(|e| e.to_string())));
        });
    }
    drop(done);
    let (mut held, mut up, mut failed, mut why) = (Vec::with_capacity(n), Vec::new(), no_endpoint, String::new());
    while let Some((ep, r)) = results.next().await {
        match r {
            Ok((u, c)) => {
                up.push(us(u));
                held.push((ep, c));
            }
            Err(e) => {
                failed += 1;
                why = e;
            }
        }
    }
    let secs = t.elapsed().as_secs_f64();
    // Let the memory settle before the readings.
    L::sleep(Duration::from_millis(500)).await;
    let (s1, c1) = (server_stats::<L>(&ctl).await.unwrap_or(s_base), Stats::now());
    up.sort_by(f64::total_cmp);
    let ok = held.len() as f64;
    Rec::new(L::name(), "many")
        .n("requested", n as f64)
        .n("connected_and_moved", ok)
        .n("failed", f64::from(failed))
        .n("all_done_s", secs)
        .n("first_byte_p50_ms", pct(&up, 0.5) / 1e3)
        .n("first_byte_p99_ms", pct(&up, 0.99) / 1e3)
        .n("server_rss_base_mib", s_base.rss_kb as f64 / 1024.0)
        .n("server_rss_mib", s1.rss_kb as f64 / 1024.0)
        .n(
            "server_kib_per_conn",
            s1.rss_kb.saturating_sub(s_base.rss_kb) as f64 / ok.max(1.0),
        )
        .n(
            "client_kib_per_conn",
            c1.rss_kb.saturating_sub(c_made.rss_kb) as f64 / ok.max(1.0),
        )
        .n("client_rss_before_mib", c_base.rss_kb as f64 / 1024.0)
        .n("server_cpu_s", s1.cpu_secs_since(s_base))
        .n("client_cpu_s", c1.cpu_secs_since(c_made))
        .s("last_error", &why)
        .emit();
    for (ep, c) in held {
        L::close(&ep, &c).await;
        L::shutdown(ep).await;
    }
    L::shutdown(ctl_ep).await;
}

static VARIANT: OnceLock<String> = OnceLock::new();

/// The variant of the library named on the command line (`quic` or `tcp` for rust-libp2p), `""` if none.
pub fn variant() -> &'static str {
    VARIANT.get().map_or("", String::as_str)
}

fn num<T: std::str::FromStr>(a: &[String], i: usize, default: T) -> T {
    a.get(i).and_then(|s| s.parse().ok()).unwrap_or(default)
}

/// The entry point of every comparison binary.
pub fn main<L: Lib>() {
    let mut args: Vec<String> = std::env::args().skip(1).filter(|a| a != "--bench").collect();
    if let Some(i) = args.iter().position(|a| a.starts_with("--variant=")) {
        let _ = VARIANT.set(args.remove(i).trim_start_matches("--variant=").to_owned());
    }
    if args.iter().any(|a| a == "--count-allocs") {
        count_allocs();
    }
    args.retain(|a| a != "--count-allocs");
    match args.first().map(String::as_str) {
        Some("server") => L::run(async {
            match L::serve().await {
                Ok(addr) => {
                    println!("ADDR {addr}");
                    futures::future::pending::<()>().await;
                }
                Err(e) => {
                    eprintln!("the server did not start: {e}");
                    std::process::exit(2);
                }
            }
        }),
        Some("client") if args.len() >= 3 => {
            let addr = args[1].clone();
            let (a, scenario) = (args[3..].to_vec(), args[2].clone());
            L::run(async move {
                let a = &a[..];
                match scenario.as_str() {
                    "setup" => setup::<L>(&addr, num(a, 0, 200), false).await,
                    "resume" => setup::<L>(&addr, num(a, 0, 200), true).await,
                    "throughput" => throughput::<L>(&addr, num(a, 0, 1 << 30), num(a, 1, 1)).await,
                    "latency" => latency::<L>(&addr, num(a, 0, 64), num(a, 1, 100_000)).await,
                    "allocs" => {
                        count_allocs();
                        latency::<L>(&addr, 64, num(a, 0, 20_000)).await;
                        bulk_allocs::<L>(&addr, num(a, 1, 64 << 20)).await;
                    }
                    "many" => many::<L>(&addr, num(a, 0, 1000), num(a, 1, 64 * 1024)).await,
                    other => {
                        eprintln!("unknown scenario {other}");
                        std::process::exit(2);
                    }
                }
            });
        }
        _ => {
            eprintln!(
                "usage: server [--count-allocs] | client <addr> <setup|resume|throughput|latency|allocs|many> [numbers]"
            );
            std::process::exit(2);
        }
    }
}
