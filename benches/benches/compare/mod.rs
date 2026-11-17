//! The shared harness of the comparison benches (`compare_vinc`, `compare_iroh`, `compare_libp2p`), also built into the
//! distributed harness's node program, which runs the same scenarios between the nodes of an emulated or real network.
//!
//! One library is measured per process, and a process is either the server or the client of a scenario:
//!
//! - `server [--count-allocs]` binds on `VINC_BENCH_BIND` (an IP address; 127.0.0.1 when unset), prints `ADDR <text>`
//!   and serves until it is killed.
//! - `client <addr> <scenario> [numbers]` runs one scenario against it and prints one JSON line per result.
//!
//! `--endpoints=per-core` (or `VINC_BENCH_ENDPOINTS=per-core`; the default is `1`) asks a library that can for one
//! endpoint on every worker of its runtime: the server serves on all of them and the `many` test spreads its clients
//! over them. Every result line of a per-core process says so (`endpoints`: `per-core`; a line without it ran on one
//! endpoint); the default code path is untouched, and the other tests run on one endpoint either way.
//!
//! `--reading=undriven|driven` (the default is `undriven`; only the argument names it) is how the `many` test reads
//! memory: `undriven` leaves VINC's client endpoints undriven and settles 500 ms, as the row was read before; `driven`
//! runs every client endpoint's own driver while the connections are open (VINC's `run()`; the other libraries always
//! do) and settles 1.5 s before reading. Every `many` line says which (`reading`).
//!
//! The wire protocol is the same for every library: a bidirectional stream starts with a mode byte. `H` is answered
//! with `k` (the first byte of a connection), `S` is a sink that answers the byte count, `E` echoes everything it reads
//! until the end of the stream (the `requests` scenario opens one such stream per request), and `T` answers the
//! server's own resource counters (resident memory, CPU time, allocations) so the client can read what the server paid
//! for a phase. `B` is `T` after the server has reset its peak resident memory, so a peak read later starts from that
//! point (the peak is 0 when it could not be reset). The scenarios are written once against the [`Lib`] trait; each
//! library's module (`vinc`, `iroh`, `libp2p`) only maps its own endpoint, connection and stream types onto it.
//!
//! Invariants: nothing here is specific to one library; a number is printed only when it was measured in this run;
//! a failure is counted and printed, never dropped.

// Measurement code: counters become floats for the report, and argument and buffer positions are checked by the
// harness that passes them.
#![allow(
    unreachable_pub,
    dead_code,
    unsafe_code,
    clippy::indexing_slicing,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::unreadable_literal,
    clippy::format_push_string
)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::future::Future;
use std::io;
use std::net::{IpAddr, Ipv4Addr};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering::Relaxed};
use std::time::{Duration, Instant};

use futures::StreamExt;
use futures::channel::mpsc;

pub mod iroh;
pub mod libp2p;
mod many;
pub mod vinc;

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

/// The KiB of the line `key` (`VmRSS:`, `VmHWM:`) of a `/proc/<pid>/status` text.
fn parse_status_kb(status: &str, key: &str) -> Option<u64> {
    status
        .lines()
        .find_map(|l| l.strip_prefix(key))
        .and_then(|v| v.split_whitespace().next()?.parse().ok())
}

fn status_kb(key: &str) -> u64 {
    std::fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| parse_status_kb(&s, key))
        .unwrap_or(0)
}

/// This process's resident memory now, in KiB.
pub fn resident_kb() -> u64 {
    status_kb("VmRSS:")
}

/// The most resident memory this process has had, in KiB.
pub fn peak_kb() -> u64 {
    status_kb("VmHWM:")
}

/// Start this process's peak resident memory (`VmHWM`) afresh from its resident memory now; whether the system did it.
pub fn reset_peak() -> bool {
    reset_peak_at("/proc/self/clear_refs")
}

/// [`reset_peak`] through the file at `path` (writing `5` there resets the peak).
fn reset_peak_at(path: &str) -> bool {
    std::fs::write(path, "5").is_ok()
}

/// What one process has used so far.
#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    /// Resident memory in KiB.
    pub rss_kb: u64,
    /// The most resident memory the process has had, in KiB (`VmHWM`); 0 when it was not read (or, in the answer to a
    /// base request, could not be reset).
    pub peak_kb: u64,
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
        let (rss_kb, peak_kb) = (resident_kb(), peak_kb());
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
            peak_kb,
            cpu_ticks,
            allocs: ALLOCS.load(Relaxed),
            alloc_bytes: BYTES.load(Relaxed),
        }
    }

    fn to_bytes(self) -> [u8; 40] {
        let mut b = [0u8; 40];
        for (c, v) in b
            .chunks_mut(8)
            .zip([self.rss_kb, self.cpu_ticks, self.allocs, self.alloc_bytes, self.peak_kb])
        {
            c.copy_from_slice(&v.to_le_bytes());
        }
        b
    }

    fn from_bytes(b: &[u8; 40]) -> Self {
        let v: Vec<u64> = b
            .chunks(8)
            .map(|c| u64::from_le_bytes(c.try_into().unwrap_or([0; 8])))
            .collect();
        Self {
            rss_kb: v[0],
            cpu_ticks: v[1],
            allocs: v[2],
            alloc_bytes: v[3],
            peak_kb: v[4],
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
        let rec = format!("{{\"lib\":\"{lib}\",\"scenario\":\"{scenario}\"");
        // A line of the default carries nothing new; one of a per-core process says so, so it is never read as the
        // other.
        Self(if per_core() {
            format!("{rec},\"endpoints\":\"per-core\"")
        } else {
            rec
        })
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
    /// Whether the library can run one endpoint on every worker of its runtime (`--endpoints=per-core`).
    const PER_CORE: bool = false;
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
    /// Start the future `make` builds for client `i` of a crowd, or say why it did not start. A library that runs one
    /// endpoint on every worker ([`per_core`]) starts it on worker `i` modulo the workers, where the client's endpoint
    /// is made; the default starts it here, as [`spawn`](Self::spawn) does.
    fn spawn_client<F: Future<Output = ()> + 'static>(
        i: usize,
        make: impl FnOnce() -> F + Send + 'static,
    ) -> io::Result<()> {
        let _ = i;
        Self::spawn(make());
        Ok(())
    }
    /// A client endpoint of the many-connection test: [`client`](Self::client), driven by its own task when the reading
    /// is `driven` for a library whose endpoint needs one (the others always are).
    fn burst_client() -> impl Future<Output = io::Result<Self::Ep>> {
        Self::client()
    }
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
        b'B' => {
            tx.write_all(&base_stats(reset_peak()).to_bytes()).await?;
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

/// The counters of a process whose peak was just reset (`reset`: whether it was): its peak is 0 when it was not, so
/// no one reads an old peak as a new one.
fn base_stats(reset: bool) -> Stats {
    let mut s = Stats::now();
    if !reset {
        s.peak_kb = 0;
    }
    s
}

/// The server's counters, asked over the connection.
async fn server_stats<L: Lib>(c: &L::Conn) -> io::Result<Stats> {
    ask_stats::<L>(c, b'T').await
}

/// The server's counters after it reset its peak memory, asked over the connection.
async fn server_base<L: Lib>(c: &L::Conn) -> io::Result<Stats> {
    ask_stats::<L>(c, b'B').await
}

async fn ask_stats<L: Lib>(c: &L::Conn, mode: u8) -> io::Result<Stats> {
    let (mut tx, mut rx) = L::open(c).await?;
    tx.write_all(&[mode]).await?;
    let mut b = [0u8; 40];
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

/// One request of a request-response protocol: a stream of its own, the request, the end of the send half, the
/// echoed response. Returns how long the stream took to open: the wait for a place among the peer's streams.
async fn request<L: Lib>(c: &L::Conn, req: &[u8], resp: &mut [u8]) -> io::Result<f64> {
    let t = Instant::now();
    let (mut tx, mut rx) = L::open(c).await?;
    let opened = us(t.elapsed());
    tx.write_all(req).await?;
    tx.finish().await?;
    read_exact(&mut rx, resp).await?;
    Ok(opened)
}

/// `count` requests of `size` bytes each way over one connection, `concurrency` in flight at once, each on a stream
/// of its own (as a request-response protocol opens one per request); a latency includes opening the stream.
async fn requests<L: Lib>(addr: &str, size: usize, count: usize, concurrency: usize) {
    let concurrency = concurrency.max(1);
    let name = format!("requests_{size}b_c{concurrency}");
    let Ok(ep) = L::client().await else {
        Rec::new(L::name(), &name).s("status", "failed: no endpoint").emit();
        return;
    };
    let Ok(conn) = L::hello(&ep, addr, false).await else {
        Rec::new(L::name(), &name).s("status", "failed: no connection").emit();
        return;
    };
    let mut req = vec![0xa5u8; size + 1];
    req[0] = b'E';
    let req = &req[..];
    // The requests left to start, shared by the workers, which all run on this one task.
    let left = std::cell::Cell::new(count.min(1000));
    let worker = |conn: L::Conn| {
        let left = &left;
        async move {
            let (mut v, mut failed, mut why) = (Vec::new(), 0u32, None);
            let mut resp = vec![0u8; size];
            while left.get() > 0 {
                left.set(left.get() - 1);
                let t = Instant::now();
                match request::<L>(&conn, req, &mut resp).await {
                    Ok(opened) => v.push((us(t.elapsed()), opened)),
                    Err(e) => {
                        failed += 1;
                        why.get_or_insert_with(|| e.to_string());
                    }
                }
            }
            (v, failed, why)
        }
    };
    // Warm-up: the same mix, unmeasured.
    futures::future::join_all((0..concurrency).map(|_| worker(conn.clone()))).await;
    let (s0, c0) = (server_stats::<L>(&conn).await.unwrap_or_default(), Stats::now());
    left.set(count);
    let wall = Instant::now();
    let done = futures::future::join_all((0..concurrency).map(|_| worker(conn.clone()))).await;
    let secs = wall.elapsed().as_secs_f64();
    let (c1, s1) = (Stats::now(), server_stats::<L>(&conn).await.unwrap_or(s0));
    let (mut v, mut failed, mut why) = (Vec::with_capacity(count), 0u32, None);
    for (lat, f, w) in done {
        v.extend(lat);
        failed += f;
        why = why.or(w);
    }
    // What makes the tail: the slowest hundredth's mean wait to open against its mean time after the open.
    v.sort_by(|a, b| b.0.total_cmp(&a.0));
    let tail = &v[..v.len().div_ceil(100)];
    let tail_n = tail.len().max(1) as f64;
    let tail_open = tail.iter().map(|t| t.1).sum::<f64>() / tail_n;
    let tail_rest = tail.iter().map(|t| t.0 - t.1).sum::<f64>() / tail_n;
    let mut opens: Vec<f64> = v.iter().map(|t| t.1).collect();
    let mut v: Vec<f64> = v.iter().map(|t| t.0).collect();
    v.sort_by(f64::total_cmp);
    opens.sort_by(f64::total_cmp);
    let n = v.len().max(1) as f64;
    let mut r = Rec::new(L::name(), &name)
        .n("requests", v.len() as f64)
        .n("failed", f64::from(failed))
        .n("size", size as f64)
        .n("concurrency", concurrency as f64)
        .n("p50_us", pct(&v, 0.5))
        .n("p99_us", pct(&v, 0.99))
        .n("max_us", pct(&v, 1.0))
        .n("open_p50_us", pct(&opens, 0.5))
        .n("open_p99_us", pct(&opens, 0.99))
        .n("tail_open_us", tail_open)
        .n("tail_after_open_us", tail_rest)
        .n("rate_per_s", n / secs)
        .n("client_cpu_us_per_req", c1.cpu_secs_since(c0) * 1e6 / n)
        .n("server_cpu_us_per_req", s1.cpu_secs_since(s0) * 1e6 / n);
    if let Some(e) = why {
        r = r.s("status", &format!("{failed} requests failed, the first: {e}"));
    }
    r.emit();
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

static DRIVEN: AtomicBool = AtomicBool::new(false);

/// Held by every test that sets `DRIVEN` or `PER_CORE`, so they also pass together in one process.
#[cfg(test)]
pub(crate) static SWITCHES: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The lock on the switches and what they held when it was taken; dropping it puts them back, even after a failed
/// assert.
#[cfg(test)]
pub(crate) struct SwitchGuard {
    found: (bool, bool),
    _one: std::sync::MutexGuard<'static, ()>,
}

#[cfg(test)]
impl SwitchGuard {
    pub(crate) fn hold() -> Self {
        let one = SWITCHES.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        Self {
            found: (PER_CORE.load(Relaxed), DRIVEN.load(Relaxed)),
            _one: one,
        }
    }
}

#[cfg(test)]
impl Drop for SwitchGuard {
    fn drop(&mut self) {
        PER_CORE.store(self.found.0, Relaxed);
        DRIVEN.store(self.found.1, Relaxed);
    }
}

/// Whether the many-connection test reads memory from driven client endpoints rather than undriven ones (the default).
pub fn driven() -> bool {
    DRIVEN.load(Relaxed)
}

/// How the reading is named in the results.
pub fn reading() -> &'static str {
    if driven() { "driven" } else { "undriven" }
}

/// How long the many-connection test lets memory settle before it reads it.
fn settle() -> Duration {
    Duration::from_millis(if driven() { 1500 } else { 500 })
}

/// Whether `v` (the option's text, if given) names the driven reading.
fn parse_reading(v: Option<&str>) -> Result<bool, String> {
    match v {
        None | Some("undriven") => Ok(false),
        Some("driven") => Ok(true),
        Some(other) => Err(format!("the reading is `driven` or `undriven`, not `{other}`")),
    }
}

/// Read the reading option: the `--reading=` argument (removed from `args`), else `undriven`.
fn reading_option(args: &mut Vec<String>) -> Result<(), String> {
    let arg = args
        .iter()
        .position(|a| a.starts_with("--reading="))
        .map(|i| args.remove(i).trim_start_matches("--reading=").to_owned());
    DRIVEN.store(parse_reading(arg.as_deref())?, Relaxed);
    Ok(())
}

static PER_CORE: AtomicBool = AtomicBool::new(false);

/// Whether this process runs one endpoint on every worker of the runtime: the server serves on all of them and the
/// many-connection test spreads its clients over them. Set by `--endpoints=per-core` or `VINC_BENCH_ENDPOINTS=per-core`
/// for a library that can ([`Lib::PER_CORE`]); a runtime with no workers runs one either way.
pub fn per_core() -> bool {
    PER_CORE.load(Relaxed)
}

/// Read the endpoints option: the `--endpoints=` argument (removed from `args`), else `VINC_BENCH_ENDPOINTS`, else `1`.
fn endpoints_option<L: Lib>(args: &mut Vec<String>) -> Result<(), String> {
    let arg = args
        .iter()
        .position(|a| a.starts_with("--endpoints="))
        .map(|i| args.remove(i).trim_start_matches("--endpoints=").to_owned());
    let v = arg.or_else(|| std::env::var("VINC_BENCH_ENDPOINTS").ok());
    match v.as_deref() {
        None | Some("1") => {}
        Some("per-core") => PER_CORE.store(L::PER_CORE, Relaxed),
        Some(other) => return Err(format!("the endpoints are `1` or `per-core`, not `{other}`")),
    }
    Ok(())
}

static VARIANT: OnceLock<String> = OnceLock::new();

/// The variant of the library named on the command line (`quic` or `tcp` for rust-libp2p), `""` if none.
pub fn variant() -> &'static str {
    VARIANT.get().map_or("", String::as_str)
}

fn num<T: std::str::FromStr>(a: &[String], i: usize, default: T) -> T {
    a.get(i).and_then(|s| s.parse().ok()).unwrap_or(default)
}

/// The address every socket of this process binds: `VINC_BENCH_BIND`, loopback when it is not set.
///
/// # Errors
/// The variable is set but is not an IP address.
pub fn bind_ip() -> io::Result<IpAddr> {
    match std::env::var("VINC_BENCH_BIND") {
        Ok(v) => v
            .parse()
            .map_err(|_| io::Error::other(format!("VINC_BENCH_BIND is not an IP address: {v}"))),
        Err(_) => Ok(IpAddr::V4(Ipv4Addr::LOCALHOST)),
    }
}

/// The entry point of every comparison binary.
pub fn main<L: Lib>() {
    run_args::<L>(std::env::args().skip(1).filter(|a| a != "--bench").collect());
}

/// Run the server or the client named by `args` (`server ...` or `client <addr> <scenario> ...`) to the end.
pub fn run_args<L: Lib>(mut args: Vec<String>) {
    if let Some(i) = args.iter().position(|a| a.starts_with("--variant=")) {
        let _ = VARIANT.set(args.remove(i).trim_start_matches("--variant=").to_owned());
    }
    if let Err(e) = endpoints_option::<L>(&mut args).and_then(|()| reading_option(&mut args)) {
        eprintln!("{e}");
        std::process::exit(2);
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
                    "requests" => requests::<L>(&addr, num(a, 0, 512), num(a, 1, 10_000), num(a, 2, 1)).await,
                    "allocs" => {
                        count_allocs();
                        latency::<L>(&addr, 64, num(a, 0, 20_000)).await;
                        bulk_allocs::<L>(&addr, num(a, 1, 64 << 20)).await;
                    }
                    "many" => many::many::<L>(&addr, num(a, 0, 1000), num(a, 1, 64 * 1024)).await,
                    other => {
                        eprintln!("unknown scenario {other}");
                        std::process::exit(2);
                    }
                }
            });
        }
        _ => {
            eprintln!(
                "usage: [--endpoints=1|per-core] [--reading=undriven|driven] server [--count-allocs] \
                 | client <addr> <setup|resume|throughput|latency|requests|allocs|many> [numbers]"
            );
            std::process::exit(2);
        }
    }
}

// The benches have no test harness; these run in the harness crate that includes this module.
#[cfg(test)]
#[allow(unused_imports, clippy::unwrap_used)]
mod tests {
    use super::*;

    #[test]
    fn the_peak_and_the_resident_size_are_read_from_a_status_text() {
        let status = "Name:\tcompare\nVmPeak:\t  900000 kB\nVmHWM:\t  123456 kB\nVmRSS:\t   98765 kB\nThreads:\t4\n";
        assert_eq!(parse_status_kb(status, "VmHWM:"), Some(123_456));
        assert_eq!(parse_status_kb(status, "VmRSS:"), Some(98_765));
        assert_eq!(parse_status_kb(status, "VmSwap:"), None);
        assert_eq!(parse_status_kb("VmHWM:\tmany kB\n", "VmHWM:"), None);
    }

    #[test]
    fn the_reading_is_undriven_by_default_driven_on_request_and_nothing_else() {
        assert_eq!(parse_reading(None), Ok(false));
        assert_eq!(parse_reading(Some("undriven")), Ok(false));
        assert_eq!(parse_reading(Some("driven")), Ok(true));
        assert!(parse_reading(Some("idle")).is_err());
    }

    #[test]
    fn the_reading_argument_is_taken_out_of_the_arguments() {
        let _switches = SwitchGuard::hold();
        let mut args = vec!["--reading=driven".to_owned(), "server".to_owned()];
        assert_eq!(reading_option(&mut args), Ok(()));
        assert_eq!(args, ["server"]);
        assert!(driven());
        let mut bad = vec!["--reading=never".to_owned()];
        assert!(reading_option(&mut bad).is_err());
    }

    #[test]
    fn the_peak_is_reset_by_writing_5_and_a_write_that_fails_says_so() {
        let path = std::env::temp_dir().join(format!("clear_refs_{}", std::process::id()));
        assert!(reset_peak_at(path.to_str().unwrap()));
        assert_eq!(std::fs::read_to_string(&path).unwrap(), "5");
        std::fs::remove_file(&path).unwrap();
        assert!(!reset_peak_at("/no/such/directory/clear_refs"));
    }

    #[test]
    fn a_base_whose_peak_was_not_reset_carries_no_peak() {
        assert_eq!(base_stats(false).peak_kb, 0);
        assert!(base_stats(true).peak_kb > 0);
    }

    #[test]
    fn per_core_is_taken_only_by_a_library_that_can_and_every_line_of_a_per_core_process_says_so() {
        let _switches = SwitchGuard::hold();
        let line = || Rec::new("x", "many").0;
        let mut args = vec!["--endpoints=per-core".to_owned(), "server".to_owned()];
        assert_eq!(endpoints_option::<iroh::Iroh>(&mut args), Ok(()));
        assert_eq!(args, ["server"]);
        assert!(!per_core(), "a library that cannot run per-core runs on one endpoint");
        assert!(!line().contains("endpoints"));
        assert_eq!(
            endpoints_option::<vinc::Vinc1>(&mut vec!["--endpoints=1".to_owned()]),
            Ok(())
        );
        assert!(!per_core());
        assert_eq!(
            endpoints_option::<vinc::Vinc1>(&mut vec!["--endpoints=per-core".to_owned()]),
            Ok(())
        );
        assert!(per_core());
        assert!(line().contains("\"endpoints\":\"per-core\""), "{}", line());
        assert!(endpoints_option::<vinc::Vinc1>(&mut vec!["--endpoints=two".to_owned()]).is_err());
    }
}
