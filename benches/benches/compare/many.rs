//! The many-connection test: `n` clients, each with its own endpoint, connect at once and move bytes while the server's
//! memory and CPU are read. On one endpoint at each end, or with `--endpoints=per-core` spread over the workers.
//!
//! Invariant: a cell of the result line is a measured number or `null`. A reading that failed (the server's counters
//! before or after the burst, the reset of a peak) and a count of zero connections leave the cells that need them
//! `null`; nothing stands in for them, so the summary never ranks them. The exception is the process's own memory and
//! CPU: a failed read of those is still 0 (issue 619).

use std::io;
use std::time::{Duration, Instant};

use futures::StreamExt;
use futures::channel::{mpsc, oneshot};

use super::{Lib, Rec, Stats, pct, per_core, reading, reset_peak, server_base, server_stats, settle, upload, us};

/// What a burst of clients did.
struct Burst {
    requested: usize,
    /// Clients that connected and moved their bytes.
    ok: u32,
    failed: u32,
    secs: f64,
    /// The time to each first byte, in microseconds, sorted.
    up: Vec<f64>,
    /// The last dial error, else the first reason a client did not start; both when both happened.
    why: String,
}

/// The readings around a burst; `None` is a read that failed.
struct Readings {
    /// The server's counters before the burst, taken as it reset its peak (peak 0 if it could not).
    s_base: Option<Stats>,
    s_end: Option<Stats>,
    /// The client before its endpoints were made.
    c_before: Stats,
    /// The client with its endpoints made and its peak reset (`c_peak_reset`: whether it was).
    c_made: Stats,
    c_peak_reset: bool,
    c_end: Stats,
}

/// The peak since `base` was read, in KiB, when it was reset there (`reset`) and read at `end`.
fn peak_over(base: &Stats, end: &Stats, reset: bool) -> Option<u64> {
    (reset && end.peak_kb != 0).then(|| end.peak_kb.saturating_sub(base.rss_kb))
}

/// This process's counters with its peak reset, and whether it was.
fn client_made() -> (Stats, bool) {
    let reset = reset_peak();
    (Stats::now(), reset)
}

/// Keep the first reason a client could not start, so a row whose every failure is of that kind still says why.
fn keep_first(why: &mut String, e: &io::Error) {
    if why.is_empty() {
        *why = e.to_string();
    }
}

/// The row's `last_error`: the last dial error, else the first reason a client did not start. When both happened the
/// line keeps both, so a later dial error never hides that clients could not start.
fn why_of(did_not_start: u32, start: &str, dial: &str) -> String {
    match (start.is_empty(), dial.is_empty()) {
        (false, false) => format!("clients that did not start: {did_not_start} ({start}); last dial error: {dial}"),
        (false, true) => start.to_owned(),
        _ => dial.to_owned(),
    }
}

/// The result line of a burst. A cell is `null`, not a number, when a reading it needs failed or nothing connected.
fn line(lib: &str, b: &Burst, r: &Readings) -> Rec {
    let per_conn = |kb: Option<u64>| match kb {
        Some(kb) if b.ok > 0 => kb as f64 / f64::from(b.ok),
        _ => f64::NAN,
    };
    let mib = |s: Option<Stats>| s.map_or(f64::NAN, |s| s.rss_kb as f64 / 1024.0);
    let server = r.s_base.zip(r.s_end);
    let server_peak = server.and_then(|(a, z)| peak_over(&a, &z, a.peak_kb != 0));
    Rec::new(lib, "many")
        .n("requested", b.requested as f64)
        .n("connected_and_moved", f64::from(b.ok))
        .n("failed", f64::from(b.failed))
        .n("all_done_s", if b.ok > 0 { b.secs } else { f64::NAN })
        .n("first_byte_p50_ms", pct(&b.up, 0.5) / 1e3)
        .n("first_byte_p99_ms", pct(&b.up, 0.99) / 1e3)
        .n("server_rss_base_mib", mib(r.s_base))
        .n("server_rss_mib", mib(r.s_end))
        .n(
            "server_kib_per_conn",
            per_conn(server.map(|(a, z)| z.rss_kb.saturating_sub(a.rss_kb))),
        )
        .n(
            "client_kib_per_conn",
            per_conn(Some(r.c_end.rss_kb.saturating_sub(r.c_made.rss_kb))),
        )
        .n("server_peak_kib_per_conn", per_conn(server_peak))
        .n(
            "client_peak_kib_per_conn",
            per_conn(peak_over(&r.c_made, &r.c_end, r.c_peak_reset)),
        )
        .n("client_rss_before_mib", r.c_before.rss_kb as f64 / 1024.0)
        .s("reading", reading())
        .n("server_cpu_s", server.map_or(f64::NAN, |(a, z)| z.cpu_secs_since(a)))
        .n("client_cpu_s", r.c_end.cpu_secs_since(r.c_made))
        .s("last_error", &b.why)
}

/// The line of a run whose control connection did not open.
fn no_control<L: Lib>() -> Rec {
    Rec::new(L::name(), "many")
        .s("status", "failed: no control connection")
        .s("reading", reading())
}

/// `n` clients, each with its own endpoint, connect at once and move `each` bytes; the server's memory and CPU are read
/// while every connection is still open. The line goes to `sink` as soon as it is read, before the clients let go.
async fn many_one<L: Lib>(addr: &str, n: usize, each: u64, sink: impl FnOnce(Rec)) {
    let Ok(ctl_ep) = L::burst_client().await else {
        sink(no_control::<L>());
        return;
    };
    let Ok(ctl) = L::hello(&ctl_ep, addr, false).await else {
        sink(no_control::<L>());
        return;
    };
    let s_base = server_base::<L>(&ctl).await.ok();
    let c_before = Stats::now();
    let mut eps = Vec::with_capacity(n);
    let (mut no_endpoint, mut start, mut dial) = (0u32, String::new(), String::new());
    for _ in 0..n {
        match L::burst_client().await {
            Ok(e) => eps.push(e),
            Err(e) => {
                no_endpoint += 1;
                keep_first(&mut start, &e);
            }
        }
    }
    let (c_made, c_peak_reset) = client_made();
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
    let (mut held, mut up, mut failed) = (Vec::with_capacity(n), Vec::new(), no_endpoint);
    while let Some((ep, r)) = results.next().await {
        match r {
            Ok((u, c)) => {
                up.push(us(u));
                held.push((ep, c));
            }
            Err(e) => {
                failed += 1;
                dial = e;
            }
        }
    }
    let secs = t.elapsed().as_secs_f64();
    // Let the memory settle before the readings.
    L::sleep(settle()).await;
    let (s_end, c_end) = (server_stats::<L>(&ctl).await.ok(), Stats::now());
    up.sort_by(f64::total_cmp);
    let burst = Burst {
        requested: n,
        ok: held.len() as u32,
        failed,
        secs,
        up,
        why: why_of(no_endpoint, &start, &dial),
    };
    let readings = Readings {
        s_base,
        s_end,
        c_before,
        c_made,
        c_peak_reset,
        c_end,
    };
    sink(line(L::name(), &burst, &readings));
    for (ep, c) in held {
        L::close(&ep, &c).await;
        L::shutdown(ep).await;
    }
    L::shutdown(ctl_ep).await;
}

/// The `many` test: on one endpoint as ever, or, with `--endpoints=per-core`, with the clients spread over the workers.
pub(super) async fn many<L: Lib>(addr: &str, n: usize, each: u64) {
    if per_core() {
        many_spread::<L>(addr, n, each, Rec::emit).await;
    } else {
        many_one::<L>(addr, n, each, Rec::emit).await;
    }
}

/// `n` clients, each with its own endpoint, connect at once and move `each` bytes; the server's memory and CPU are read
/// while every connection is still open.
///
/// Each client is one job that [`Lib::spawn_client`] starts (on a worker of its own when the endpoints are per core):
/// it makes its endpoint, waits for the start, connects and uploads, then holds its connection until it is released.
/// The readings are the same either way: the client's memory after every endpoint is made and while every connection
/// is open, the time from the start to the last upload. A client the library did not start counts as having no
/// endpoint.
#[allow(clippy::too_many_lines)]
async fn many_spread<L: Lib>(addr: &str, n: usize, each: u64, sink: impl FnOnce(Rec)) {
    let Ok(ctl_ep) = L::burst_client().await else {
        sink(no_control::<L>());
        return;
    };
    let Ok(ctl) = L::hello(&ctl_ep, addr, false).await else {
        sink(no_control::<L>());
        return;
    };
    let s_base = server_base::<L>(&ctl).await.ok();
    let c_before = Stats::now();
    let (made, mut made_rx) = mpsc::unbounded::<Result<(), String>>();
    let (done, mut results) = mpsc::unbounded::<Result<Duration, String>>();
    let (ended, mut ended_rx) = mpsc::unbounded::<()>();
    let (mut go, mut release) = (Vec::with_capacity(n), Vec::with_capacity(n));
    let (mut refused, mut start, mut dial) = (0usize, String::new(), String::new());
    for i in 0..n {
        let (go_tx, go_rx) = oneshot::channel::<Instant>();
        let (release_tx, release_rx) = oneshot::channel::<()>();
        go.push(go_tx);
        release.push(release_tx);
        let (addr, made, done, ended) = (addr.to_owned(), made.clone(), done.clone(), ended.clone());
        let started = L::spawn_client(i, move || async move {
            // Each sender goes as soon as it has spoken: a job that ends early closes its channels instead of leaving
            // the crowd waiting for it.
            let ep = match L::burst_client().await {
                Ok(ep) => ep,
                Err(e) => {
                    let _ = made.unbounded_send(Err(e.to_string()));
                    return;
                }
            };
            let _ = made.unbounded_send(Ok(()));
            drop(made);
            let held = match go_rx.await {
                Ok(t) => {
                    let r = async {
                        let c = L::hello(&ep, &addr, false).await?;
                        let up = t.elapsed();
                        upload::<L>(&c, each).await?;
                        io::Result::Ok((up, c))
                    }
                    .await;
                    let held = match r {
                        Ok((up, c)) => {
                            let _ = done.unbounded_send(Ok(up));
                            Some(c)
                        }
                        Err(e) => {
                            let _ = done.unbounded_send(Err(e.to_string()));
                            None
                        }
                    };
                    drop(done);
                    held
                }
                Err(_) => None,
            };
            let _ = release_rx.await;
            if let Some(c) = held {
                L::close(&ep, &c).await;
            }
            L::shutdown(ep).await;
            let _ = ended.unbounded_send(());
        });
        if let Err(e) = started {
            refused += 1;
            keep_first(&mut start, &e);
        }
    }
    drop((made, done, ended));
    let mut no_endpoint = u32::try_from(refused).unwrap_or(u32::MAX);
    for _ in 0..n - refused {
        match made_rx.next().await {
            Some(Ok(())) => {}
            Some(Err(e)) => {
                no_endpoint += 1;
                if start.is_empty() {
                    start = e;
                }
            }
            None => no_endpoint += 1,
        }
    }
    let (c_made, c_peak_reset) = client_made();
    let t = Instant::now();
    for g in go {
        let _ = g.send(t);
    }
    let (mut ok, mut up, mut failed) = (0u32, Vec::new(), no_endpoint);
    for _ in 0..n.saturating_sub(no_endpoint as usize) {
        match results.next().await {
            Some(Ok(u)) => {
                up.push(us(u));
                ok += 1;
            }
            Some(Err(e)) => {
                failed += 1;
                dial = e;
            }
            None => break,
        }
    }
    let secs = t.elapsed().as_secs_f64();
    // Let the memory settle before the readings.
    L::sleep(settle()).await;
    let (s_end, c_end) = (server_stats::<L>(&ctl).await.ok(), Stats::now());
    up.sort_by(f64::total_cmp);
    let burst = Burst {
        requested: n,
        ok,
        failed,
        secs,
        up,
        why: why_of(no_endpoint, &start, &dial),
    };
    let readings = Readings {
        s_base,
        s_end,
        c_before,
        c_made,
        c_peak_reset,
        c_end,
    };
    sink(line(L::name(), &burst, &readings));
    for r in release {
        let _ = r.send(());
    }
    while ended_rx.next().await.is_some() {}
    L::shutdown(ctl_ep).await;
}

// The benches have no test harness; these run in the harness crate that includes this module.
#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::ignored_unit_patterns,
    clippy::unused_async_trait_impl,
    reason = "tests assert"
)]
mod tests {
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering::Relaxed};

    use super::super::{Rx, Tx, handle};
    use super::*;

    /// A burst over in-memory streams to the real [`handle`], with the failures a test asks for.
    struct Fake;

    /// The server's answer to the base request fails.
    const NO_BASE: u8 = 1;
    /// The server's answer to the request after the burst fails.
    const NO_END: u8 = 2;
    /// Every dial after the control connection fails.
    const NO_CONNECT: u8 = 4;
    static FAULTS: AtomicU8 = AtomicU8::new(0);
    /// The client `spawn_client` refuses (`usize::MAX`: none).
    static REFUSE: AtomicUsize = AtomicUsize::new(usize::MAX);
    /// The endpoint whose making fails, counting the control endpoint as 0 (`usize::MAX`: none).
    static BAD_ENDPOINT: AtomicUsize = AtomicUsize::new(usize::MAX);
    static MADE: AtomicUsize = AtomicUsize::new(0);
    static DIALS: AtomicUsize = AtomicUsize::new(0);
    /// One test at a time sets the statics above.
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

    struct FakeTx(Option<mpsc::UnboundedSender<Vec<u8>>>);
    struct FakeRx {
        rx: mpsc::UnboundedReceiver<Vec<u8>>,
        left: Vec<u8>,
    }

    impl Tx for FakeTx {
        async fn write_all(&mut self, b: &[u8]) -> io::Result<()> {
            let fault = match b {
                b"B" => NO_BASE,
                b"T" => NO_END,
                _ => 0,
            };
            if FAULTS.load(Relaxed) & fault != 0 {
                return Err(io::Error::other("the stream failed"));
            }
            let tx = self.0.as_ref().ok_or_else(|| io::Error::other("finished"))?;
            tx.unbounded_send(b.to_vec()).map_err(io::Error::other)
        }
        async fn finish(&mut self) -> io::Result<()> {
            self.0 = None;
            Ok(())
        }
    }

    impl Rx for FakeRx {
        async fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
            if self.left.is_empty() {
                match self.rx.next().await {
                    Some(v) => self.left = v,
                    None => return Ok(0),
                }
            }
            let n = b.len().min(self.left.len());
            b[..n].copy_from_slice(&self.left[..n]);
            self.left.drain(..n);
            Ok(n)
        }
    }

    impl Lib for Fake {
        fn name() -> &'static str {
            "fake"
        }
        const RESUMES: bool = false;
        type Ep = ();
        type Conn = ();
        type Tx = FakeTx;
        type Rx = FakeRx;

        fn run<T>(f: impl std::future::Future<Output = T>) -> T {
            nuclei::Builder::new().build().unwrap().block_on(f)
        }
        fn spawn(f: impl std::future::Future<Output = ()> + 'static) {
            nuclei::spawn_local(f).detach();
        }
        fn spawn_client<F: std::future::Future<Output = ()> + 'static>(
            i: usize,
            make: impl FnOnce() -> F + Send + 'static,
        ) -> io::Result<()> {
            if i == REFUSE.load(Relaxed) {
                return Err(io::Error::other("the client was not started"));
            }
            Self::spawn(make());
            Ok(())
        }
        async fn sleep(d: Duration) {
            nuclei::time::sleep(d).await;
        }
        async fn serve() -> io::Result<String> {
            Ok(String::new())
        }
        async fn client() -> io::Result<()> {
            if MADE.fetch_add(1, Relaxed) == BAD_ENDPOINT.load(Relaxed) {
                return Err(io::Error::other("no endpoint"));
            }
            Ok(())
        }
        async fn connect(_: &(), _: &str) -> io::Result<()> {
            if DIALS.fetch_add(1, Relaxed) > 0 && FAULTS.load(Relaxed) & NO_CONNECT != 0 {
                return Err(io::Error::other("no connection"));
            }
            Ok(())
        }
        async fn open(_: &()) -> io::Result<(FakeTx, FakeRx)> {
            let (c2s_tx, c2s_rx) = mpsc::unbounded();
            let (s2c_tx, s2c_rx) = mpsc::unbounded();
            Self::spawn(async move {
                let _ = handle(
                    FakeTx(Some(s2c_tx)),
                    FakeRx {
                        rx: c2s_rx,
                        left: Vec::new(),
                    },
                )
                .await;
            });
            Ok((
                FakeTx(Some(c2s_tx)),
                FakeRx {
                    rx: s2c_rx,
                    left: Vec::new(),
                },
            ))
        }
        async fn close(_: &(), _: &()) {}
        async fn shutdown(_: ()) {}
    }

    /// The result line of a burst of `n` clients with the given failures: `spread` runs the per-core path.
    fn burst(spread: bool, n: usize, faults: u8, refuse: usize, bad_endpoint: usize) -> String {
        let _one = ONE_AT_A_TIME.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        let _switches = super::super::SWITCHES
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        FAULTS.store(faults, Relaxed);
        REFUSE.store(refuse, Relaxed);
        BAD_ENDPOINT.store(bad_endpoint, Relaxed);
        MADE.store(0, Relaxed);
        DIALS.store(0, Relaxed);
        let out = Rc::new(RefCell::new(None));
        let sink = {
            let out = Rc::clone(&out);
            move |rec: Rec| *out.borrow_mut() = Some(format!("{}}}", rec.0))
        };
        Fake::run(async move {
            if spread {
                many_spread::<Fake>("", n, 1024, sink).await;
            } else {
                many_one::<Fake>("", n, 1024, sink).await;
            }
        });
        out.borrow_mut().take().unwrap()
    }

    /// The text of the field `k` of a result line (numbers and `null`), if the line has it.
    fn raw<'a>(line: &'a str, k: &str) -> Option<&'a str> {
        let rest = line.split(&format!("\"{k}\":")).nth(1)?;
        rest.split([',', '}']).next()
    }

    fn number(v: &str, k: &str) -> f64 {
        raw(v, k)
            .and_then(|r| r.parse().ok())
            .unwrap_or_else(|| panic!("{k} is a number in {v}"))
    }

    fn is_null(v: &str, k: &str) -> bool {
        raw(v, k) == Some("null")
    }

    #[test]
    fn every_client_that_connects_is_counted_and_its_cells_are_numbers() {
        for spread in [false, true] {
            let v = burst(spread, 8, 0, usize::MAX, usize::MAX);
            assert_eq!(number(&v, "requested"), 8.0, "spread {spread}");
            assert_eq!(number(&v, "connected_and_moved"), 8.0, "spread {spread}");
            assert_eq!(number(&v, "failed"), 0.0, "spread {spread}");
            for k in [
                "server_rss_base_mib",
                "server_rss_mib",
                "server_kib_per_conn",
                "client_kib_per_conn",
                "server_cpu_s",
                "client_cpu_s",
                "first_byte_p50_ms",
                "all_done_s",
            ] {
                number(&v, k);
            }
            // Both peaks are measured exactly when this process could reset its peak, as the fake server is in it.
            let reset = reset_peak();
            for k in ["server_peak_kib_per_conn", "client_peak_kib_per_conn"] {
                assert_eq!(!is_null(&v, k), reset, "{k} (spread {spread}): {v}");
                if reset {
                    number(&v, k);
                }
            }
        }
    }

    #[test]
    fn a_client_that_could_not_start_leaves_its_reason_in_the_row() {
        for spread in [false, true] {
            let v = burst(spread, 6, 0, usize::MAX, 3);
            assert!(
                v.contains("\"last_error\":\"no endpoint\""),
                "an endpoint that failed (spread {spread}): {v}"
            );
        }
        let v = burst(true, 6, 0, 3, usize::MAX);
        assert!(
            v.contains("\"last_error\":\"the client was not started\""),
            "a refused client: {v}"
        );
    }

    #[test]
    fn a_dial_error_does_not_hide_that_clients_could_not_start() {
        for spread in [false, true] {
            let v = burst(spread, 6, NO_CONNECT, usize::MAX, 3);
            let both = "clients that did not start: 1 (no endpoint); last dial error: no connection";
            assert!(
                v.contains(&format!("\"last_error\":\"{both}\"")),
                "spread {spread}: {v}"
            );
        }
    }

    #[test]
    fn a_control_endpoint_that_cannot_be_made_is_reported_not_dropped() {
        for spread in [false, true] {
            let v = burst(spread, 4, 0, usize::MAX, 0);
            assert!(
                v.contains("\"status\":\"failed: no control connection\""),
                "spread {spread}: {v}"
            );
        }
    }

    #[test]
    fn a_client_the_library_did_not_start_or_that_made_no_endpoint_is_a_failure_not_a_connection() {
        let v = burst(true, 6, 0, 3, usize::MAX);
        assert_eq!(number(&v, "connected_and_moved"), 5.0, "a refused client");
        assert_eq!(number(&v, "failed"), 1.0, "a refused client");
        for spread in [false, true] {
            // The control endpoint is the first made, so endpoint 3 is the third client's.
            let v = burst(spread, 6, 0, usize::MAX, 3);
            assert_eq!(number(&v, "connected_and_moved"), 5.0, "spread {spread}");
            assert_eq!(number(&v, "failed"), 1.0, "spread {spread}");
        }
    }

    #[test]
    fn a_failed_base_read_leaves_the_server_cells_missing_not_the_whole_process_divided() {
        for spread in [false, true] {
            let v = burst(spread, 8, NO_BASE, usize::MAX, usize::MAX);
            for k in [
                "server_rss_base_mib",
                "server_kib_per_conn",
                "server_peak_kib_per_conn",
                "server_cpu_s",
            ] {
                assert!(is_null(&v, k), "{k} with no base (spread {spread}): {v}");
            }
            number(&v, "server_rss_mib");
            number(&v, "client_kib_per_conn");
        }
    }

    #[test]
    fn a_failed_stats_request_after_the_burst_leaves_the_server_cells_missing_not_zero() {
        for spread in [false, true] {
            let v = burst(spread, 8, NO_END, usize::MAX, usize::MAX);
            for k in [
                "server_rss_mib",
                "server_kib_per_conn",
                "server_peak_kib_per_conn",
                "server_cpu_s",
            ] {
                assert!(is_null(&v, k), "{k} with no reading after (spread {spread}): {v}");
            }
            number(&v, "server_rss_base_mib");
            number(&v, "client_cpu_s");
        }
    }

    #[test]
    fn nothing_connected_leaves_every_per_connection_cell_missing() {
        for spread in [false, true] {
            let v = burst(spread, 7, NO_CONNECT, usize::MAX, usize::MAX);
            assert_eq!(number(&v, "connected_and_moved"), 0.0, "spread {spread}");
            assert_eq!(number(&v, "failed"), 7.0, "spread {spread}");
            for k in [
                "server_kib_per_conn",
                "client_kib_per_conn",
                "server_peak_kib_per_conn",
                "client_peak_kib_per_conn",
                "first_byte_p50_ms",
                "first_byte_p99_ms",
                "all_done_s",
            ] {
                assert!(is_null(&v, k), "{k} with no connection (spread {spread}): {v}");
            }
        }
    }

    fn stats(rss_kb: u64, peak_kb: u64) -> Stats {
        Stats {
            rss_kb,
            peak_kb,
            ..Stats::default()
        }
    }

    fn pure_line(s_base: Stats, s_end: Stats, c_made: Stats, c_end: Stats, c_peak_reset: bool) -> String {
        pure_line_of(10, s_base, s_end, c_made, c_end, c_peak_reset)
    }

    /// The line of a burst that asked for 10 clients and had `ok` connect.
    fn pure_line_of(ok: u32, s_base: Stats, s_end: Stats, c_made: Stats, c_end: Stats, c_peak_reset: bool) -> String {
        let burst = Burst {
            requested: 10,
            ok,
            failed: 10 - ok,
            secs: 1.0,
            up: vec![1.0; ok as usize],
            why: String::new(),
        };
        let readings = Readings {
            s_base: Some(s_base),
            s_end: Some(s_end),
            c_before: stats(500, 500),
            c_made,
            c_peak_reset,
            c_end,
        };
        format!("{}}}", line("fake", &burst, &readings).0)
    }

    #[test]
    fn the_peak_of_each_side_starts_from_its_memory_at_the_reset_not_from_before_its_endpoints() {
        let v = pure_line(
            stats(1000, 1000),
            stats(2000, 6000),
            stats(1500, 1500),
            stats(2500, 4500),
            true,
        );
        // The server: (6000 - 1000) / 10. The client: (4500 - 1500) / 10, not from the 500 before its endpoints.
        assert_eq!(number(&v, "server_peak_kib_per_conn"), 500.0);
        assert_eq!(number(&v, "client_peak_kib_per_conn"), 300.0);
    }

    #[test]
    fn a_cell_per_connection_divides_by_the_clients_that_connected_not_the_ones_asked_for() {
        let v = pure_line_of(
            4,
            stats(1000, 1000),
            stats(2000, 6000),
            stats(1500, 1500),
            stats(2500, 4500),
            true,
        );
        assert_eq!(number(&v, "server_kib_per_conn"), 250.0);
        assert_eq!(number(&v, "client_kib_per_conn"), 250.0);
        assert_eq!(number(&v, "server_peak_kib_per_conn"), 1250.0);
        assert_eq!(number(&v, "client_peak_kib_per_conn"), 750.0);
    }

    #[test]
    fn a_peak_that_was_not_reset_is_missing_never_the_old_peak() {
        // The server's answer to the base request carries peak 0 when it could not reset; the client says it did not.
        let v = pure_line(
            stats(1000, 0),
            stats(2000, 6000),
            stats(1500, 1500),
            stats(2500, 4500),
            false,
        );
        assert!(is_null(&v, "server_peak_kib_per_conn"), "{v}");
        assert!(is_null(&v, "client_peak_kib_per_conn"), "{v}");
        number(&v, "server_kib_per_conn");
        number(&v, "client_kib_per_conn");
    }
}
