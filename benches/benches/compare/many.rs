//! The many-connection test: `n` clients, each with its own endpoint, connect at once and move bytes while the server's
//! memory and CPU are read. On one endpoint at each end, or with `--endpoints=per-core` spread over the workers.

use std::io;
use std::time::{Duration, Instant};

use futures::StreamExt;
use futures::channel::{mpsc, oneshot};

use super::{Lib, Rec, Stats, pct, per_core, server_stats, upload, us};

/// `n` clients, each with its own endpoint, connect at once and move `each` bytes; the server's memory and CPU are read
/// while every connection is still open.
async fn many_one<L: Lib>(addr: &str, n: usize, each: u64) {
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

/// The `many` test: on one endpoint as ever, or, with `--endpoints=per-core`, with the clients spread over the workers.
pub(super) async fn many<L: Lib>(addr: &str, n: usize, each: u64) {
    if per_core() {
        many_spread::<L>(addr, n, each).await;
    } else {
        many_one::<L>(addr, n, each).await;
    }
}

/// `n` clients, each with its own endpoint, connect at once and move `each` bytes; the server's memory and CPU are read
/// while every connection is still open.
///
/// Each client is one job that [`Lib::spawn_client`] starts (on a worker of its own when the endpoints are per core):
/// it makes its endpoint, waits for the start, connects and uploads, then holds its connection until it is released.
/// The readings are the same either way: the client's memory after every endpoint is made and while every connection
/// is open, the time from the start to the last upload.
#[allow(clippy::too_many_lines)]
async fn many_spread<L: Lib>(addr: &str, n: usize, each: u64) {
    let Ok(ctl_ep) = L::client().await else { return };
    let Ok(ctl) = L::hello(&ctl_ep, addr, false).await else {
        Rec::new(L::name(), "many")
            .s("status", "failed: no control connection")
            .emit();
        return;
    };
    let s_base = server_stats::<L>(&ctl).await.unwrap_or_default();
    let c_base = Stats::now();
    let (made, mut made_rx) = mpsc::unbounded::<bool>();
    let (done, mut results) = mpsc::unbounded::<Result<Duration, String>>();
    let (ended, mut ended_rx) = mpsc::unbounded::<()>();
    let (mut go, mut release) = (Vec::with_capacity(n), Vec::with_capacity(n));
    for i in 0..n {
        let (go_tx, go_rx) = oneshot::channel::<Instant>();
        let (release_tx, release_rx) = oneshot::channel::<()>();
        go.push(go_tx);
        release.push(release_tx);
        let (addr, made, done, ended) = (addr.to_owned(), made.clone(), done.clone(), ended.clone());
        L::spawn_client(i, move || async move {
            // Each sender goes as soon as it has spoken: a job that ends early closes its channels instead of leaving
            // the crowd waiting for it.
            let Ok(ep) = L::client().await else {
                let _ = made.unbounded_send(false);
                return;
            };
            let _ = made.unbounded_send(true);
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
    }
    drop((made, done, ended));
    let mut no_endpoint = 0u32;
    for _ in 0..n {
        match made_rx.next().await {
            Some(true) => {}
            Some(false) | None => no_endpoint += 1,
        }
    }
    let c_made = Stats::now();
    let t = Instant::now();
    for g in go {
        let _ = g.send(t);
    }
    let (mut ok, mut up, mut failed, mut why) = (0u32, Vec::new(), no_endpoint, String::new());
    for _ in 0..n.saturating_sub(no_endpoint as usize) {
        match results.next().await {
            Some(Ok(u)) => {
                up.push(us(u));
                ok += 1;
            }
            Some(Err(e)) => {
                failed += 1;
                why = e;
            }
            None => break,
        }
    }
    let secs = t.elapsed().as_secs_f64();
    // Let the memory settle before the readings.
    L::sleep(Duration::from_millis(500)).await;
    let (s1, c1) = (server_stats::<L>(&ctl).await.unwrap_or(s_base), Stats::now());
    up.sort_by(f64::total_cmp);
    let ok = f64::from(ok);
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
    for r in release {
        let _ = r.send(());
    }
    while ended_rx.next().await.is_some() {}
    L::shutdown(ctl_ep).await;
}
