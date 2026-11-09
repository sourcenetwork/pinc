//! A server that holds a thousand sessions in one process over loopback, all moving data; and the engine building on
//! a thread with the default stack size.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::zombie_processes,
    clippy::useless_conversion,
    clippy::manual_assert_eq,
    clippy::items_after_statements,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod vinc_common;

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use vinc::Vinc;
use vinc_common::{ECHO, Exec, Svc, lo, watchdog};
use vinc_driver::{EngineConfig, Identity, Limits, Wake, chan, plane, run};

const SESSIONS: usize = 1000;
/// The most handshakes in flight at once.
const DIALING: usize = 64;

/// What a client of the crowd needs: one session with one stream.
fn small() -> Limits {
    Limits {
        connections: 1,
        pool_chunks: 16,
        stream_window: 32 * 1024,
        streams: 2,
        ..Limits::default()
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn a_thousand_sessions_in_one_process_all_move_data() {
    watchdog(900);
    let exec = Exec::new(4);
    let server = Vinc::builder()
        .bind_addr(lo())
        .limits(Limits {
            connections: 1024,
            pool_chunks: 32,
            stream_window: 32 * 1024,
            streams: 2,
            ..Limits::default()
        })
        .spawn_on(exec.clone())
        .unwrap();
    exec.block_on({
        let server = server.clone();
        async move { server.register(Arc::new(Svc(ECHO))).await.unwrap() }
    });
    let addr = server.addr();
    let (done, failed, release, dialing) = (
        Arc::new(AtomicUsize::new(0)),
        Arc::new(AtomicUsize::new(0)),
        Arc::new(AtomicBool::new(false)),
        Arc::new(AtomicUsize::new(0)),
    );
    let errors = Arc::new(Mutex::new(Vec::<String>::new()));
    let clients: Vec<_> = (0..SESSIONS)
        .map(|i| {
            // At most DIALING handshakes are in flight, so a burst of a thousand does not starve the server.
            wait_until(Duration::from_secs(300), || {
                dialing
                    .try_update(Ordering::SeqCst, Ordering::SeqCst, |n| (n < DIALING).then_some(n + 1))
                    .is_ok()
            })
            .expect("the dial window never opened");
            let (addr, done, failed, release, dialing, errors) = (
                addr.clone(),
                Arc::clone(&done),
                Arc::clone(&failed),
                Arc::clone(&release),
                Arc::clone(&dialing),
                Arc::clone(&errors),
            );
            thread::Builder::new()
                .stack_size(2 * 1024 * 1024)
                .spawn(move || {
                    let run = || -> Result<_, String> {
                        let ep = Vinc::builder()
                            .bind_addr(lo())
                            .limits(small())
                            .bind_blocking()
                            .map_err(|e| format!("bind: {e:?}"))?
                            .blocking();
                        let mut last = String::new();
                        let conn = (0..5)
                            .find_map(|_| match ep.connect(addr.clone(), ECHO) {
                                Ok(c) => Some(c),
                                Err(e) => {
                                    last = format!("{e:?}");
                                    None
                                }
                            })
                            .ok_or_else(|| format!("client {i}: no session after 5 dials: {last}"))?;
                        dialing.fetch_sub(1, Ordering::SeqCst);
                        let (mut tx, mut rx) = conn.open_bi().map_err(|e| format!("client {i}: open: {e:?}"))?;
                        let payload: Vec<u8> = (0..20_000usize).map(|k| (k ^ i) as u8).collect();
                        tx.write_all(&payload)
                            .map_err(|e| format!("client {i}: write: {e:?}"))?;
                        tx.finish().map_err(|e| format!("client {i}: finish: {e:?}"))?;
                        let got = rx
                            .read_to_end(1 << 20)
                            .map_err(|e| format!("client {i}: read: {e:?}"))?;
                        if got != payload {
                            return Err(format!("client {i}: the echo differs ({} bytes)", got.len()));
                        }
                        Ok((conn, ep))
                    };
                    match run() {
                        Ok(keep) => {
                            done.fetch_add(1, Ordering::SeqCst);
                            // Every session stays open until all have moved their data.
                            wait_until(Duration::from_secs(600), || release.load(Ordering::SeqCst)).ok();
                            drop(keep);
                        }
                        Err(e) => {
                            errors.lock().unwrap().push(e);
                            failed.fetch_add(1, Ordering::SeqCst);
                        }
                    }
                })
                .unwrap()
        })
        .collect();
    let all = wait_until(Duration::from_secs(600), || {
        failed.load(Ordering::SeqCst) > 0 || done.load(Ordering::SeqCst) == SESSIONS
    });
    let stats = exec.block_on({
        let server = server.clone();
        async move { server.node_stats().await.unwrap() }
    });
    let finish = |release: &AtomicBool| {
        release.store(true, Ordering::SeqCst);
        for c in clients {
            c.join().unwrap();
        }
    };
    let (n_done, n_failed) = (done.load(Ordering::SeqCst), failed.load(Ordering::SeqCst));
    if all.is_err() || n_failed > 0 {
        let first: Vec<String> = errors.lock().unwrap().iter().take(5).cloned().collect();
        finish(&release);
        panic!("{n_done} of {SESSIONS} clients done, {n_failed} failed: {first:?}; server {stats:?}");
    }
    // A dial that was retried leaves its first attempt half open on the server until it times out.
    assert_eq!(stats.sessions - stats.half_open, SESSIONS, "{stats:?}");
    assert_eq!(stats.events_lost, 0, "{stats:?}");
    finish(&release);
}

/// Poll `ready` with a bounded, growing pause until it holds or `limit` passes.
fn wait_until(limit: Duration, mut ready: impl FnMut() -> bool) -> Result<(), ()> {
    let end = Instant::now() + limit;
    let mut pause = Duration::from_micros(100);
    while !ready() {
        if Instant::now() >= end {
            return Err(());
        }
        thread::sleep(pause);
        pause = (pause * 2).min(Duration::from_millis(20));
    }
    Ok(())
}

struct Nop;
impl Wake for Nop {
    fn wake(&self) {}
}

#[test]
fn the_engine_builds_on_a_thread_with_the_default_stack() {
    // A thread made by `std::thread::spawn` has the default stack (2 MiB unless RUST_MIN_STACK says otherwise); the
    // endpoint of 1024 sessions is over a megabyte and its stream tables are far larger.
    for connections in [1, 1024] {
        let sessions = thread::spawn(move || {
            let (_remote, plane) = plane(8, Arc::new(Nop));
            let (queue, _incoming) = chan(4);
            let cfg = EngineConfig {
                identity: Identity::from_seed(&[5; 32]).unwrap(),
                alpns: vec![ECHO.to_vec()],
                limits: Limits {
                    connections,
                    pool_chunks: 16,
                    ..Limits::default()
                },
                admit: None,
                max_gso: 1,
                locals: vec!["10.0.0.1:4433".parse().unwrap()],
            };
            run(cfg, plane, queue, 10_000_000_000, |e| e.node_stats().sessions).unwrap()
        })
        .join()
        .unwrap();
        assert_eq!(sessions, 0);
    }
}
