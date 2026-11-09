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

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::Duration;

use vinc::Vinc;
use vinc_common::{ECHO, Exec, Svc, lo, watchdog};
use vinc_driver::{EngineConfig, Identity, Limits, Wake, chan, plane, run};

const SESSIONS: usize = 1000;

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
    let all_up = Arc::new(Barrier::new(SESSIONS + 1));
    let done = Arc::new(AtomicUsize::new(0));
    let clients: Vec<_> = (0..SESSIONS)
        .map(|i| {
            let (addr, all_up, done) = (addr.clone(), Arc::clone(&all_up), Arc::clone(&done));
            let t = thread::Builder::new()
                .stack_size(2 * 1024 * 1024)
                .spawn(move || {
                    let ep = Vinc::builder()
                        .bind_addr(lo())
                        .limits(small())
                        .bind_blocking()
                        .unwrap()
                        .blocking();
                    let mut conn = None;
                    for _ in 0..5 {
                        if let Ok(c) = ep.connect(addr.clone(), ECHO) {
                            conn = Some(c);
                            break;
                        }
                    }
                    let conn = conn.expect("a session did not open");
                    let (mut tx, mut rx) = conn.open_bi().unwrap();
                    let payload: Vec<u8> = (0..20_000usize).map(|k| (k ^ i) as u8).collect();
                    tx.write_all(&payload).unwrap();
                    tx.finish().unwrap();
                    assert_eq!(rx.read_to_end(1 << 20).unwrap(), payload);
                    done.fetch_add(1, Ordering::SeqCst);
                    // Every session stays open until all have moved their data.
                    all_up.wait();
                    all_up.wait();
                    drop(conn);
                })
                .unwrap();
            thread::sleep(Duration::from_millis(2));
            t
        })
        .collect();
    all_up.wait();
    assert_eq!(done.load(Ordering::SeqCst), SESSIONS);
    let stats = exec.block_on({
        let server = server.clone();
        async move { server.node_stats().await.unwrap() }
    });
    // A dial that was retried leaves its first attempt half open on the server until it times out.
    assert_eq!(stats.sessions - stats.half_open, SESSIONS, "{stats:?}");
    assert_eq!(stats.events_lost, 0, "{stats:?}");
    all_up.wait();
    for c in clients {
        c.join().unwrap();
    }
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
