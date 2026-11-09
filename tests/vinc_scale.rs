//! A server that holds a thousand sessions in one process over loopback, all moving data; and the engine building on
//! a nuclei worker with its default stack size.
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

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Duration;

use nuclei::sync::Semaphore;
use vinc::Vinc;
use vinc_common::{ECHO, Svc, bind, eventually, register, within};
use vinc_driver::{AllowAll, EngineConfig, Identity, Limits, chan, plane, run};

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

/// One client: its own endpoint, one session, 20 000 bytes echoed; then it holds the session until `release`.
async fn client(
    i: usize,
    addr: vinc::NodeAddr,
    dialing: Arc<Semaphore>,
    done: Arc<AtomicUsize>,
    release: Arc<AtomicBool>,
) -> Result<(), String> {
    // At most DIALING handshakes are in flight, so a burst of a thousand does not starve the server.
    let permit = dialing
        .acquire()
        .await
        .map_err(|_| "the dial window closed".to_owned())?;
    let ep = bind(Vinc::builder().limits(small())).await;
    let mut last = String::new();
    let mut conn = None;
    for _ in 0..5 {
        match ep.connect(addr.clone(), ECHO).await {
            Ok(c) => {
                conn = Some(c);
                break;
            }
            Err(e) => last = format!("{e:?}"),
        }
    }
    let conn = conn.ok_or_else(|| format!("client {i}: no session after 5 dials: {last}"))?;
    drop(permit);
    let (mut tx, mut rx) = conn.open_bi().await.map_err(|e| format!("client {i}: open: {e:?}"))?;
    let payload: Vec<u8> = (0..20_000usize).map(|k| (k ^ i) as u8).collect();
    tx.write_all(&payload)
        .await
        .map_err(|e| format!("client {i}: write: {e:?}"))?;
    tx.finish().await.map_err(|e| format!("client {i}: finish: {e:?}"))?;
    let got = rx
        .read_to_end(1 << 20)
        .await
        .map_err(|e| format!("client {i}: read: {e:?}"))?;
    if got != payload {
        return Err(format!("client {i}: the echo differs ({} bytes)", got.len()));
    }
    done.fetch_add(1, Ordering::SeqCst);
    // Every session stays open until all have moved their data.
    while !release.load(Ordering::SeqCst) {
        nuclei::time::sleep(Duration::from_millis(50)).await;
    }
    drop((conn, ep));
    Ok(())
}

#[nuclei::test]
async fn a_thousand_sessions_in_one_process_all_move_data() {
    within(900, async {
        let server = bind(Vinc::builder().limits(Limits {
            connections: 1024,
            pool_chunks: 32,
            stream_window: 32 * 1024,
            streams: 2,
            ..Limits::default()
        }))
        .await;
        register(&server, Arc::new(Svc(ECHO))).await.unwrap();
        let addr = server.addr();
        let (done, release, dialing) = (
            Arc::new(AtomicUsize::new(0)),
            Arc::new(AtomicBool::new(false)),
            Arc::new(Semaphore::new(DIALING)),
        );
        let clients: Vec<_> = (0..SESSIONS)
            .map(|i| {
                nuclei::spawn(client(
                    i,
                    addr.clone(),
                    Arc::clone(&dialing),
                    Arc::clone(&done),
                    Arc::clone(&release),
                ))
            })
            .collect();
        eventually(600, "every client moved its data", || async {
            done.load(Ordering::SeqCst) == SESSIONS || clients.iter().any(nuclei::Task::is_finished)
        })
        .await;
        let stats = server.node_stats().await.unwrap();
        let n_done = done.load(Ordering::SeqCst);
        release.store(true, Ordering::SeqCst);
        let mut errors = Vec::new();
        for c in clients {
            if let Err(e) = c.await {
                errors.push(e);
            }
        }
        assert!(
            errors.is_empty(),
            "{n_done} of {SESSIONS} clients done, {} failed: {:?}; server {stats:?}",
            errors.len(),
            errors.iter().take(5).collect::<Vec<_>>()
        );
        // A dial that was retried leaves its first attempt half open on the server until it times out.
        assert_eq!(stats.sessions - stats.half_open, SESSIONS, "{stats:?}");
        assert_eq!(stats.events_lost, 0, "{stats:?}");
    })
    .await;
}

#[nuclei::test]
async fn the_engine_builds_on_a_nuclei_worker_with_the_default_stack() {
    // A nuclei worker has the runtime's default stack; the endpoint of 1024 sessions is over a megabyte and its stream
    // tables are far larger.
    for connections in [1, 1024] {
        let sessions = nuclei::spawn(async move {
            let (_remote, plane) = plane(8);
            let (queue, _incoming) = chan(4);
            let cfg = EngineConfig {
                identity: Identity::from_seed(&[5; 32]).unwrap(),
                alpns: vec![ECHO.to_vec()],
                limits: Limits {
                    connections,
                    pool_chunks: 16,
                    ..Limits::default()
                },
                admit: AllowAll,
                max_gso: 1,
                locals: vec!["10.0.0.1:4433".parse().unwrap()],
            };
            run(cfg, plane, queue, 10_000_000_000, async |e| e.node_stats().sessions)
                .await
                .unwrap()
        })
        .await;
        assert_eq!(sessions, 0);
    }
}
