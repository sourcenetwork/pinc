//! What a client holds (vinc#158, #141): the memory of an endpoint with no session, and of one session that moved 64 KiB
//! and went quiet, as the resident bytes of the client's own allocations.
//!
//! A server runs on a thread of its own; the test thread builds [`CLIENTS`] endpoints of one session each and moves
//! 64 KiB on each, one after the other. The allocator records every allocation of 4 KiB or more the test thread makes,
//! and the system says which of their pages are resident, so the reading does not depend on how lazily the allocator
//! commits a large buffer. Smaller allocations are left out: a few KiB a session.
//!
//! And what a burst leaves behind (vinc#435): [`BURST`] sessions on one client endpoint move 64 KiB each at once and go
//! quiet; the process's resident memory may grow by little more than the resident pages of the live allocations of
//! both ends. Memory freed and kept by the allocator is resident and held by nothing.
#![cfg(target_os = "linux")]
#![allow(
    unsafe_code,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_precision_loss,
    clippy::semicolon_if_nothing_returned
)]

mod vinc_common;

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use std::time::Duration;

use vinc::{Limits, Vinc};
use vinc_common::{SINK, bind_idle, node};

/// The client endpoints, one session each.
const CLIENTS: usize = 32;
/// The most an endpoint with no session may hold. It holds 619 KiB; before vinc#158 it held 987 KiB, 464 KiB of it the
/// buffers and queues of the four relay slots, made whether a relay was named or not.
const ENDPOINT_MAX: usize = 704 * 1024;
/// The most a session that moved 64 KiB and went quiet may add to its endpoint. It adds 54 KiB; before vinc#435 it
/// added 101 KiB, and before vinc#158 161 KiB: a pool segment of 256 KiB written as far as its chunks were used, the
/// endpoint's own receive and transmit buffers, and the handshake machine the endpoint kept for its next handshake.
const SESSION_MAX: usize = 80 * 1024;

const SMALL: usize = 4096;
const CAP: usize = 1 << 16;
const GONE: usize = usize::MAX;

static PTRS: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static SIZES: [AtomicUsize; CAP] = [const { AtomicUsize::new(0) }; CAP];
static LOCK: AtomicBool = AtomicBool::new(false);

thread_local! {
    /// This thread's allocations are recorded.
    static TRACK: Cell<bool> = const { Cell::new(false) };
}

fn slot(p: usize) -> usize {
    (p >> 4) % CAP
}

fn locked<T>(f: impl FnOnce() -> T) -> T {
    while LOCK.swap(true, Relaxed) {
        std::hint::spin_loop();
    }
    let r = f();
    LOCK.store(false, Relaxed);
    r
}

fn record(p: *mut u8, size: usize) {
    if p.is_null() || size < SMALL || !TRACK.with(Cell::get) {
        return;
    }
    locked(|| {
        let mut i = slot(p as usize);
        while !matches!(PTRS[i].load(Relaxed), 0 | GONE) {
            i = (i + 1) % CAP;
        }
        PTRS[i].store(p as usize, Relaxed);
        SIZES[i].store(size, Relaxed);
    });
}

fn forget(p: *mut u8, size: usize) {
    if size < SMALL {
        return;
    }
    locked(|| {
        let mut i = slot(p as usize);
        for _ in 0..CAP {
            match PTRS[i].load(Relaxed) {
                0 => return,
                q if q == p as usize => {
                    PTRS[i].store(GONE, Relaxed);
                    return;
                }
                _ => i = (i + 1) % CAP,
            }
        }
    });
}

struct Recording;

// SAFETY: every method forwards to the system allocator with the arguments it was given.
unsafe impl GlobalAlloc for Recording {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        record(p, l.size());
        p
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(l) };
        record(p, l.size());
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        forget(p, l.size());
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, l, new) };
        if !q.is_null() {
            forget(p, l.size());
            record(q, new);
        }
        q
    }
}

#[global_allocator]
static RECORDING: Recording = Recording;

unsafe extern "C" {
    fn mincore(addr: *mut u8, len: usize, vec: *mut u8) -> i32;
}

/// The resident bytes of the recorded allocations that are live.
fn resident() -> usize {
    const PAGE: usize = 4096;
    let was = TRACK.with(|t| t.replace(false));
    // Room for every entry before the lock is taken: a reallocation under it would free, and freeing takes the lock.
    let mut live: Vec<(usize, usize)> = Vec::with_capacity(CAP);
    locked(|| {
        for i in 0..CAP {
            let p = PTRS[i].load(Relaxed);
            if !matches!(p, 0 | GONE) {
                live.push((p, SIZES[i].load(Relaxed)));
            }
        }
    });
    let mut pages = std::collections::BTreeSet::new();
    let mut map = Vec::new();
    for (p, size) in live {
        let (start, end) = (p & !(PAGE - 1), (p + size).next_multiple_of(PAGE));
        map.resize((end - start) / PAGE, 0u8);
        // SAFETY: the range covers a live allocation, rounded out to whole pages, and `map` has a byte per page.
        assert_eq!(unsafe { mincore(start as *mut u8, end - start, map.as_mut_ptr()) }, 0);
        pages.extend(
            map.iter()
                .enumerate()
                .filter(|(_, b)| **b & 1 == 1)
                .map(|(k, _)| start + k * PAGE),
        );
    }
    TRACK.with(|t| t.set(was));
    pages.len() * PAGE
}

#[test]
fn a_client_holds_little_for_an_endpoint_and_for_a_quiet_session() {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let rt = nuclei::Builder::new().build().unwrap();
        rt.block_on(async move {
            let server = node().await;
            tx.send(server.addr()).unwrap();
            std::future::pending::<()>().await
        })
    });
    let addr = rx.recv_timeout(Duration::from_secs(30)).unwrap();
    let rt = nuclei::Builder::new().build().unwrap();
    let (endpoint, session) = rt.block_on(async move {
        TRACK.with(|t| t.set(true));
        let before = resident();
        let mut eps = Vec::new();
        for _ in 0..CLIENTS {
            eps.push(
                bind_idle(Vinc::builder().alpn(SINK).limits(Limits {
                    connections: 1,
                    ..Limits::default()
                }))
                .await,
            );
        }
        let built = resident();
        let payload = vec![0x5a_u8; 64 * 1024];
        let mut held = Vec::new();
        for ep in &eps {
            let conn = ep.connect(addr.clone(), SINK).await.unwrap();
            let (mut tx, mut rx) = conn.open_bi().await.unwrap();
            tx.write_all(&payload).await.unwrap();
            tx.finish().await.unwrap();
            let reply = rx.read_to_end(1024).await.unwrap();
            assert_eq!(reply[..8], (64u64 * 1024).to_le_bytes());
            held.push(conn);
        }
        drop(payload);
        nuclei::time::sleep(Duration::from_millis(300)).await;
        let quiet = resident();
        TRACK.with(|t| t.set(false));
        drop((held, eps));
        ((built - before) / CLIENTS, quiet.saturating_sub(built) / CLIENTS)
    });
    eprintln!("an endpoint holds {endpoint} B, a quiet session adds {session} B");
    assert!(
        endpoint <= ENDPOINT_MAX,
        "an endpoint holds {endpoint} B, above {ENDPOINT_MAX}"
    );
    assert!(
        session <= SESSION_MAX,
        "a quiet session adds {session} B, above {SESSION_MAX}"
    );
}

/// The sessions of the burst, all on one client endpoint and all moving their 64 KiB at once; fewer than the 64 the
/// server's accept queue holds.
const BURST: usize = 48;
/// The most memory a session of the burst may leave resident beyond what the live allocations hold, once the burst
/// is quiet, both ends counted. It leaves 75 to 94 KiB, freed memory other than the pool's that malloc keeps; before
/// vinc#435 it left 201 to 212 KiB: the 16 KiB pool chunks its streams freed stayed in malloc's heap under the
/// sessions that outlived them, resident, though nothing held them.
const RETAINED_MAX: usize = 144 * 1024;

/// The process's resident bytes, from the system.
fn process_resident() -> usize {
    let statm = std::fs::read_to_string("/proc/self/statm").unwrap();
    let pages: usize = statm.split_whitespace().nth(1).unwrap().parse().unwrap();
    pages * 4096
}

#[test]
fn a_quiet_burst_gives_its_freed_pool_memory_back_to_the_system() {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let rt = nuclei::Builder::new().build().unwrap();
        rt.block_on(async move {
            TRACK.with(|t| t.set(true));
            let server = node().await;
            tx.send(server.addr()).unwrap();
            std::future::pending::<()>().await
        })
    });
    let addr = rx.recv_timeout(Duration::from_secs(30)).unwrap();
    let rt = nuclei::Builder::new().build().unwrap();
    let (grown, live) = rt.block_on(async move {
        TRACK.with(|t| t.set(true));
        let ep = bind_idle(Vinc::builder().alpn(SINK).limits(Limits {
            connections: BURST,
            ..Limits::default()
        }))
        .await;
        let payload = std::rc::Rc::new(vec![0x5a_u8; 64 * 1024]);
        let (rss, live) = (process_resident(), resident());
        let tasks: Vec<_> = (0..BURST)
            .map(|_| {
                let (ep, addr, payload) = (ep.clone(), addr.clone(), std::rc::Rc::clone(&payload));
                nuclei::spawn_local(async move {
                    let conn = ep.connect(addr, SINK).await.unwrap();
                    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
                    tx.write_all(&payload).await.unwrap();
                    tx.finish().await.unwrap();
                    let reply = rx.read_to_end(1024).await.unwrap();
                    assert_eq!(reply[..8], (64u64 * 1024).to_le_bytes());
                    conn
                })
            })
            .collect();
        let mut held = Vec::new();
        for t in tasks {
            held.push(t.await);
        }
        nuclei::time::sleep(Duration::from_millis(300)).await;
        let grown = process_resident().saturating_sub(rss);
        let live = resident().saturating_sub(live);
        TRACK.with(|t| t.set(false));
        drop((held, ep));
        (grown, live)
    });
    let retained = grown.saturating_sub(live) / BURST;
    eprintln!(
        "a quiet burst of {BURST}: resident grew {} KiB a session, live allocations {} KiB, retained {} B",
        grown / BURST / 1024,
        live / BURST / 1024,
        retained
    );
    assert!(
        retained <= RETAINED_MAX,
        "a quiet session of the burst leaves {retained} B resident that nothing holds, above {RETAINED_MAX}"
    );
}

/// The largest live allocation the recorded threads made.
fn largest_live() -> usize {
    let was = TRACK.with(|t| t.replace(false));
    let largest = locked(|| {
        (0..CAP)
            .filter(|&i| !matches!(PTRS[i].load(Relaxed), 0 | GONE))
            .map(|i| SIZES[i].load(Relaxed))
            .max()
            .unwrap_or(0)
    });
    TRACK.with(|t| t.set(was));
    largest
}

/// The largest live allocation of a client while one session of it has 64 KiB written and not yet acknowledged.
fn largest_while_busy(limits: Limits) -> usize {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let rt = nuclei::Builder::new().build().unwrap();
        rt.block_on(async move {
            let server = node().await;
            tx.send(server.addr()).unwrap();
            std::future::pending::<()>().await
        })
    });
    let addr = rx.recv_timeout(Duration::from_secs(30)).unwrap();
    let rt = nuclei::Builder::new().build().unwrap();
    rt.block_on(async move {
        TRACK.with(|t| t.set(true));
        let ep = bind_idle(Vinc::builder().alpn(SINK).limits(limits)).await;
        let conn = ep.connect(addr, SINK).await.unwrap();
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        tx.write_all(&vec![0x5a_u8; 64 * 1024]).await.unwrap();
        let largest = largest_live();
        tx.finish().await.unwrap();
        let _ = rx.read_to_end(1024).await.unwrap();
        TRACK.with(|t| t.set(false));
        largest
    })
}

#[test]
#[cfg(target_env = "gnu")]
fn a_session_takes_its_pool_from_segments_unless_the_limits_turn_them_off() {
    const SEGMENT: usize = 32 << 20;
    let on = largest_while_busy(Limits {
        connections: 1,
        ..Limits::default()
    });
    let off = largest_while_busy(Limits {
        connections: 1,
        pool_segments: false,
        ..Limits::default()
    });
    eprintln!("the largest live allocation of a busy session: {on} B with segments, {off} B without");
    assert!(Limits::default().pool_segments, "segments are on by default on 64-bit Linux with glibc");
    assert_eq!(on, SEGMENT, "the default pool takes its chunks from a segment of 32 MiB");
    assert!(off < SEGMENT, "with segments off the pool takes 16 KiB chunks, not segments ({off} B)");
}
