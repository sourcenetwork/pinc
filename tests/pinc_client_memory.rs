//! What a client holds (pinc#158, #141): the memory of an endpoint with no session, and of one session that moved 64 KiB
//! and went quiet, as the resident bytes of the client's own allocations.
//!
//! A server runs on a thread of its own; the test thread builds [`CLIENTS`] endpoints of one session each and moves
//! 64 KiB on each, one after the other. The allocator records every allocation of 4 KiB or more the test thread makes,
//! and the system says which of their pages are resident, so the reading does not depend on how lazily the allocator
//! commits a large buffer. Smaller allocations are left out: a few KiB a session.
#![cfg(target_os = "linux")]
#![allow(
    unsafe_code,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_precision_loss,
    clippy::semicolon_if_nothing_returned
)]

mod pinc_common;

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use std::time::Duration;

use pinc::{Limits, Pinc};
use pinc_common::{SINK, bind_idle, node};

/// The client endpoints, one session each.
const CLIENTS: usize = 32;
/// The most an endpoint with no session may hold. It holds 619 KiB; before pinc#158 it held 987 KiB, 464 KiB of it the
/// buffers and queues of the four relay slots, made whether a relay was named or not.
const ENDPOINT_MAX: usize = 704 * 1024;
/// The most a session that moved 64 KiB and went quiet may add to its endpoint. It adds 96 KiB; before pinc#158 it
/// added 161 KiB: a pool segment of 256 KiB written as far as its chunks were used, the endpoint's own receive and
/// transmit buffers, and the handshake machine the endpoint kept for its next handshake.
const SESSION_MAX: usize = 112 * 1024;

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
                bind_idle(Pinc::builder().alpn(SINK).limits(Limits {
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
