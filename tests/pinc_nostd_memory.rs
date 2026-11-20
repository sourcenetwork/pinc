//! The memory of an endpoint and of one session on a host without an executor or `std`, measured as the bytes its
//! allocations hold: two endpoints on a platform of their own, in memory, connect and echo 64 bytes on one stream.
//!
//! The figures are those of this 64-bit build host, not of a microcontroller: a pointer, a `usize` and every table of
//! them are twice as wide there, and what a 32-bit target holds is not measured yet. The counting allocator counts the
//! bytes an allocation asked for, as reserved, not as the system commits them (`pinc_client_memory` reads the resident
//! bytes of a client instead); it counts per side, so the two endpoints are told apart: each is polled with its side
//! set, and the links hold their datagrams in room made before the count starts, so no allocation crosses sides.
#![allow(
    unsafe_code,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::large_futures,
    clippy::semicolon_if_nothing_returned,
    missing_docs
)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::{Cell, RefCell};
use std::collections::VecDeque;
use std::future::{Future, poll_fn};
use std::net::SocketAddr;
use std::pin::pin;
use std::rc::Rc;
use std::sync::atomic::{AtomicIsize, Ordering::Relaxed};
use std::task::{Context, Poll, Waker};

use pinc::{Endpoint, Hosted, Limits, Pinc, Platform};

/// The most an endpoint with no session may hold, in bytes: it holds 1,861,229 (the server) and 1,860,549 (the
/// client). 1,048,576 of that is the spill arena of the default limits (128 slots of 8,192 bytes), allocated whole
/// when the endpoint is built; the rest stays under the 869,000 it had before the arena.
const BUILT_MAX: isize = 869_000 + 1_048_576;
/// The most one connected session that echoed 64 bytes may add, in bytes: it adds 2,857,873 (the server) and 2,867,821
/// (the client), nearly all of it the room reserved for the slot's tables, which is written as the session uses it
/// (`SLOT_BYTES` in `mem.rs` is 2,844,952).
const SESSION_MAX: isize = 3_155_000;

const NONE: usize = 0;
const SERVER: usize = 1;
const CLIENT: usize = 2;

static LIVE: [AtomicIsize; 3] = [const { AtomicIsize::new(0) }; 3];

thread_local! {
    /// The side whose code this thread runs now.
    static SIDE: Cell<usize> = const { Cell::new(NONE) };
}

fn side(s: usize) {
    SIDE.with(|c| c.set(s));
}

fn live(s: usize) -> isize {
    LIVE[s].load(Relaxed)
}

fn add(by: isize) {
    LIVE[SIDE.with(Cell::get)].fetch_add(by, Relaxed);
}

struct Counting;

// SAFETY: every method forwards its arguments unchanged to `System`, which upholds the `GlobalAlloc` contract; the
// counters are atomics and never allocate.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        if !p.is_null() {
            add(l.size() as isize);
        }
        p
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(l) };
        if !p.is_null() {
            add(l.size() as isize);
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        add(-(l.size() as isize));
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, l, new) };
        if !q.is_null() {
            add(new as isize - l.size() as isize);
        }
        q
    }
}

#[global_allocator]
static COUNTING: Counting = Counting;

#[derive(Debug)]
struct Down;

impl pinc::HostError for Down {
    fn is_transient(&self) -> bool {
        true
    }
}

#[derive(Default)]
struct World {
    ticks: Cell<u64>,
    moved: Cell<u64>,
    deadline: Cell<Option<u64>>,
}

struct Board {
    world: Rc<World>,
    state: Cell<u64>,
}

impl Platform for Board {
    type Instant = u64;
    type Error = Down;

    fn now(&self) -> u64 {
        self.world.ticks.get()
    }

    fn wall_ns(&self) -> u64 {
        0
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Down> {
        for chunk in out.chunks_mut(8) {
            let z = self.state.get().wrapping_add(0x9E37_79B9_7F4A_7C15);
            self.state.set(z);
            let z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            chunk.copy_from_slice(&(z ^ (z >> 31)).to_le_bytes()[..chunk.len()]);
        }
        Ok(())
    }
}

/// A datagram in room of its own: a link never allocates once it is made.
type Datagram = ([u8; 1536], usize, SocketAddr);
type Queue = Rc<RefCell<VecDeque<Datagram>>>;

fn queue() -> Queue {
    Rc::new(RefCell::new(VecDeque::with_capacity(64)))
}

const ALPN: &[u8] = b"t/echo";

fn host(
    world: &Rc<World>,
    seed: u64,
    local: SocketAddr,
    (inbox, outbox): (&Queue, &Queue),
    limits: Limits,
) -> Endpoint<impl Hosted> {
    let board = Board {
        world: Rc::clone(world),
        state: Cell::new(seed),
    };
    let (w, inbox, outbox) = (Rc::clone(world), Rc::clone(inbox), Rc::clone(outbox));
    let (wr, ws) = (Rc::clone(&w), Rc::clone(&w));
    Pinc::builder_on(board)
        .limits(limits)
        .alpn(ALPN)
        .local_addr(local)
        .build(
            async move |buf: &mut [u8]| {
                poll_fn(|_| match inbox.borrow_mut().pop_front() {
                    Some((datagram, n, from)) => {
                        wr.moved.set(wr.moved.get() + 1);
                        let n = n.min(buf.len());
                        buf[..n].copy_from_slice(&datagram[..n]);
                        Poll::Ready(Ok((n, from)))
                    }
                    None => Poll::Pending,
                })
                .await
            },
            async move |packet: &[u8], _to: SocketAddr| {
                let mut queue = outbox.borrow_mut();
                if queue.len() == 64 || packet.len() > 1536 {
                    return Err(Down);
                }
                let mut datagram = [0u8; 1536];
                datagram[..packet.len()].copy_from_slice(packet);
                queue.push_back((datagram, packet.len(), local));
                ws.moved.set(ws.moved.get() + 1);
                Ok(packet.len())
            },
            async move |at: u64| {
                poll_fn(|_| {
                    if w.ticks.get() >= at {
                        return Poll::Ready(());
                    }
                    w.deadline.set(Some(w.deadline.get().map_or(at, |d| d.min(at))));
                    Poll::Pending
                })
                .await
            },
        )
        .unwrap()
}

async fn serve(server: &Endpoint<impl Hosted>) {
    while let Some(incoming) = server.accept().await {
        let conn = incoming.into_connection();
        while let Ok((mut tx, mut rx)) = conn.accept_bi().await {
            while let Ok(Some(chunk)) = rx.read_chunk(4096).await {
                if tx.write_all(&chunk).await.is_err() {
                    return;
                }
            }
            let _ = tx.finish().await;
        }
    }
}

#[test]
fn the_memory_of_an_endpoint_and_of_one_session_on_a_host_without_std() {
    let world = Rc::new(World::default());
    let (to_server, to_client) = (queue(), queue());
    let at = |port| SocketAddr::from(([127, 0, 0, 1], port));
    let limits = Limits {
        connections: 1,
        pool_chunks: 8,
        ..Limits::default()
    };
    side(SERVER);
    let server = host(&world, 1, at(4001), (&to_server, &to_client), limits);
    side(CLIENT);
    let client = host(&world, 2, at(4002), (&to_client, &to_server), limits);
    side(NONE);
    let built = [live(SERVER), live(CLIENT)];

    let message = [0x5a_u8; 64];
    let to = server.addr();
    let mut serving = pin!(serve(&server));
    let mut running = pin!(client.run());
    let mut echoing = pin!(async {
        let conn = client.connect(to, ALPN).await?;
        let (mut tx, mut rx) = conn.open_bi().await?;
        tx.write_all(&message).await?;
        tx.finish().await?;
        let back = rx.read_to_end(1 << 16).await?;
        assert_eq!(back, message);
        Ok::<_, pinc::Error>(conn)
    });
    let mut cx = Context::from_waker(Waker::noop());
    let (mut conn, mut quiet, mut settled) = (None, 0, 0);
    while settled < 100 {
        world.deadline.set(None);
        let before = world.moved.get();
        side(SERVER);
        let _ = serving.as_mut().poll(&mut cx);
        side(CLIENT);
        let _ = running.as_mut().poll(&mut cx);
        if conn.is_none() {
            if let Poll::Ready(c) = echoing.as_mut().poll(&mut cx) {
                conn = Some(c.unwrap());
            }
        } else {
            settled += 1;
        }
        side(NONE);
        quiet = if world.moved.get() == before { quiet + 1 } else { 0 };
        if quiet >= 4 {
            let Some(next) = world.deadline.get() else { break };
            world.ticks.set(next.max(world.ticks.get()));
            quiet = 0;
        }
    }
    assert!(conn.is_some(), "the echo did not finish");
    let session = [live(SERVER) - built[0], live(CLIENT) - built[1]];
    println!(
        "bytes live on the 64-bit build host: server {} with no session, a session adds {}; client {} with no \
         session, a session adds {}",
        built[0], session[0], built[1], session[1]
    );
    for (built, session) in built.into_iter().zip(session) {
        assert!(
            built <= BUILT_MAX,
            "an endpoint with no session holds {built} B, above {BUILT_MAX}"
        );
        assert!(
            session <= SESSION_MAX,
            "a session adds {session} B, above {SESSION_MAX}"
        );
    }
    side(NONE);
}
