//! A complete host on a platform of its own: the one a host without `std` copies, in memory.
//!
//! The host brings a counter clock in nanoseconds, an error type and a source of randomness (the [`Board`], a
//! [`Platform`]), and the three closures of the endpoint over two queues in memory. There is no executor: the host's
//! own loop polls the futures it has, and when nothing moved for some rounds it lets the clock reach the nearest
//! deadline. Two endpoints connect and one echoes what the other sends. Nothing in the host names `std` but `main`
//! (it prints).
//!
//! Run with `cargo run -p pinc --example platform`.

#![allow(
    missing_docs,
    unreachable_pub,
    clippy::missing_errors_doc,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::large_futures,
    reason = "an example favours the short form"
)]

extern crate alloc;

use alloc::collections::VecDeque;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::future::{Future, poll_fn};
use core::net::SocketAddr;
use core::pin::pin;
use core::task::{Context, Poll, Waker};

use pinc::{Endpoint, Error, ErrorKind, HostError, Hosted, Limits, Pinc, Platform};

const ALPN: &[u8] = b"example/platform/1";

/// The datagrams a queue holds before it drops one, as a radio's buffer does.
const QUEUE: usize = 256;

/// Rounds of the loop in which nothing moved before time is allowed to pass.
const QUIET: u32 = 4;

/// The host's own error type: the link refused a datagram.
#[derive(Debug)]
pub struct Down;

impl HostError for Down {
    /// A refused send loses one datagram and nothing else.
    fn is_transient(&self) -> bool {
        true
    }
}

/// What the endpoints of the host share: the counter clock, how many datagrams moved, and the nearest deadline a
/// sleeping endpoint asked for.
#[derive(Default)]
struct World {
    ticks: Cell<u64>,
    moved: Cell<u64>,
    deadline: Cell<Option<u64>>,
}

/// The host's platform: the counter clock, no wall clock, and a generator of its own.
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

    /// This host does not know the date.
    fn wall_ns(&self) -> u64 {
        0
    }

    /// A stand-in: a real host fills `out` from its hardware generator. This one (splitmix64) is predictable and
    /// serves only to make the example run.
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

/// The datagrams waiting for one endpoint, with the address each came from.
type Queue = Rc<RefCell<VecDeque<(Vec<u8>, SocketAddr)>>>;

/// An endpoint over `world` whose datagrams arrive in `inbox` and leave into `outbox`.
fn endpoint(
    world: &Rc<World>,
    seed: u64,
    local: SocketAddr,
    (inbox, outbox): (&Queue, &Queue),
) -> pinc::Result<Endpoint<impl Hosted>> {
    let board = Board {
        world: Rc::clone(world),
        state: Cell::new(seed),
    };
    let (w, inbox, outbox) = (Rc::clone(world), Rc::clone(inbox), Rc::clone(outbox));
    let (wr, ws) = (Rc::clone(&w), Rc::clone(&w));
    Pinc::builder_on(board)
        .limits(Limits::wasm())
        .alpn(ALPN)
        .local_addr(local)
        .build(
            async move |buf: &mut [u8]| {
                poll_fn(|_| match inbox.borrow_mut().pop_front() {
                    Some((datagram, from)) => {
                        wr.moved.set(wr.moved.get() + 1);
                        let n = datagram.len().min(buf.len());
                        buf[..n].copy_from_slice(&datagram[..n]);
                        Poll::Ready(Ok((n, from)))
                    }
                    None => Poll::Pending,
                })
                .await
            },
            async move |packet: &[u8], _to: SocketAddr| {
                let mut queue = outbox.borrow_mut();
                if queue.len() == QUEUE {
                    return Err(Down);
                }
                // The only peer of an endpoint is the other one, which is told whose datagram this is.
                queue.push_back((packet.to_vec(), local));
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
                .await;
            },
        )
}

/// The server: it takes one session and echoes each stream the peer opens.
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

/// The client: it connects, sends `message` on a stream, reads it back and closes.
async fn echo(client: &Endpoint<impl Hosted>, server: pinc::NodeAddr, message: &[u8]) -> pinc::Result<Vec<u8>> {
    let conn = client.connect(server, ALPN).await?;
    let (mut tx, mut rx) = conn.open_bi().await?;
    tx.write_all(message).await?;
    tx.finish().await?;
    let back = rx.read_to_end(1 << 16).await?;
    conn.close(0).await;
    Ok(back)
}

/// Two endpoints in memory connect and the first echoes `message` through the second; returns what came back.
pub fn run(message: &[u8]) -> pinc::Result<Vec<u8>> {
    let world = Rc::new(World::default());
    let (to_server, to_client): (Queue, Queue) = (Queue::default(), Queue::default());
    let (server_at, client_at) = (
        SocketAddr::from(([127, 0, 0, 1], 4001)),
        SocketAddr::from(([127, 0, 0, 1], 4002)),
    );
    let server = endpoint(&world, 1, server_at, (&to_server, &to_client))?;
    let client = endpoint(&world, 2, client_at, (&to_client, &to_server))?;

    let mut serving = pin!(serve(&server));
    let mut echoing = pin!(echo(&client, server.addr(), message));
    let mut cx = Context::from_waker(Waker::noop());
    let mut quiet = 0;
    loop {
        world.deadline.set(None);
        let before = world.moved.get();
        let _ = serving.as_mut().poll(&mut cx);
        if let Poll::Ready(back) = echoing.as_mut().poll(&mut cx) {
            return back;
        }
        quiet = if world.moved.get() == before { quiet + 1 } else { 0 };
        if quiet >= QUIET {
            // Nothing moved for some rounds: time passes, to the nearest deadline anyone asked for.
            let Some(at) = world.deadline.get() else {
                return Err(Error::new(ErrorKind::TimedOut, "nothing is waiting for time to pass"));
            };
            world.ticks.set(at.max(world.ticks.get()));
            quiet = 0;
        }
    }
}

#[allow(dead_code)]
fn main() {
    match run(b"hello, pinc") {
        Ok(b) => println!("echoed: {}", String::from_utf8_lossy(&b)),
        Err(e) => eprintln!("failed: {e}"),
    }
}
