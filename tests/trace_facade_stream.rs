//! Trace generation for the stream and datagram handles of the facade (`crates/pinc/src/stream.rs`, `conn.rs`,
//! `engine/ops.rs`): real endpoints over an in-memory wire and a virtual clock, recorded as ndjson for the TLA+ trace
//! checks `TraceFacadeStream.tla` (the code as written, `facade_stream.ndjson`) and `TraceFacadeStreamDoc.tla` (the
//! documented behaviour, `facade_stream_doc.ndjson`).
//!
//! A run connects two endpoints; the peer opens a stream and writes one chunk, the subject accepts it. The subject
//! then calls write, finish, reset, read, stop, the datagram calls, close and the drops of its halves, the peer sends
//! chunks, finishes, resets, stops, sends datagrams, closes and reads what the subject wrote. Every call and every
//! action is followed by a settled world, so each recorded call meets what the calls before it made. A call that
//! would wait is polled once and dropped (r 3). The second test records the behaviour the documentation promises and
//! the code does not have today: it is expected to fail the documented trace check until the code is fixed.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::await_holding_refcell_ref,
    clippy::type_complexity,
    clippy::many_single_char_names,
    clippy::struct_excessive_bools,
    dead_code,
    unreachable_pub,
    missing_docs
)]

mod facade_world;
#[path = "trace_facade_stream_runs.rs"]
mod runs;

use std::cell::{Cell, RefCell};
use std::fmt::Write as _;
use std::future::{Future, poll_fn};
use std::pin::pin;
use std::rc::Rc;
use std::task::{Poll, Waker};

use facade_world::{Exec, PEER, PEER_BASE, SUBJECT, Wire, settle, settle_until};
use pinc::trace_waits;
use pinc::{Connection, Endpoint, ErrorKind, Hosted, Limits, RecvStream, SendStream};
use pinc_tests::SplitMix64;

const ALPN: &[u8] = b"trace/stream";
type Slot<T> = Rc<RefCell<Option<T>>>;

/// The codes of the model's constants.
const RC: u64 = 7;
const SC: u64 = 3;
const PR: u64 = 5;
const PC: u64 = 6;
const PCC: u64 = 9;
const LC: u64 = 11;

/// A result as the records show it.
#[derive(Clone, Copy, Default)]
struct Res {
    r: u32,
    k: u32,
    c: u64,
    v: u64,
}

impl Res {
    const fn ok(v: u64) -> Self {
        Self { r: 0, k: 0, c: 0, v }
    }

    const fn end(v: u64) -> Self {
        Self { r: 1, k: 0, c: 0, v }
    }

    fn err(e: pinc::Error) -> Self {
        let c = match e.kind() {
            ErrorKind::Stopped(c) | ErrorKind::Reset(c) | ErrorKind::Closed { code: c, .. } => c,
            _ => 0,
        };
        Self {
            r: 2,
            k: trace_waits::kind_code(e.kind()),
            c,
            v: 0,
        }
    }

    const PENDING: Self = Self { r: 3, k: 0, c: 0, v: 0 };
}

enum Out<H: Hosted> {
    Unit,
    Res(Res),
    Conn(Connection<H>),
    Bi(SendStream<H>, RecvStream<H>),
    Uni(RecvStream<H>),
    Send(SendStream<H>),
}

fn slot<T>(v: Option<T>) -> Slot<T> {
    Rc::new(RefCell::new(v))
}

fn chunk(j: u64) -> [u8; 32] {
    [j as u8; 32]
}

// ---- the subject's calls ----

async fn write_c<H: Hosted + 'static>(s: Slot<SendStream<H>>, j: u64, count: u64) -> Out<H> {
    let mut g = s.borrow_mut();
    let Some(s) = g.as_mut() else {
        panic!("write on a dropped stream")
    };
    Out::Res(match s.write(&chunk(j)).await {
        Ok(n) => {
            assert_eq!(n, 32, "a write took part of a chunk");
            Res::ok(count)
        }
        Err(e) => Res::err(e),
    })
}

async fn finish_c<H: Hosted + 'static>(s: Slot<SendStream<H>>) -> Out<H> {
    let mut g = s.borrow_mut();
    let Some(s) = g.as_mut() else {
        panic!("finish on a dropped stream")
    };
    Out::Res(s.finish().await.map_or_else(Res::err, |()| Res::ok(0)))
}

async fn reset_c<H: Hosted + 'static>(s: Slot<SendStream<H>>) -> Out<H> {
    let mut g = s.borrow_mut();
    let Some(s) = g.as_mut() else {
        panic!("reset on a dropped stream")
    };
    s.reset(RC).await;
    Out::Res(Res::ok(0))
}

/// A chunk of 32 equal bytes: its byte, else a failure.
fn chunk_byte(buf: &[u8; 32], n: usize) -> u64 {
    assert_eq!(n, 32, "a chunk arrived in pieces");
    assert!(buf.iter().all(|b| *b == buf[0]), "a chunk arrived in pieces");
    u64::from(buf[0])
}

async fn read_c<H: Hosted + 'static>(r: Slot<RecvStream<H>>) -> Out<H> {
    let mut g = r.borrow_mut();
    let Some(r) = g.as_mut() else {
        panic!("read on a dropped stream")
    };
    let mut buf = [0u8; 32];
    Out::Res(match r.read(&mut buf).await {
        Ok(Some(n)) => Res::ok(chunk_byte(&buf, n)),
        Ok(None) => Res::end(0),
        Err(e) => Res::err(e),
    })
}

async fn stop_c<H: Hosted + 'static>(r: Slot<RecvStream<H>>) -> Out<H> {
    let mut g = r.borrow_mut();
    let Some(r) = g.as_mut() else {
        panic!("stop on a dropped stream")
    };
    r.stop(SC).await;
    Out::Res(Res::ok(0))
}

async fn rdg_c<H: Hosted + 'static>(c: Connection<H>, fit: bool) -> Out<H> {
    let mut buf = vec![0u8; if fit { 64 } else { 4 }];
    Out::Res(match c.recv_datagram(&mut buf).await {
        Ok(n) => {
            assert_eq!(n, 8, "a datagram is 8 bytes");
            Res::ok(u64::from(buf[0]))
        }
        Err(e) => Res::err(e),
    })
}

async fn sdg_c<H: Hosted + 'static>(c: Connection<H>, big: bool, count: u64) -> Out<H> {
    let data = vec![9u8; if big { 65_536 } else { 8 }];
    Out::Res(c.send_datagram(&data).await.map_or_else(Res::err, |()| Res::ok(count)))
}

async fn close_c<H: Hosted + 'static>(c: Connection<H>, code: u64) -> Out<H> {
    c.close(code).await;
    Out::Res(Res::ok(0))
}

async fn run_ep<H: Hosted + 'static>(e: Endpoint<H>) -> Out<H> {
    let _ = e.run().await;
    Out::Unit
}

async fn connect<H: Hosted + 'static>(e: Endpoint<H>, to: Endpoint<H>) -> Out<H> {
    match e.connect(to.addr(), ALPN).await {
        Ok(c) => Out::Conn(c),
        Err(e) => panic!("connect failed: {e:?}"),
    }
}

async fn accept_conn<H: Hosted + 'static>(e: Endpoint<H>) -> Out<H> {
    match e.accept().await {
        Some(i) => Out::Conn(i.into_connection()),
        None => panic!("the peer's endpoint stopped"),
    }
}

async fn accept_bi<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    match c.accept_bi().await {
        Ok((s, r)) => Out::Bi(s, r),
        Err(e) => panic!("accept failed: {e:?}"),
    }
}

async fn accept_uni<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    match c.accept_uni().await {
        Ok(r) => Out::Uni(r),
        Err(e) => panic!("accept failed: {e:?}"),
    }
}

// ---- the peer's actions ----

/// The peer's side of the run's stream.
struct Peer<H: Hosted> {
    send: Slot<SendStream<H>>,
    recv: Slot<RecvStream<H>>,
    /// The chunks the peer wrote, and the next datagram's number is `dgrams + 1`.
    chunks: Cell<u64>,
    dgrams: Cell<u64>,
    read: Cell<u64>,
    saw_end: Cell<bool>,
}

async fn peer_open<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    let (mut s, r) = c.open_bi().await.expect("the peer opens a stream");
    s.write_all(&chunk(1)).await.expect("the peer writes");
    Out::Bi(s, r)
}

/// Open a stream and write one byte on it, keeping every half open.
async fn peer_open_byte<H: Hosted + 'static>(c: Connection<H>, uni: bool) -> Out<H> {
    if uni {
        let mut s = c.open_uni().await.expect("the peer opens a stream");
        s.write_all(&[1]).await.expect("the peer writes");
        Out::Send(s)
    } else {
        let (mut s, r) = c.open_bi().await.expect("the peer opens a stream");
        s.write_all(&[1]).await.expect("the peer writes");
        Out::Bi(s, r)
    }
}

/// Finish the sending half of every stream in `halves`, and drop them.
async fn finish_halves<H: Hosted + 'static>(halves: Vec<Out<H>>) -> Out<H> {
    for h in halves {
        if let Out::Bi(mut s, _recv) = h {
            s.finish().await.expect("the peer finishes");
        }
    }
    Out::Unit
}

async fn peer_send<H: Hosted + 'static>(p: Rc<Peer<H>>) -> Out<H> {
    let j = p.chunks.get() + 1;
    let mut g = p.send.borrow_mut();
    let s = g.as_mut().expect("the peer's send half");
    s.write_all(&chunk(j)).await.expect("the peer writes a chunk");
    p.chunks.set(j);
    Out::Res(Res::ok(0))
}

async fn peer_fin<H: Hosted + 'static>(p: Rc<Peer<H>>) -> Out<H> {
    let mut g = p.send.borrow_mut();
    g.as_mut()
        .expect("the peer's send half")
        .finish()
        .await
        .expect("the peer finishes");
    Out::Res(Res::ok(0))
}

async fn peer_reset<H: Hosted + 'static>(p: Rc<Peer<H>>) -> Out<H> {
    p.send
        .borrow_mut()
        .as_mut()
        .expect("the peer's send half")
        .reset(PR)
        .await;
    Out::Res(Res::ok(0))
}

async fn peer_stop<H: Hosted + 'static>(p: Rc<Peer<H>>) -> Out<H> {
    p.recv
        .borrow_mut()
        .as_mut()
        .expect("the peer's recv half")
        .stop(PC)
        .await;
    Out::Res(Res::ok(0))
}

async fn peer_dg<H: Hosted + 'static>(c: Connection<H>, j: u64) -> Out<H> {
    c.send_datagram(&[j as u8; 8]).await.expect("the peer sends a datagram");
    Out::Res(Res::ok(0))
}

/// Read until a read would wait, the end or an error; as the peer's `pread` record.
async fn peer_read<H: Hosted + 'static>(p: Rc<Peer<H>>) -> Out<H> {
    if p.saw_end.get() {
        return Out::Res(Res::end(p.read.get()));
    }
    let mut g = p.recv.borrow_mut();
    let r = g.as_mut().expect("the peer's recv half");
    loop {
        let mut buf = [0u8; 32];
        let step = {
            let mut f = pin!(r.read(&mut buf));
            poll_fn(|cx| {
                Poll::Ready(match f.as_mut().poll(cx) {
                    Poll::Ready(v) => Some(v),
                    Poll::Pending => None,
                })
            })
            .await
        };
        match step {
            Some(Ok(Some(n))) => {
                let j = p.read.get() + 1;
                assert_eq!(chunk_byte(&buf, n), j, "the peer read a chunk out of order");
                p.read.set(j);
            }
            Some(Ok(None)) => {
                p.saw_end.set(true);
                return Out::Res(Res::end(p.read.get()));
            }
            Some(Err(e)) => return Out::Res(Res::err(e)),
            None => {
                return Out::Res(Res {
                    r: 3,
                    v: p.read.get(),
                    ..Res::default()
                });
            }
        }
    }
}

// ---- one run ----

struct T<H: Hosted> {
    w: Wire,
    x: Exec<Out<H>>,
    out: String,
    subject: Endpoint<H>,
    peer: Endpoint<H>,
    sconn: Option<Connection<H>>,
    pconn: Option<Connection<H>>,
    s: Slot<SendStream<H>>,
    r: Slot<RecvStream<H>>,
    recv_id: u64,
    p: Rc<Peer<H>>,
    next_p: u32,
    writes_ok: u64,
    reads_ok: u64,
    sends_ok: u64,
    /// Streams kept open so their halves are not dropped.
    keep: Vec<Out<H>>,
}

fn fresh(seed: u64) -> T<impl Hosted + 'static> {
    fresh_with(seed, Limits::default())
}

fn fresh_with(seed: u64, limits: Limits) -> T<impl Hosted + 'static> {
    let w = Wire::new(SplitMix64::traced(seed));
    let subject = w.endpoint(SUBJECT.parse().unwrap(), 1, ALPN, limits);
    let peer = w.endpoint(PEER.parse().unwrap(), 2, ALPN, limits);
    T {
        w,
        x: Exec::new(),
        out: String::new(),
        subject,
        peer,
        sconn: None,
        pconn: None,
        s: slot(None),
        r: slot(None),
        recv_id: 0,
        p: Rc::new(Peer {
            send: slot(None),
            recv: slot(None),
            chunks: Cell::new(0),
            dgrams: Cell::new(0),
            read: Cell::new(0),
            saw_end: Cell::new(false),
        }),
        next_p: 0,
        writes_ok: 0,
        reads_ok: 0,
        sends_ok: 0,
        keep: Vec::new(),
    }
}

impl<H: Hosted + 'static> T<H> {
    /// Settle, then let 100 ms of virtual time pass, so that what the transport holds back (its pacing and its delayed
    /// acknowledgements) is sent before the next step.
    fn settle(&mut self) {
        settle(&self.w, &mut self.x, &mut |_| {});
        let end = self.w.virt.now.get() + 100_000_000;
        while let Some(wakers) = self.w.advance_to(end) {
            wakers.into_iter().for_each(Waker::wake);
            settle(&self.w, &mut self.x, &mut |_| {});
        }
    }

    fn spawn(&mut self, fut: impl Future<Output = Out<H>> + 'static) -> u32 {
        let id = PEER_BASE + self.next_p;
        self.next_p += 1;
        self.x.spawn(id, false, fut);
        id
    }

    /// Run a future that must finish; its output.
    fn finish(&mut self, fut: impl Future<Output = Out<H>> + 'static) -> Out<H> {
        let id = self.spawn(fut);
        self.settle();
        let reason = (
            self.sconn.as_ref().map(Connection::close_reason),
            self.pconn.as_ref().map(Connection::close_reason),
        );
        let pending = self.x.pending();
        self.x
            .done
            .remove(&id)
            .unwrap_or_else(|| panic!("an action did not finish: {id} {pending:?} {reason:?}"))
    }

    /// Run a call of the subject: still pending after the world settled is r 3, and the call is dropped.
    fn call(&mut self, fut: impl Future<Output = Out<H>> + 'static) -> Res {
        let id = self.spawn(fut);
        self.settle();
        match self.x.done.remove(&id) {
            Some(Out::Res(r)) => r,
            Some(_) => panic!("a call returned something else"),
            None => {
                self.x.drop_task(id);
                Res::PENDING
            }
        }
    }

    fn rec(&mut self, head: &str, r: Res) {
        writeln!(
            self.out,
            r#"{{"t":"fst",{head},"r":{},"k":{},"c":{},"v":{}}}"#,
            r.r, r.k, r.c, r.v
        )
        .unwrap();
    }

    fn conn(&self) -> Connection<H> {
        self.sconn.clone().unwrap()
    }

    fn pc(&self) -> Connection<H> {
        self.pconn.clone().unwrap()
    }

    fn live(&self) -> bool {
        self.conn().close_reason().is_none()
    }

    /// Connect, the peer opens a stream and writes chunk 1, the subject accepts it; `init` is recorded.
    fn begin(&mut self) {
        self.spawn(run_ep(self.subject.clone()));
        self.spawn(run_ep(self.peer.clone()));
        let c = self.spawn(connect(self.subject.clone(), self.peer.clone()));
        let a = self.spawn(accept_conn(self.peer.clone()));
        self.settle_until(&mut |x| x.done.contains_key(&c) && x.done.contains_key(&a));
        let (Some(Out::Conn(sc)), Some(Out::Conn(pc))) = (self.x.done.remove(&c), self.x.done.remove(&a)) else {
            panic!("the endpoints did not connect");
        };
        self.sconn = Some(sc);
        self.pconn = Some(pc);
        let Out::Bi(ps, pr) = self.finish(peer_open(self.pc())) else {
            panic!("no stream")
        };
        *self.p.send.borrow_mut() = Some(ps);
        *self.p.recv.borrow_mut() = Some(pr);
        self.p.chunks.set(1);
        let Out::Bi(s, r) = self.finish(accept_bi(self.conn())) else {
            panic!("no stream")
        };
        self.recv_id = r.id();
        *self.s.borrow_mut() = Some(s);
        *self.r.borrow_mut() = Some(r);
        writeln!(self.out, r#"{{"t":"fst","op":"init","pw":1,"r":0,"k":0,"c":0,"v":0}}"#).unwrap();
    }

    fn settle_until(&mut self, cond: &mut dyn FnMut(&Exec<Out<H>>) -> bool) {
        settle_until(&self.w, &mut self.x, &mut |_| {}, cond);
    }

    fn await_close(&mut self) {
        let c = self.conn();
        self.settle_until(&mut |_| c.close_reason().is_some());
    }

    // The subject's calls, each recorded.

    fn write(&mut self) -> Res {
        let j = self.writes_ok + 1;
        let r = self.call(write_c(Rc::clone(&self.s), j, j));
        if r.r == 0 {
            self.writes_ok += 1;
        }
        self.rec(r#""op":"write""#, r);
        r
    }

    fn finish_s(&mut self) -> Res {
        let r = self.call(finish_c(Rc::clone(&self.s)));
        self.rec(r#""op":"finish""#, r);
        r
    }

    fn reset(&mut self) -> Res {
        let r = self.call(reset_c(Rc::clone(&self.s)));
        self.rec(r#""op":"reset""#, r);
        r
    }

    fn dsend(&mut self) {
        drop(self.s.borrow_mut().take());
        self.settle();
        self.rec(r#""op":"dsend""#, Res::ok(0));
    }

    fn read(&mut self) -> Res {
        let r = self.call(read_c(Rc::clone(&self.r)));
        if r.r == 0 {
            self.reads_ok += 1;
            assert_eq!(r.v, self.reads_ok, "the subject read a chunk out of order");
        }
        self.rec(r#""op":"read""#, r);
        r
    }

    fn stop(&mut self) -> Res {
        let r = self.call(stop_c(Rc::clone(&self.r)));
        self.rec(r#""op":"stop""#, r);
        r
    }

    fn drecv(&mut self) {
        drop(self.r.borrow_mut().take());
        self.settle();
        self.rec(r#""op":"drecv""#, Res::ok(0));
    }

    fn rdg(&mut self, fit: bool) -> Res {
        let r = self.call(rdg_c(self.conn(), fit));
        self.rec(&format!(r#""op":"rdg","fit":{fit}"#), r);
        r
    }

    fn sdg(&mut self, big: bool) -> Res {
        let r = self.call(sdg_c(self.conn(), big, self.sends_ok + 1));
        if r.r == 0 {
            self.sends_ok += 1;
        }
        self.rec(&format!(r#""op":"sdg","big":{big}"#), r);
        r
    }

    fn close(&mut self) {
        let r = self.call(close_c(self.conn(), LC));
        self.await_close();
        self.rec(r#""op":"close""#, r);
    }

    // The peer's actions, each recorded.

    fn pclose(&mut self) {
        self.finish(close_c(self.pc(), PCC));
        self.await_close();
        self.rec(r#""op":"pclose""#, Res::ok(0));
    }

    fn psend(&mut self) {
        self.finish(peer_send(Rc::clone(&self.p)));
        self.rec(r#""op":"psend""#, Res::ok(0));
    }

    fn pfin(&mut self) {
        self.finish(peer_fin(Rc::clone(&self.p)));
        self.rec(r#""op":"pfin""#, Res::ok(0));
    }

    fn preset(&mut self) {
        self.finish(peer_reset(Rc::clone(&self.p)));
        self.rec(r#""op":"preset""#, Res::ok(0));
    }

    fn pstop(&mut self) {
        self.finish(peer_stop(Rc::clone(&self.p)));
        self.rec(r#""op":"pstop""#, Res::ok(0));
    }

    fn pdg(&mut self) {
        let j = self.p.dgrams.get() + 1;
        self.finish(peer_dg(self.pc(), j));
        self.p.dgrams.set(j);
        self.rec(r#""op":"pdg""#, Res::ok(0));
    }

    fn pread(&mut self) -> Res {
        let Out::Res(r) = self.finish(peer_read(Rc::clone(&self.p))) else {
            panic!("no result")
        };
        self.rec(r#""op":"pread""#, r);
        r
    }

    fn held(&mut self) -> bool {
        let held = self.conn().trace_held(self.recv_id);
        self.rec(r#""op":"held""#, Res::ok(u64::from(held)));
        held
    }
}

fn expect(r: Res, (rr, k, c): (u32, u32, u64), what: &str) {
    assert_eq!((r.r, r.k, r.c), (rr, k, c), "{what}");
}

const KIND_STOPPED: u32 = 1;
const KIND_RESET: u32 = 2;
const KIND_CLOSED_BY_PEER: u32 = 3;
const KIND_CLOSED_LOCAL: u32 = 4;
const KIND_TOO_LARGE: u32 = 5;

fn write_file(name: &str, out: &str) {
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join(name), out).unwrap();
    }
}

#[test]
fn the_stream_handles_match_the_model() {
    let mut out = String::new();
    for n in 1..=10 {
        let mut t = fresh(0x7374_7200 + u64::from(n));
        runs::fixed(n, &mut t);
        out.push_str(&t.out);
    }
    for run in 0..40u64 {
        let mut t = fresh(0x7374_7300 + run);
        runs::seeded(&mut t, 0x6673_746d + run);
        out.push_str(&t.out);
    }
    if !pinc_tests::soaking() {
        for op in [
            "write", "finish", "read", "held", "rdg", "sdg", "pread", "pclose", "close", "pdg",
        ] {
            assert!(out.contains(&format!(r#""op":"{op}""#)), "no {op} was recorded");
        }
    }
    write_file("facade_stream.ndjson", &out);
}

// ---- the documented behaviour ----

fn documented<H: Hosted + 'static>(n: u32, t: &mut T<H>) {
    t.begin();
    match n {
        1 => {
            t.reset();
            t.write();
            t.finish_s();
        }
        2 => {
            // The list of discarded streams passes the 128 streams a session used to remember: the subject opens 29
            // two-way streams and drops their receiving halves, then the peer opens 99 more (with the stream of
            // `begin`, the 100 it may hold), the subject accepts each and drops its receiving half, and last the
            // stream of `begin` is dropped with unread bytes. A dropped stream is always discarded, so it holds nothing.
            let mut local = Vec::new();
            for _ in 0..29 {
                if let Out::Bi(s, _recv) = t.finish(peer_open_byte(t.conn(), false)) {
                    local.push(Out::Send(s));
                }
            }
            let mut peer_halves = Vec::new();
            for _ in 0..99 {
                peer_halves.push(t.finish(peer_open_byte(t.pc(), false)));
                if let Out::Bi(s, _recv) = t.finish(accept_bi(t.conn())) {
                    local.push(Out::Send(s));
                }
            }
            t.psend();
            t.drecv();
            let held = t.held();
            assert!(!held, "a stream dropped after 128 others still held what the peer sent");
            t.finish(finish_halves(peer_halves));
            t.finish(peer_fin(Rc::clone(&t.p)));
            drop(t.s.borrow_mut().take());
            drop(local);
            t.settle();
        }
        _ => {
            t.pdg();
            t.pdg();
            t.pclose();
            t.rdg(true);
            t.rdg(true);
            t.rdg(true);
        }
    }
}

#[test]
fn the_documented_stream_scenarios() {
    let mut out = String::new();
    for n in 1..=3 {
        // A stream is charged its whole window of the pool from its first byte; the smallest window lets 100 streams
        // hold data at once.
        let limits = Limits {
            stream_window: 16 * 1024,
            ..Limits::default()
        };
        let mut t = fresh_with(0x646f_6300 + u64::from(n), limits);
        documented(n, &mut t);
        out.push_str(&t.out);
    }
    write_file("facade_stream_doc.ndjson", &out);
}
