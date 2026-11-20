//! Trace generation for the waiters of a facade session (`crates/pinc/src/engine.rs`, `engine/ops.rs`, `drive.rs`):
//! real endpoints over an in-memory wire, a virtual clock and a manual executor whose wakers log which future they wake,
//! recorded as ndjson (`facade_waits.ndjson`) for the TLA+ trace check (`TraceFacadeWaits.tla`).
//!
//! The subject endpoint logs, in one sequence with those wakes, each event its core handles for the session with the
//! session's queues after it, each notification of every waiter, each end of the session, each attempt that ended or
//! registered a wait, each kick and each baton. The test adds the futures it spawns, polls, drops and the results they
//! return. Five fixed runs (accept order and refusal, read and write wakes, datagrams, cancellation, shutdown) and 40
//! seeded runs of 80 steps. After every step the test polls every pending future once more and fails on one that is
//! ready: that is a lost wake.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::await_holding_refcell_ref,
    clippy::type_complexity,
    unreachable_pub,
    missing_docs
)]

mod facade_world;
#[path = "trace_facade_waits_runs.rs"]
mod runs;

use std::cell::{Cell, RefCell};
use std::fmt::Write as _;
use std::future::{Future, poll_fn};
use std::pin::pin;
use std::rc::Rc;
use std::task::Poll;

use facade_world::{Ev, Exec, PEER, PEER_BASE, SUBJECT, Wire, settle, settle_until};
use pinc::trace_waits::{self, Mark};
use pinc::{Connection, Endpoint, ErrorKind, Hosted, Limits, RecvStream, SendStream};
use pinc_tests::SplitMix64;

const ALPN: &[u8] = b"trace/waits";
type Slot<T> = Rc<RefCell<Option<T>>>;

/// What a spawned future returns.
enum Out<H: Hosted> {
    Unit,
    /// Ok; the stream id of an accept or an open, else 0.
    Ok(u64),
    /// `Ok(None)` of a read.
    End,
    Err(pinc::Error),
    Conn(Connection<H>),
}

impl<H: Hosted> Out<H> {
    /// The `r`, `e` and `v` of a `ret` record.
    fn code(&self) -> (u32, u32, u64) {
        match self {
            Self::Unit | Self::End | Self::Conn(_) => (1, 0, 0),
            Self::Ok(v) => (1, 0, *v),
            Self::Err(e) => (2, trace_waits::kind_code(e.kind()), 0),
        }
    }
}

/// A stream of the subject: both halves, in slots so a pending call can keep its half borrowed.
struct SubStream<H: Hosted> {
    id: u64,
    send: Slot<SendStream<H>>,
    recv: Slot<RecvStream<H>>,
    ended: Cell<bool>,
}

type Subs<H> = Rc<RefCell<Vec<Rc<SubStream<H>>>>>;

/// A stream of the peer.
struct PeerStream<H: Hosted> {
    id: u64,
    send: Slot<SendStream<H>>,
    recv: Slot<RecvStream<H>>,
    sent_end: Cell<bool>,
    stopped: Cell<bool>,
}

type Peers<H> = Rc<RefCell<Vec<Rc<PeerStream<H>>>>>;

fn slot<T>(v: Option<T>) -> Slot<T> {
    Rc::new(RefCell::new(v))
}

fn stored<H: Hosted>(subs: &Subs<H>, id: u64, send: Option<SendStream<H>>, recv: Option<RecvStream<H>>) {
    subs.borrow_mut().push(Rc::new(SubStream {
        id,
        send: slot(send),
        recv: slot(recv),
        ended: Cell::new(false),
    }));
}

// ---- the subject's calls ----

async fn accept_bi<H: Hosted + 'static>(c: Connection<H>, subs: Subs<H>) -> Out<H> {
    match c.accept_bi().await {
        Ok((s, r)) => {
            let id = s.id();
            stored(&subs, id, Some(s), Some(r));
            Out::Ok(id)
        }
        Err(e) => Out::Err(e),
    }
}

async fn accept_uni<H: Hosted + 'static>(c: Connection<H>, subs: Subs<H>) -> Out<H> {
    match c.accept_uni().await {
        Ok(r) => {
            let id = r.id();
            stored(&subs, id, None, Some(r));
            Out::Ok(id)
        }
        Err(e) => Out::Err(e),
    }
}

async fn open_bi<H: Hosted + 'static>(c: Connection<H>, subs: Subs<H>) -> Out<H> {
    match c.open_bi().await {
        Ok((s, r)) => {
            let id = s.id();
            stored(&subs, id, Some(s), Some(r));
            Out::Ok(id)
        }
        Err(e) => Out::Err(e),
    }
}

async fn recv_dg<H: Hosted + 'static>(c: Connection<H>, len: usize) -> Out<H> {
    let mut buf = vec![0u8; len];
    match c.recv_datagram(&mut buf).await {
        Ok(_) => Out::Ok(0),
        Err(e) => Out::Err(e),
    }
}

async fn read_s<H: Hosted + 'static>(st: Rc<SubStream<H>>) -> Out<H> {
    let mut buf = [0u8; 4];
    let mut g = st.recv.borrow_mut();
    let Some(r) = g.as_mut() else { return Out::Ok(0) };
    match r.read(&mut buf).await {
        Ok(Some(_)) => Out::Ok(0),
        Ok(None) => {
            st.ended.set(true);
            Out::End
        }
        Err(e) => {
            st.ended.set(true);
            Out::Err(e)
        }
    }
}

async fn write_s<H: Hosted + 'static>(st: Rc<SubStream<H>>) -> Out<H> {
    let mut g = st.send.borrow_mut();
    let Some(s) = g.as_mut() else { return Out::Ok(0) };
    match s.write(&[7u8; 16]).await {
        Ok(_) => Out::Ok(0),
        Err(e) => Out::Err(e),
    }
}

async fn answered<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    match c.answered().await {
        Ok(()) => Out::Ok(0),
        Err(e) => Out::Err(e),
    }
}

async fn closed<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    Out::Err(c.closed().await)
}

async fn run_ep<H: Hosted + 'static>(e: Endpoint<H>) -> Out<H> {
    let _ = e.run().await;
    Out::Unit
}

async fn connect<H: Hosted + 'static>(e: Endpoint<H>, to: Endpoint<H>) -> Out<H> {
    match e.connect(to.addr(), ALPN).await {
        Ok(c) => Out::Conn(c),
        Err(e) => Out::Err(e),
    }
}

async fn ep_close<H: Hosted + 'static>(e: Endpoint<H>) -> Out<H> {
    e.close().await;
    Out::Ok(0)
}

async fn conn_close<H: Hosted + 'static>(c: Connection<H>, code: u64) -> Out<H> {
    c.close(code).await;
    Out::Ok(0)
}

// ---- the peer's actions, which always finish ----

async fn peer_accept<H: Hosted + 'static>(e: Endpoint<H>, into: Slot<Connection<H>>) -> Out<H> {
    let Some(inc) = e.accept().await else {
        return Out::Err(pinc::Error::shutdown());
    };
    *into.borrow_mut() = Some(inc.into_connection());
    Out::Ok(0)
}

/// Accept every stream the subject opens, for the peer's table.
async fn peer_acceptor<H: Hosted + 'static>(c: Connection<H>, peers: Peers<H>) -> Out<H> {
    loop {
        match c.accept_bi().await {
            Ok((s, r)) => peers.borrow_mut().push(Rc::new(PeerStream {
                id: s.id(),
                send: slot(Some(s)),
                recv: slot(Some(r)),
                sent_end: Cell::new(false),
                stopped: Cell::new(false),
            })),
            Err(e) => return Out::Err(e),
        }
    }
}

async fn peer_open<H: Hosted + 'static>(c: Connection<H>, peers: Peers<H>, uni: bool) -> Out<H> {
    let (mut s, r) = if uni {
        match c.open_uni().await {
            Ok(s) => (s, None),
            Err(e) => return Out::Err(e),
        }
    } else {
        match c.open_bi().await {
            Ok((s, r)) => (s, Some(r)),
            Err(e) => return Out::Err(e),
        }
    };
    if let Err(e) = s.write_all(&[1u8; 4]).await {
        return Out::Err(e);
    }
    let id = s.id();
    peers.borrow_mut().push(Rc::new(PeerStream {
        id,
        send: slot(Some(s)),
        recv: slot(r),
        sent_end: Cell::new(false),
        stopped: Cell::new(false),
    }));
    Out::Ok(id)
}

async fn peer_write<H: Hosted + 'static>(ps: Rc<PeerStream<H>>) -> Out<H> {
    let mut g = ps.send.borrow_mut();
    match g.as_mut() {
        Some(s) => match s.write_all(&[2u8; 4]).await {
            Ok(()) => Out::Ok(0),
            Err(e) => Out::Err(e),
        },
        None => Out::Ok(0),
    }
}

async fn peer_finish<H: Hosted + 'static>(ps: Rc<PeerStream<H>>) -> Out<H> {
    ps.sent_end.set(true);
    let mut g = ps.send.borrow_mut();
    match g.as_mut() {
        Some(s) => match s.finish().await {
            Ok(()) => Out::Ok(0),
            Err(e) => Out::Err(e),
        },
        None => Out::Ok(0),
    }
}

async fn peer_reset<H: Hosted + 'static>(ps: Rc<PeerStream<H>>, code: u64) -> Out<H> {
    ps.sent_end.set(true);
    if let Some(s) = ps.send.borrow_mut().as_mut() {
        s.reset(code).await;
    }
    Out::Ok(0)
}

async fn peer_stop<H: Hosted + 'static>(ps: Rc<PeerStream<H>>, code: u64) -> Out<H> {
    ps.stopped.set(true);
    if let Some(r) = ps.recv.borrow_mut().as_mut() {
        r.stop(code).await;
    }
    Out::Ok(0)
}

/// Read what is readable on the peer's half, until a read would wait.
async fn peer_drain<H: Hosted + 'static>(ps: Rc<PeerStream<H>>) -> Out<H> {
    let mut g = ps.recv.borrow_mut();
    let Some(r) = g.as_mut() else { return Out::Ok(0) };
    loop {
        let mut buf = [0u8; 64];
        let mut f = pin!(r.read(&mut buf));
        let step = poll_fn(|cx| {
            Poll::Ready(match f.as_mut().poll(cx) {
                Poll::Ready(v) => Some(v),
                Poll::Pending => None,
            })
        })
        .await;
        if !matches!(step, Some(Ok(Some(_)))) {
            return Out::Ok(0);
        }
    }
}

async fn peer_dgram<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    match c.send_datagram(&[3u8; 8]).await {
        Ok(()) => Out::Ok(0),
        Err(e) => Out::Err(e),
    }
}

// ---- the record log ----

/// One record: its text up to the `woke` list, and the queues an `ev` record gets when its event ends.
struct Rec {
    head: String,
    lists: Option<[Vec<u64>; 3]>,
    woke: Vec<u32>,
}

fn nums<T: ToString>(v: &[T]) -> String {
    format!("[{}]", v.iter().map(ToString::to_string).collect::<Vec<_>>().join(","))
}

#[derive(Default)]
struct Log {
    recs: Vec<Rec>,
    cur: Option<u32>,
    open_ev: Option<usize>,
}

impl Log {
    fn add(&mut self, head: String) {
        self.recs.push(Rec {
            head,
            lists: None,
            woke: Vec::new(),
        });
    }

    /// Turn the marks the probe collected into records, in order.
    fn drain(&mut self) {
        for m in trace_waits::take() {
            match m {
                Mark::EvStart { k, s } => {
                    self.open_ev = Some(self.recs.len());
                    self.add(format!(r#"{{"t":"fw","op":"ev","k":{k},"s":{s}"#));
                }
                Mark::EvEnd { acc, accu, fail } => {
                    let at = self.open_ev.take().expect("an event ended that never began");
                    self.recs[at].lists = Some([acc, accu, fail]);
                }
                Mark::All => self.add(r#"{"t":"fw","op":"all""#.to_owned()),
                Mark::End { e } => self.add(format!(r#"{{"t":"fw","op":"end","e":{e}"#)),
                Mark::SendDrop { s } => self.add(format!(r#"{{"t":"fw","op":"sdrop","s":{s}"#)),
                Mark::Try { key, s } => {
                    let f = self.cur.expect("a wait was logged outside a poll");
                    self.add(format!(r#"{{"t":"fw","op":"try","f":{f},"key":{key},"s":{s}"#));
                }
                Mark::Kick => self.add(r#"{"t":"fw","op":"wake","why":2"#.to_owned()),
                Mark::Pass => self.add(r#"{"t":"fw","op":"wake","why":3"#.to_owned()),
                Mark::Woke(f) => self.recs.last_mut().expect("a wake before any record").woke.push(f),
            }
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn on<H: Hosted>(&mut self, e: Ev<'_, Out<H>>) {
        match e {
            Ev::Before(id) if id < PEER_BASE => {
                self.drain();
                self.cur = Some(id);
                self.add(format!(r#"{{"t":"fw","op":"poll","f":{id}"#));
            }
            Ev::Before(_) => {}
            Ev::After(id, out) => {
                self.drain();
                if id < PEER_BASE {
                    let (r, e, v) = out.map_or((0, 0, 0), Out::code);
                    self.add(format!(r#"{{"t":"fw","op":"ret","f":{id},"r":{r},"e":{e},"v":{v}"#));
                    self.cur = None;
                }
            }
            Ev::WakeStart => {
                self.drain();
                self.add(r#"{"t":"fw","op":"wake","why":1"#.to_owned());
            }
            Ev::WakeEnd => self.drain(),
        }
    }

    fn render(&self) -> String {
        let mut out = String::new();
        for r in &self.recs {
            let lists = r.lists.as_ref().map_or_else(String::new, |[a, b, c]| {
                format!(r#","acc":{},"accu":{},"fail":{}"#, nums(a), nums(b), nums(c))
            });
            writeln!(out, r#"{}{lists},"woke":{}}}"#, r.head, nums(&r.woke)).unwrap();
        }
        out
    }
}

// ---- one run ----

struct T<H: Hosted> {
    w: Wire,
    x: Exec<Out<H>>,
    log: Log,
    subject: Endpoint<H>,
    peer: Endpoint<H>,
    sconn: Option<Connection<H>>,
    pconn: Slot<Connection<H>>,
    next_f: u32,
    next_p: u32,
    subs: Subs<H>,
    peers: Peers<H>,
}

fn fresh(seed: u64) -> T<impl Hosted + 'static> {
    // What the last run's dropped futures logged is not this run's.
    let _ = trace_waits::take();
    let w = Wire::new(SplitMix64::traced(seed));
    let subject = w.endpoint(
        SUBJECT.parse().unwrap(),
        1,
        ALPN,
        Limits {
            accept_streams: 2,
            ..Limits::default()
        },
    );
    let peer = w.endpoint(PEER.parse().unwrap(), 2, ALPN, Limits::default());
    subject.trace_waits();
    T {
        w,
        x: Exec::new(),
        log: Log::default(),
        subject,
        peer,
        sconn: None,
        pconn: slot(None),
        next_f: 0,
        next_p: PEER_BASE,
        subs: Rc::default(),
        peers: Rc::default(),
    }
}

impl<H: Hosted + 'static> T<H> {
    fn settle(&mut self) {
        settle(&self.w, &mut self.x, &mut |e| self.log.on(e));
    }

    fn settle_until(&mut self, cond: &mut dyn FnMut(&Exec<Out<H>>) -> bool) {
        settle_until(&self.w, &mut self.x, &mut |e| self.log.on(e), cond);
    }

    /// Spawn a subject future of `call`, on stream `s`; its id.
    fn spawn_s(&mut self, call: u32, s: u64, fut: impl Future<Output = Out<H>> + 'static) -> u32 {
        self.log.drain();
        let f = self.next_f;
        self.next_f += 1;
        assert!(f < 64, "a run uses at most 63 futures");
        self.log
            .add(format!(r#"{{"t":"fw","op":"spawn","f":{f},"call":{call},"s":{s}"#));
        self.x.spawn(f, true, fut);
        f
    }

    /// Spawn a subject future, settle, and check the rest; its id.
    fn call(&mut self, call: u32, s: u64, fut: impl Future<Output = Out<H>> + 'static) -> u32 {
        let f = self.spawn_s(call, s, fut);
        self.step();
        f
    }

    /// Run one action of the peer to its end, then check the rest.
    fn act(&mut self, fut: impl Future<Output = Out<H>> + 'static) -> Out<H> {
        let id = self.next_p;
        self.next_p += 1;
        self.x.spawn(id, false, fut);
        self.settle();
        let out = self.x.done.remove(&id).expect("an action of the peer did not finish");
        self.rest();
        out
    }

    fn step(&mut self) {
        self.settle();
        self.rest();
    }

    /// The test's own check of `NoLostWake`: every pending future, polled again, still waits.
    fn rest(&mut self) {
        self.log.drain();
        self.log.add(r#"{"t":"fw","op":"rest""#.to_owned());
        for f in self.x.pending() {
            if f >= PEER_BASE {
                continue;
            }
            self.x.poll_one(f, &mut |e| self.log.on(e));
            assert!(!self.x.done.contains_key(&f), "future {f} was ready but nobody woke it");
        }
        self.settle();
    }

    fn drop_f(&mut self, f: u32) {
        if self.x.pending().contains(&f) {
            self.log.drain();
            self.log.add(format!(r#"{{"t":"fw","op":"drop","f":{f}"#));
            self.x.drop_task(f);
            self.log.drain();
        }
    }

    /// The result of a finished future, taken.
    fn result(&mut self, f: u32) -> Out<H> {
        self.x
            .done
            .remove(&f)
            .unwrap_or_else(|| panic!("future {f} has not finished"))
    }

    fn conn(&self) -> Connection<H> {
        self.sconn.clone().unwrap()
    }

    fn pconn(&self) -> Connection<H> {
        self.pconn.borrow().clone().unwrap()
    }

    /// A run starts: the endpoints run, the subject connects, and `answered` and `closed` wait.
    fn begin(&mut self) {
        self.log.add(r#"{"t":"fw","op":"init""#.to_owned());
        let f = self.spawn_s(16, 0, run_ep(self.subject.clone()));
        assert_eq!(f, 0);
        self.x.spawn(self.next_p, false, run_ep(self.peer.clone()));
        self.next_p += 1;
        let f = self.spawn_s(16, 0, connect(self.subject.clone(), self.peer.clone()));
        assert_eq!(f, 1);
        self.x.spawn(
            self.next_p,
            false,
            peer_accept(self.peer.clone(), Rc::clone(&self.pconn)),
        );
        self.next_p += 1;
        let pconn = Rc::clone(&self.pconn);
        self.settle_until(&mut |x| x.done.contains_key(&1) && pconn.borrow().is_some());
        match self.result(1) {
            Out::Conn(c) => self.sconn = Some(c),
            Out::Err(e) => panic!("connect failed: {e:?}"),
            _ => panic!("connect returned something else"),
        }
        let (c1, c2) = (self.conn(), self.conn());
        assert_eq!(self.call(9, 0, answered(c1)), 2);
        assert_eq!(self.call(4, 0, closed(c2)), 3);
    }

    fn accept_bi(&mut self) -> u32 {
        let (c, subs) = (self.conn(), Rc::clone(&self.subs));
        self.call(1, 0, accept_bi(c, subs))
    }

    fn accept_uni(&mut self) -> u32 {
        let (c, subs) = (self.conn(), Rc::clone(&self.subs));
        self.call(2, 0, accept_uni(c, subs))
    }

    fn recv_dg(&mut self, len: usize) -> u32 {
        let c = self.conn();
        self.call(3, 0, recv_dg(c, len))
    }

    fn read(&mut self, st: &Rc<SubStream<H>>) -> u32 {
        self.call(7, st.id, read_s(Rc::clone(st)))
    }

    fn write(&mut self, st: &Rc<SubStream<H>>) -> u32 {
        self.call(8, st.id, write_s(Rc::clone(st)))
    }

    fn sub(&self, i: usize) -> Rc<SubStream<H>> {
        Rc::clone(&self.subs.borrow()[i])
    }

    fn peer_open(&mut self, uni: bool) -> u64 {
        let (c, peers) = (self.pconn(), Rc::clone(&self.peers));
        match self.act(peer_open(c, peers, uni)) {
            Out::Ok(id) => id,
            _ => panic!("the peer could not open a stream"),
        }
    }

    fn peer_stream(&self, i: usize) -> Rc<PeerStream<H>> {
        Rc::clone(&self.peers.borrow()[i])
    }

    fn peer_dgram(&mut self) {
        let c = self.pconn();
        self.act(peer_dgram(c));
    }

    fn peer_close(&mut self, code: u64) {
        let c = self.pconn();
        self.act(conn_close(c, code));
        let s = self.conn();
        self.settle_until(&mut |_| s.close_reason().is_some());
        self.rest();
    }

    /// The result of `f` is an error of `kind`.
    fn expect_err(&mut self, f: u32, kind: ErrorKind) {
        match self.result(f) {
            Out::Err(e) => assert_eq!(e.kind(), kind, "future {f}"),
            _ => panic!("future {f} did not return an error"),
        }
    }

    fn expect_ids(&mut self, fs: &[u32], ids: &[u64]) {
        for (f, id) in fs.iter().zip(ids) {
            match self.result(*f) {
                Out::Ok(got) => assert_eq!(got, *id, "future {f} took the wrong stream"),
                _ => panic!("future {f} did not return a stream"),
            }
        }
    }
}

#[test]
fn the_waiters_of_a_session_match_the_model() {
    let mut out = String::new();
    let mut add = |t: &mut T<_>| out.push_str(&t.log.render());
    let mut t = fresh(0x7761_6974);
    runs::run_accept_order(&mut t);
    add(&mut t);
    drop(t);
    let mut t = fresh(0x7761_6975);
    runs::run_read_write(&mut t);
    add(&mut t);
    drop(t);
    let mut t = fresh(0x7761_6976);
    runs::run_datagrams(&mut t);
    add(&mut t);
    drop(t);
    let mut t = fresh(0x7761_6977);
    runs::run_cancel(&mut t);
    add(&mut t);
    drop(t);
    let mut t = fresh(0x7761_6978);
    runs::run_shutdown(&mut t);
    add(&mut t);
    drop(t);
    for run in 0..40u64 {
        let mut t = fresh(0x7769_7265 + run);
        runs::run_seeded(&mut t, 0x6661_6377 + run);
        add(&mut t);
        drop(t);
    }
    if !pinc_tests::soaking() {
        for needle in [r#""op":"end""#, r#""op":"drop""#, r#""op":"try","f":"#, r#","key":0,"#] {
            assert!(out.contains(needle), "no record has {needle}");
        }
        assert!(
            out.lines()
                .any(|l| l.contains(r#""op":"ev","k":5,"#) && !l.contains(r#""fail":[]"#)),
            "no stream was refused"
        );
        assert!(
            out.lines()
                .any(|l| l.contains(r#""op":"try""#) && !l.contains(r#""key":0,"#)),
            "no wait was registered"
        );
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("facade_waits.ndjson"), &out).unwrap();
    }
}
