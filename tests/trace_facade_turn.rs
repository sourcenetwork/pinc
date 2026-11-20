//! Trace generation for the drive's turn (`crates/pinc/src/drive.rs`: `Shared::run_as`, the guard `Turn`, `flush`, over
//! the slab of `standby.rs`), recorded as ndjson (`facade_turn.ndjson`) for the TLA+ trace check `TraceFacadeTurn.tla`.
//!
//! Endpoint A runs no `Endpoint::run`: its facade calls (a dial, accepts of streams, a receive and a send of a datagram) are
//! tasks 1.. of the manual executor, and whichever of them waits takes the driving role. A peer endpoint B runs on
//! tasks from 100. The probe module `pinc::trace_turn` marks each step of a call; the test gives each mark the task
//! that was polled (or dropped), maps the ticket of a notification to the task that holds it, and writes the datagrams
//! that reached A's socket (`arrive`) and the firing of a sleep of A (`hostwake`) in their place. Nothing is written
//! when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::type_complexity,
    dead_code,
    unreachable_pub,
    missing_docs
)]

mod facade_world;

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::future::Future;
use std::net::SocketAddr;
use std::rc::Rc;

use facade_world::{Ev, Exec, PEER, SUBJECT, Wire, settle};
use pinc::trace_turn::{self, Kind};
use pinc::{Connection, Endpoint, ErrorKind, Hosted, Limits, SendStream};
use pinc_tests::SplitMix64;

const ALPN: &[u8] = b"turn/one";
/// The first task of the peer; the facade calls of A are below.
const PEER_TASK: u32 = 100;
/// The generation bound of the instance (`GENS`).
const GENS: u32 = 1 << 30;

enum Out<H: Hosted> {
    Unit,
    Conn(Connection<H>),
    Fail(ErrorKind),
}

type Kept<H> = Rc<RefCell<Vec<SendStream<H>>>>;
type Conns<H> = Rc<RefCell<Vec<Connection<H>>>>;

async fn run_ep<H: Hosted + 'static>(e: Endpoint<H>) -> Out<H> {
    let _ = e.run().await;
    Out::Unit
}

async fn peer_accept<H: Hosted + 'static>(e: Endpoint<H>, into: Conns<H>) -> Out<H> {
    while let Some(inc) = e.accept().await {
        into.borrow_mut().push(inc.into_connection());
    }
    Out::Unit
}

async fn connect<H: Hosted + 'static>(e: Endpoint<H>, to: Endpoint<H>) -> Out<H> {
    match e.connect(to.addr(), ALPN).await {
        Ok(c) => Out::Conn(c),
        Err(e) => Out::Fail(e.kind()),
    }
}

async fn accept_bi<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    match c.accept_bi().await {
        Ok(_) => Out::Unit,
        Err(e) => Out::Fail(e.kind()),
    }
}

async fn accept_uni<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    match c.accept_uni().await {
        Ok(_) => Out::Unit,
        Err(e) => Out::Fail(e.kind()),
    }
}

async fn recv_dg<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    let mut buf = [0u8; 64];
    match c.recv_datagram(&mut buf).await {
        Ok(_) => Out::Unit,
        Err(e) => Out::Fail(e.kind()),
    }
}

async fn send_dg<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    match c.send_datagram(&[5u8; 8]).await {
        Ok(()) => Out::Unit,
        Err(e) => Out::Fail(e.kind()),
    }
}

/// The peer opens a stream to A and writes to it, keeping its end.
async fn peer_open<H: Hosted + 'static>(c: Connection<H>, uni: bool, keep: Kept<H>) -> Out<H> {
    let mut s = if uni {
        match c.open_uni().await {
            Ok(s) => s,
            Err(e) => return Out::Fail(e.kind()),
        }
    } else {
        match c.open_bi().await {
            Ok((s, _r)) => s,
            Err(e) => return Out::Fail(e.kind()),
        }
    };
    if let Err(e) = s.write_all(&[1u8; 4]).await {
        return Out::Fail(e.kind());
    }
    keep.borrow_mut().push(s);
    Out::Unit
}

async fn peer_dgram<H: Hosted + 'static>(c: Connection<H>) -> Out<H> {
    match c.send_datagram(&[3u8; 8]).await {
        Ok(()) => Out::Unit,
        Err(e) => Out::Fail(e.kind()),
    }
}

/// The lines, and what they need to know to write the next one.
#[derive(Default)]
struct Lines {
    out: String,
    /// Datagrams of A's socket already written.
    arrived: usize,
    /// The ticket each task holds, by task: a notification names a ticket.
    held: BTreeMap<(u32, u32), u32>,
    counts: BTreeMap<&'static str, usize>,
    /// The largest generation of a ticket seen.
    max_gen: u32,
    /// Whether some `wait` took datagrams, and some went on to flush.
    took: bool,
    flushed: bool,
    /// The task that drives now, from the last `wait` (cleared when it ends).
    driver_task: Option<u32>,
}

fn code(c: Option<(u32, u32)>) -> String {
    c.map_or_else(|| "[]".to_owned(), |(i, g)| format!("[{i},{g}]"))
}

impl Lines {
    fn put(&mut self, op: &'static str, f: Option<u32>, rest: &str) {
        *self.counts.entry(op).or_default() += 1;
        let f = f.map_or_else(String::new, |f| format!(",\"f\":{f}"));
        writeln!(self.out, "{{\"op\":\"{op}\"{f}{rest}}}").unwrap();
    }

    fn sync(&mut self, w: &Wire, a: SocketAddr) {
        for _ in self.arrived..w.arrived(a) {
            self.put("arrive", None, "");
        }
        self.arrived = w.arrived(a);
    }

    /// Write the marks of the probe, for the task `f` that was polled or dropped.
    fn drain(&mut self, f: u32) {
        // A notification of the polled call's own ticket during its poll wakes its waker, which the executor polls again
        // once the poll returns: in the model, a notification right after the poll's last step.
        let mut own = false;
        // A notification of a ticket this poll allocated: its call is known only from the poll's last mark.
        let mut unmatched = Vec::new();
        for m in trace_turn::take() {
            let state = m.state.map_or_else(String::new, |(flag, driver)| {
                format!(",\"flag\":{flag},\"driver\":{}", code(driver))
            });
            match m.kind {
                Kind::Notify(tk) => match self.held.get(&tk).copied() {
                    Some(h) if h == f => own = true,
                    Some(h) => self.put("notify", Some(h), ""),
                    None => unmatched.push(tk),
                },
                Kind::NotifyAll => self.put("notifyall", None, ""),
                _ if f >= PEER_TASK => panic!("a mark for task {f}, which is not a call of the subject"),
                Kind::Start => self.put("start", Some(f), &state),
                Kind::Io => self.put("io", Some(f), &state),
                Kind::Done => self.put("done", Some(f), &state),
                Kind::Flush => self.put("flush", Some(f), &state),
                Kind::Wait { tk, drv, took, flush } => {
                    assert!(tk.1 < GENS, "a generation reached the bound of the instance");
                    self.max_gen = self.max_gen.max(tk.1);
                    self.took |= took > 0;
                    self.flushed |= flush;
                    self.held.retain(|_, h| *h != f);
                    self.held.insert(tk, f);
                    if drv {
                        self.driver_task = Some(f);
                    }
                    let rest = format!(
                        ",\"tk\":[{},{}],\"drv\":{drv},\"took\":{took},\"flush\":{flush}{state}",
                        tk.0, tk.1
                    );
                    self.put("wait", Some(f), &rest);
                }
                Kind::Return | Kind::Drop | Kind::Taken => {
                    self.held.retain(|_, h| *h != f);
                    if self.driver_task == Some(f) {
                        self.driver_task = None;
                    }
                    let op = match m.kind {
                        Kind::Drop => "drop",
                        Kind::Taken => "taken",
                        _ => "flush",
                    };
                    self.put(op, Some(f), &state);
                }
            }
        }
        // A notification of a ticket nobody holds after the poll does nothing: it is not a step.
        for tk in unmatched {
            match self.held.get(&tk).copied() {
                Some(h) if h == f => own = true,
                Some(h) => self.put("notify", Some(h), ""),
                None => {}
            }
        }
        // Held still: the call ended its poll waiting. Ended, or done: the wake finds nothing to poll.
        if own && self.held.values().any(|h| *h == f) {
            self.put("notify", Some(f), "");
        }
    }

    fn on<O>(&mut self, w: &Wire, a: SocketAddr, ev: &Ev<'_, O>) {
        match *ev {
            Ev::Before(_) | Ev::WakeStart | Ev::WakeEnd => self.sync(w, a),
            Ev::After(id, _) => self.drain(id),
        }
    }
}

struct T<H: Hosted + 'static> {
    w: Wire,
    x: Exec<Out<H>>,
    a: Endpoint<H>,
    b: Endpoint<H>,
    addr: SocketAddr,
    lines: RefCell<Lines>,
    pconns: Conns<H>,
    keep: Kept<H>,
    peer: u32,
}

impl<H: Hosted + 'static> T<H> {
    fn settle(&mut self) {
        let (w, l, a) = (&self.w, &self.lines, self.addr);
        settle(w, &mut self.x, &mut |ev| l.borrow_mut().on(w, a, &ev));
    }

    fn spawn(&mut self, id: u32, fut: impl Future<Output = Out<H>> + 'static) {
        self.x.spawn(id, false, fut);
    }

    /// A task of the peer, run to its end.
    fn peer(&mut self, fut: impl Future<Output = Out<H>> + 'static) {
        let id = self.peer;
        self.peer += 1;
        self.x.spawn(id, false, fut);
        self.settle();
        let _ = self.x.done.remove(&id);
    }

    fn drop_task(&mut self, id: u32) {
        let (w, a) = (&self.w, self.addr);
        self.lines.borrow_mut().sync(w, a);
        assert!(self.x.drop_task(id), "task {id} was pending");
        self.lines.borrow_mut().drain(id);
    }

    fn pconn(&self) -> Connection<H> {
        self.pconns.borrow()[0].clone()
    }

    fn finished(&mut self, id: u32) -> bool {
        self.x.done.contains_key(&id)
    }

    /// Fire the next timers `n` times; a timer of A is a `hostwake` line, written before it wakes.
    fn timers(&mut self, n: usize) {
        for _ in 0..n {
            let Some(ws) = self.w.advance() else { return };
            {
                let (w, a) = (&self.w, self.addr);
                let mut l = self.lines.borrow_mut();
                l.sync(w, a);
                if w.fired(a) {
                    l.put("hostwake", None, "");
                }
            }
            for k in ws {
                k.wake();
            }
            self.settle();
        }
    }
}

fn run<H: Hosted + 'static>(w: Wire, a: Endpoint<H>, b: Endpoint<H>) {
    let addr: SocketAddr = SUBJECT.parse().unwrap();
    let _ = trace_turn::take();
    a.trace_waits();
    let mut t = T {
        w,
        x: Exec::new(),
        a,
        b,
        addr,
        lines: RefCell::default(),
        pconns: Rc::default(),
        keep: Rc::default(),
        peer: PEER_TASK + 2,
    };
    t.x.spawn(PEER_TASK, false, run_ep(t.b.clone()));
    t.x.spawn(PEER_TASK + 1, false, peer_accept(t.b.clone(), Rc::clone(&t.pconns)));
    // A dial: the first call to wait takes the role and drives the handshake.
    t.spawn(1, connect(t.a.clone(), t.b.clone()));
    t.settle();
    assert!(t.finished(1), "the dial ended");
    let Some(Out::Conn(c)) = t.x.done.remove(&1) else {
        panic!("the dial failed")
    };
    assert!(!t.pconns.borrow().is_empty(), "the peer accepted the session");
    // Three calls wait together: the first takes the role, the others wait on their tickets.
    t.spawn(2, accept_bi(c.clone()));
    t.spawn(3, accept_uni(c.clone()));
    t.spawn(4, recv_dg(c.clone()));
    t.settle();
    assert!(!t.finished(2) && !t.finished(3) && !t.finished(4), "three calls wait");
    // The peer opens a stream: the driver reads the datagrams, and the call that waited for it returns and passes the
    // role on.
    let (pc, keep) = (t.pconn(), Rc::clone(&t.keep));
    t.peer(peer_open(pc.clone(), false, Rc::clone(&keep)));
    assert!(t.finished(2), "the accept of the stream returned");
    // A datagram: the call that waits for it returns.
    t.peer(peer_dgram(pc.clone()));
    assert!(t.finished(4), "the receive of the datagram returned");
    // A call whose payload is the send: A's datagram flushes before the call returns (a done line, then a flush),
    // where the calls above took their value out and returned it in the poll that took it (taken lines).
    t.spawn(7, send_dg(c.clone()));
    t.settle();
    assert!(t.finished(7), "the datagram of A was sent");
    // Two more calls wait; the host drops the one that drives, and a waiting one takes the role.
    t.spawn(5, accept_bi(c.clone()));
    t.spawn(6, recv_dg(c.clone()));
    t.settle();
    let driver = t.lines.borrow().driver_task.expect("a call drives");
    t.drop_task(driver);
    t.settle();
    assert!(t.lines.borrow().driver_task.is_some(), "another call took the role");
    // Time passes: the sleeps of the driver fire.
    t.timers(3);
    // The peer opens a stream and a unidirectional stream; the calls that wait for them return.
    t.peer(peer_open(pc.clone(), false, Rc::clone(&keep)));
    t.peer(peer_open(pc, true, keep));
    // Whatever still waits is dropped, the driver among them.
    for id in t.x.pending().into_iter().filter(|id| *id < PEER_TASK) {
        t.drop_task(id);
    }
    t.settle();
    {
        let (w, a) = (&t.w, t.addr);
        t.lines.borrow_mut().sync(w, a);
    }
    let l = t.lines.borrow();
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("facade_turn.ndjson"), &l.out).unwrap();
    }
    // Every step of the turn the run reaches, and what it cannot: `notifyall` needs the core's event queue to
    // overflow, which no run of this size does and which the facade's public API cannot make one burst do.
    for op in [
        "start", "io", "done", "taken", "wait", "flush", "drop", "notify", "arrive", "hostwake",
    ] {
        assert!(l.counts.get(op).copied().unwrap_or(0) > 0, "no {op} line was written");
    }
    assert!(l.counts["drop"] >= 2, "the host dropped calls");
    assert!(l.took, "a wait took datagrams from the host");
    assert!(l.flushed, "a wait went on to flush");
    assert!(l.max_gen > 0, "a slot was taken again");
    assert!(l.max_gen < GENS);
    assert!(l.counts["start"] >= 6, "six calls started");
}

#[test]
fn trace_facade_turn() {
    let w = Wire::new(SplitMix64::traced(31));
    let a = w.endpoint(SUBJECT.parse().unwrap(), 1, ALPN, Limits::default());
    let b = w.endpoint(PEER.parse().unwrap(), 2, ALPN, Limits::default());
    run(w, a, b);
}
