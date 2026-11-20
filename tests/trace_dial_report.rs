//! Trace generation for the dial report (`crates/pinc/src/conn.rs`, `engine.rs`, the handshake of `pinc-transport`),
//! recorded as ndjson (`dial_report.ndjson`) for the TLA+ trace check `TraceDialReport.tla`.
//!
//! Endpoint A dials a peer P in the shared world of `facade_world.rs`, one tick (500 ms) of virtual time at a time. The
//! test writes a line before it acts (a tick, a stop of P, a cut, a dial, ...), when the world has settled, and a line
//! for what A's application sees as it sees it (a dial that returned, `Connection::answered` that returned, a
//! connection that closed). The run: a dial answered at once; an optimistic dial that rides a cut and is answered after
//! the heal; an optimistic dial to a peer that stopped, which ends early; one to a peer that came back as a new
//! incarnation, which rejects the ticket; and a dial without a cached allow to a peer that stopped, which fails at the
//! handshake's limit; and, on a node made thin by a slow round trip, a dial handed over to a peer that stopped, which has
//! no early end and closes at the limit. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::type_complexity,
    dead_code,
    unreachable_pub,
    missing_docs
)]

mod facade_world;

use std::cell::{Cell, RefCell};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::future::Future;
use std::net::SocketAddr;
use std::rc::Rc;
use std::time::Duration;

use facade_world::{Ev, Exec, PEER, SUBJECT, Wire, settle};
use pinc::{AllowAll, Connection, Endpoint, ErrorKind, Hosted, Limits, NodeAddr};
use pinc_crypto::NodeId;
use pinc_tests::SplitMix64;

const ALPN: &[u8] = b"dial/report";
const TICK: u64 = 500_000_000;
/// The handshake's limit in ticks (30 s).
const LIMIT: u64 = 60;
/// A little over the round trip from which a node is thin (250 ms), as nanoseconds.
const THIN_RTT: u64 = 300_000_000;

enum Out<H: Hosted> {
    Unit,
    Dial(pinc::Result<Connection<H>>),
    Answered(pinc::Result<()>),
    Closed { answered: bool },
}

/// What the application of A sees, as lines.
struct Seen {
    out: Rc<RefCell<String>>,
    tick: Rc<Cell<u64>>,
    dial_at: Rc<Cell<u64>>,
    /// The dials that returned already answered, by task: decided when `connect` returns, not later.
    returned_answered: RefCell<BTreeSet<u32>>,
}

impl Seen {
    fn line(&self, s: &str) {
        writeln!(self.out.borrow_mut(), "{s}").unwrap();
    }

    fn observe<H: Hosted>(&self, ev: &Ev<'_, Out<H>>) {
        let Ev::After(id, Some(o)) = *ev else { return };
        match o {
            Out::Dial(Ok(c)) if c.is_answered() => {
                self.returned_answered.borrow_mut().insert(id);
                self.line(r#"{"op":"answered","how":"return"}"#);
            }
            Out::Dial(Err(e)) => {
                assert_eq!(
                    e.kind(),
                    ErrorKind::TimedOut,
                    "a dial fails only at the handshake's limit"
                );
                self.line(r#"{"op":"failed"}"#);
            }
            Out::Answered(Ok(())) => self.line(r#"{"op":"answered","how":"event"}"#),
            Out::Closed { answered: true } => self.line(r#"{"op":"drop"}"#),
            // The facade tells an early end and the limit apart by nothing but when: the early end comes at most 15
            // ticks into a dial, the limit past 60.
            Out::Closed { answered: false } => {
                let why = if self.tick.get() - self.dial_at.get() > LIMIT {
                    "limit"
                } else {
                    "early"
                };
                self.line(&format!("{{\"op\":\"closed\",\"why\":\"{why}\"}}"));
            }
            Out::Dial(Ok(_)) | Out::Answered(Err(_)) | Out::Unit => {}
        }
    }
}

struct R<H: Hosted + 'static> {
    w: Wire,
    x: Exec<Out<H>>,
    a: Endpoint<H>,
    p: Option<(Endpoint<H>, u32)>,
    pid: NodeId,
    paddr: NodeAddr,
    seen: Seen,
    cached: bool,
    next: u32,
    pending: Vec<u32>,
    conn: Option<Connection<H>>,
}

fn addr(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

fn world<H: Hosted + 'static>(wire: Wire, subject: Endpoint<H>, peer: Endpoint<H>) -> R<H> {
    let pid = peer.id();
    let paddr = peer.addr();
    let mut r = R {
        w: wire,
        x: Exec::new(),
        a: subject,
        p: None,
        pid,
        paddr,
        seen: Seen {
            out: Rc::default(),
            tick: Rc::default(),
            dial_at: Rc::default(),
            returned_answered: RefCell::default(),
        },
        cached: false,
        next: 0,
        pending: Vec::new(),
        conn: None,
    };
    let ep = r.a.clone();
    r.spawn(async move {
        let _ = ep.run().await;
        Out::Unit
    });
    r.start_peer(peer);
    r.settle();
    r
}

impl<H: Hosted + 'static> R<H> {
    fn spawn(&mut self, fut: impl Future<Output = Out<H>> + 'static) -> u32 {
        self.next += 1;
        self.x.spawn(self.next, false, fut);
        self.next
    }

    fn start_peer(&mut self, p: Endpoint<H>) {
        let e = p.clone();
        let id = self.spawn(async move {
            let _ = e.run().await;
            Out::Unit
        });
        self.p = Some((p, id));
    }

    fn settle(&mut self) {
        let seen = &self.seen;
        settle(&self.w, &mut self.x, &mut |ev| seen.observe(&ev));
    }

    /// The dials that finished get their watchers: `answered` and `closed` of the connection they gave.
    fn collect(&mut self) {
        let mut again = false;
        for id in std::mem::take(&mut self.pending) {
            match self.x.done.remove(&id) {
                Some(Out::Dial(Ok(c))) => {
                    let (c1, c2) = (c.clone(), c.clone());
                    // A dial that returned answered is the `return` line; only a handed-over one is awaited.
                    if !self.seen.returned_answered.borrow().contains(&id) {
                        self.spawn(async move { Out::Answered(c1.answered().await) });
                    }
                    self.spawn(async move {
                        let _ = c2.closed().await;
                        Out::Closed {
                            answered: c2.is_answered(),
                        }
                    });
                    self.conn = Some(c);
                    again = true;
                }
                Some(_) => {}
                None => self.pending.push(id),
            }
        }
        if again {
            self.settle();
        }
    }

    fn line(&self, s: &str) {
        self.seen.line(s);
    }

    /// A line of the test's own, written with the world settled: first the change of A's cached allow, if any.
    fn own(&mut self, s: &str) {
        let cached = self.a.trace_gate(&[self.pid]).expect("the core is free").cache[0] == Some(true);
        if cached != self.cached {
            self.cached = cached;
            self.line(&format!("{{\"op\":\"cache\",\"allow\":{cached}}}"));
        }
        self.line(s);
    }

    fn tick(&mut self) {
        self.own(r#"{"op":"tick"}"#);
        self.seen.tick.set(self.seen.tick.get() + 1);
        self.run_to(self.seen.tick.get() * TICK);
        self.collect();
    }

    /// Move the clock to `to`, firing the timers on the way and settling after each.
    fn run_to(&mut self, to: u64) {
        for _ in 0..10_000 {
            let Some(ws) = self.w.advance_to(to) else { break };
            for k in ws {
                k.wake();
            }
            self.settle();
        }
        self.settle();
    }

    /// A dial whose first answer takes `ns` to reach A: a round trip longer than the node's thin bound, no tick.
    fn slow_dial(&mut self, ns: u64) {
        self.w.hold(addr(SUBJECT), true);
        self.dial();
        let to = self.w.virt.now.get() + ns;
        self.run_to(to);
        self.w.hold(addr(SUBJECT), false);
        self.settle();
        self.collect();
    }

    fn count(&self, op: &str) -> usize {
        self.seen
            .out
            .borrow()
            .lines()
            .filter(|l| l.starts_with(&format!("{{\"op\":\"{op}\"")))
            .count()
    }

    /// Tick until the application saw one more `op`, at most `max` ticks.
    fn until(&mut self, op: &str, max: usize) {
        let n = self.count(op);
        for _ in 0..max {
            if self.count(op) > n {
                return;
            }
            self.tick();
        }
        assert!(
            self.count(op) > n,
            "no {op} within {max} ticks (pending {:?}, queued {:?}, wire clock {}): {}",
            self.x.pending(),
            self.w.queued(),
            self.seen.tick.get(),
            self.seen
                .out
                .borrow()
                .replace('\n', " ")
                .replace("{\"op\":\"tick\"} ", "T ")
        );
    }

    fn dial(&mut self) {
        self.own(r#"{"op":"dial"}"#);
        self.seen.dial_at.set(self.seen.tick.get());
        let (a, to) = (self.a.clone(), self.paddr.clone());
        let id = self.spawn(async move { Out::Dial(a.connect(to, ALPN).await) });
        self.pending.push(id);
        self.settle();
        self.collect();
    }

    fn done(&mut self) {
        self.own(r#"{"op":"done"}"#);
    }

    /// A closes its session with P; the close is a `drop` line when the application sees it.
    fn close_session(&mut self) {
        let c = self.conn.take().expect("a session to close");
        let n = self.count("drop");
        self.spawn(async move {
            c.close(0).await;
            Out::Unit
        });
        self.settle();
        assert_eq!(self.count("drop"), n + 1, "the session closed");
    }

    fn stop(&mut self) {
        self.own(r#"{"op":"stop"}"#);
        let (_, id) = self.p.take().expect("P runs");
        assert!(self.x.drop_task(id));
        self.w.down(addr(PEER), true);
        self.settle();
    }

    /// `p` is the peer's new incarnation: the same address and seed, built by the caller (the type is opaque).
    fn restart(&mut self, p: Endpoint<H>) {
        self.own(r#"{"op":"restart"}"#);
        self.w.down(addr(PEER), false);
        assert_eq!(p.id(), self.pid, "the same identity");
        self.start_peer(p);
        self.settle();
    }

    fn cut(&mut self, on: bool) {
        self.own(if on { r#"{"op":"cut"}"# } else { r#"{"op":"heal"}"# });
        self.w.cut(addr(SUBJECT), addr(PEER), on);
        self.settle();
    }
}

#[test]
fn trace_dial_report() {
    let w = Wire::new(SplitMix64::traced(21));
    let protos: [&[u8]; 1] = [ALPN];
    let a = w.endpoint_timed(
        addr(SUBJECT),
        1,
        &protos,
        Limits::default(),
        AllowAll,
        Some(Duration::from_secs(2 * LIMIT)),
    );
    let p = w.endpoint_timed(addr(PEER), 2, &protos, Limits::default(), AllowAll, None);
    let mut r = world(w, a, p);
    // A dial to a running peer: the handshake ends at once and `connect` returns answered.
    r.dial();
    assert_eq!(r.count("answered"), 1);
    r.done();
    r.close_session();
    // An optimistic dial (A holds the peer's allow and a ticket) while A is cut off: its first flights are lost, and
    // the peer answers the first flight that gets through after the heal.
    r.cut(true);
    r.dial();
    assert_eq!(
        r.count("answered"),
        1,
        "the dial was handed over before its peer answered"
    );
    r.tick();
    r.tick();
    r.cut(false);
    r.until("answered", 20);
    r.done();
    r.close_session();
    // An optimistic dial to a peer that stopped: it ends early, well before the handshake's limit.
    r.stop();
    r.dial();
    r.until("closed", 30);
    r.done();
    // The peer comes back as a new incarnation, which does not know the ticket: it rejects it, and the dial that was
    // handed over is answered by the full handshake that follows.
    let p =
        r.w.endpoint_timed(addr(PEER), 2, &[ALPN], Limits::default(), AllowAll, None);
    r.restart(p);
    r.dial();
    r.settle();
    assert_eq!(r.count("answered"), 3, "the new incarnation answered the dial");
    r.done();
    r.close_session();
    // With the allow forgotten the dial is not handed over: to a peer that stopped it fails at the limit.
    r.a.admission_changed(&r.pid);
    r.settle();
    r.stop();
    r.dial();
    r.until("failed", 80);
    r.done();
    // A node whose round trip is long is thin: its dial to a peer that stopped, handed over on a cached allow, has no
    // early end and runs to the handshake's limit.
    let p =
        r.w.endpoint_timed(addr(PEER), 2, &[ALPN], Limits::default(), AllowAll, None);
    r.restart(p);
    r.slow_dial(THIN_RTT);
    assert_eq!(r.count("answered"), 4, "the slow dial was answered");
    r.done();
    r.close_session();
    r.stop();
    r.dial();
    let n = r.count("closed");
    r.until("closed", usize::try_from(2 * LIMIT + 10).unwrap());
    assert!(
        r.count("closed") == n + 1 && r.seen.out.borrow().contains("\"why\":\"limit\""),
        "the dial of a thin node ended at the limit"
    );
    r.done();
    let out = r.seen.out.borrow().clone();
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("dial_report.ndjson"), &out).unwrap();
    }
    let ops: BTreeSet<&str> = out.lines().map(|l| l.split('"').nth(3).unwrap()).collect();
    for op in [
        "tick", "stop", "restart", "cut", "heal", "cache", "dial", "answered", "closed", "failed", "done", "drop",
    ] {
        assert!(ops.contains(op), "no {op} line was written");
    }
    assert!(r.count("tick") > 61, "the limit was waited out");
    assert_eq!(r.count("dial"), 7);
    assert_eq!(r.count("drop"), 4);
}
