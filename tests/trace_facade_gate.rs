//! Trace generation for the facade's access gate (`crates/pinc/src/engine/gate.rs`, `engine.rs`, `engine/ops.rs`,
//! `endpoint.rs`), recorded as ndjson for the TLA+ trace checks `TraceFacadeRevoke.tla` (`facade_revoke.ndjson`, and
//! `facade_revoke_full.ndjson` for `TraceFacadeRevokeFull.tla`) and `TraceFacadeAcpForget.tla` (`facade_acp.ndjson`).
//!
//! One endpoint A, whose access hook answers from a table the test edits, runs in the shared world of
//! `facade_world.rs` against real endpoints p1 and p2 that admit everyone. Each step is a call of the real endpoint
//! (a dial, a revoke, a close, a move of the clock); after it the test reads A through the probes of the `trace`
//! feature (the live sessions, the endpoint's answer per peer, the allow the facade remembers) and writes one line.
//! Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    dead_code,
    unreachable_pub,
    missing_docs
)]

mod facade_world;

use std::cell::{Cell, RefCell};
use std::fmt::Write as _;
use std::future::Future;
use std::rc::Rc;

use facade_world::{Exec, PEER, SUBJECT, Wire, settle};
use pinc::{Admission, Connection, Direction, Endpoint, ErrorKind, GateProbe, Hosted, Limits};
use pinc_crypto::{IdentityAlg, NodeId};
use pinc_tests::SplitMix64;

const THIRD: &str = "10.0.0.3:1000";

/// The access hook: a table of the (peer, protocol, direction) it allows, or everything. `inside` runs once, inside the
/// next call of the hook, which the endpoint makes while it holds its core.
struct Hook {
    all: bool,
    table: RefCell<Vec<(NodeId, u8, Direction)>>,
    calls: Cell<usize>,
    inside: RefCell<Option<Box<dyn FnOnce()>>>,
}

impl Hook {
    fn new(all: bool) -> Rc<Self> {
        Rc::new(Self {
            all,
            table: RefCell::default(),
            calls: Cell::new(0),
            inside: RefCell::default(),
        })
    }
}

impl Admission for Hook {
    fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        self.calls.set(self.calls.get() + 1);
        let f = self.inside.borrow_mut().take();
        if let Some(f) = f {
            f();
        }
        self.all
            || self
                .table
                .borrow()
                .iter()
                .any(|&(p, a, d)| p == *peer && alpn == &[a][..] && d == dir)
    }
}

enum Out<H: Hosted> {
    Unit,
    Conn(pinc::Result<Connection<H>>),
    Rev(pinc::Result<()>),
}

/// A session of the model: its peer (an index), protocol and direction, and the handle the test closes it by.
struct Slot<H: Hosted> {
    peer: usize,
    proto: u8,
    out: bool,
    conn: Option<Connection<H>>,
}

fn dir_name(out: bool) -> &'static str {
    if out { "out" } else { "in" }
}

fn dir_of(name: &str) -> Direction {
    if name == "out" {
        Direction::Outbound
    } else {
        Direction::Inbound
    }
}

fn nm(i: usize) -> String {
    format!("p{}", i + 1)
}

fn count(out: &str, op: &str) -> usize {
    out.lines()
        .filter(|l| l.starts_with(&format!("{{\"op\":\"{op}\"")))
        .count()
}

struct G<H: Hosted + 'static> {
    w: Wire,
    x: Exec<Out<H>>,
    a: Endpoint<H>,
    p: Vec<Endpoint<H>>,
    ids: Vec<NodeId>,
    hook: Rc<Hook>,
    rows: Vec<(usize, u8, &'static str)>,
    slots: [Option<Slot<H>>; 4],
    out: Rc<RefCell<String>>,
    live: Rc<RefCell<Vec<usize>>>,
    next: u32,
    with_live: bool,
}

/// A world of A and `peers` peers; A's hook allows `rows` (peer index, protocol, direction).
fn world(seed: u64, peers: usize, rows: &[(usize, u8, &'static str)], with_live: bool) -> G<impl Hosted + 'static> {
    let w = Wire::new(SplitMix64::traced(seed));
    let hook = Hook::new(false);
    let protos: [&[u8]; 2] = [b"a", b"b"];
    let a = w.endpoint_with(
        SUBJECT.parse().unwrap(),
        1,
        &protos,
        Limits::default(),
        Rc::clone(&hook),
    );
    let addrs = [PEER, THIRD];
    let p: Vec<_> = (0..peers)
        .map(|i| {
            w.endpoint_with(
                addrs[i].parse().unwrap(),
                2 + i as u8,
                &protos,
                Limits::default(),
                Hook::new(true),
            )
        })
        .collect();
    let ids: Vec<NodeId> = p.iter().map(Endpoint::id).collect();
    let mut g = G {
        w,
        x: Exec::new(),
        a,
        p,
        ids,
        hook,
        rows: rows.to_vec(),
        slots: [None, None, None, None],
        out: Rc::default(),
        live: Rc::default(),
        next: 0,
        with_live,
    };
    g.rebuild_hook();
    let runs: Vec<_> = std::iter::once(g.a.clone()).chain(g.p.iter().cloned()).collect();
    for e in runs {
        g.spawn(async move {
            let _ = e.run().await;
            Out::Unit
        });
    }
    g.settle();
    g
}

impl<H: Hosted + 'static> G<H> {
    fn rebuild_hook(&self) {
        *self.hook.table.borrow_mut() = self.rows.iter().map(|&(i, p, d)| (self.ids[i], p, dir_of(d))).collect();
    }

    fn spawn(&mut self, fut: impl Future<Output = Out<H>> + 'static) -> u32 {
        self.next += 1;
        self.x.spawn(self.next, false, fut);
        self.next
    }

    fn settle(&mut self) {
        settle(&self.w, &mut self.x, &mut |_| {});
    }

    fn result(&mut self, id: u32) -> Out<H> {
        self.x.done.remove(&id).expect("the task finished")
    }

    fn pr(&self) -> GateProbe {
        self.a.trace_gate(&self.ids).expect("the core is free between calls")
    }

    fn live_of(&self, pr: &GateProbe) -> Vec<usize> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(i, s)| {
                let s = s.as_ref()?;
                pr.sessions
                    .iter()
                    .any(|(n, al, d)| *n == self.ids[s.peer] && al.as_slice() == [s.proto] && *d == s.out)
                    .then_some(i + 1)
            })
            .collect()
    }

    fn revoked(&self) -> Vec<String> {
        (0..self.ids.len())
            .filter(|&i| self.a.is_revoked(&self.ids[i]))
            .map(nm)
            .collect()
    }

    /// The fields every line carries: the live slots (when the model has them), the revoked peers and, when `full`, the
    /// endpoint's answer and the remembered allow per peer.
    fn state(&self, pr: &GateProbe, full: bool) -> String {
        let live = self.live_of(pr);
        self.live.borrow_mut().clone_from(&live);
        let mut s = String::new();
        if self.with_live {
            write!(s, ",\"live\":{live:?}").unwrap();
        }
        write!(s, ",\"revoked\":{:?}", self.revoked()).unwrap();
        if full {
            let cache: Vec<String> = (0..self.ids.len())
                .map(|i| {
                    let v = match pr.cache[i] {
                        None => "none",
                        Some(true) => "allow",
                        Some(false) => "deny",
                    };
                    format!("\"{}\":\"{v}\"", nm(i))
                })
                .collect();
            let known: Vec<String> = (0..self.ids.len())
                .map(|i| {
                    let q = pr.known[i].as_ref().map_or(String::new(), |(a, d)| {
                        format!(
                            "[\"{}\",\"{}\"]",
                            String::from_utf8_lossy(a),
                            dir_name(*d == Direction::Outbound)
                        )
                    });
                    format!("\"{}\":[{q}]", nm(i))
                })
                .collect();
            write!(
                s,
                ",\"cache\":{{{}}},\"known\":{{{}}}",
                cache.join(","),
                known.join(",")
            )
            .unwrap();
        }
        s
    }

    fn emit(&mut self, op: &str, extra: &str, pr: &GateProbe, full: bool) {
        let st = self.state(pr, full);
        writeln!(self.out.borrow_mut(), "{{\"op\":\"{op}\"{extra}{st}}}").unwrap();
    }

    fn init(&mut self) {
        let hook: Vec<String> = self
            .rows
            .iter()
            .map(|&(i, p, d)| format!("[\"{}\",\"{}\",\"{d}\"]", nm(i), p as char))
            .collect();
        writeln!(
            self.out.borrow_mut(),
            "{{\"op\":\"init\",\"hook\":[{}]}}",
            hook.join(",")
        )
        .unwrap();
    }

    fn put(&mut self, slot: usize, peer: usize, proto: u8, out: bool) {
        assert!(self.slots[slot - 1].is_none(), "slot {slot} is in use");
        self.slots[slot - 1] = Some(Slot {
            peer,
            proto,
            out,
            conn: None,
        });
    }

    fn keep(&mut self, slot: usize, c: Connection<H>) {
        if let Some(s) = self.slots[slot - 1].as_mut() {
            s.conn = Some(c);
        }
    }

    /// Peer `peer` dials A on `proto`; the task of the dial.
    fn peer_dials(&mut self, slot: usize, peer: usize, proto: u8) -> u32 {
        self.put(slot, peer, proto, false);
        let (pe, to) = (self.p[peer].clone(), self.a.addr());
        let id = self.spawn(async move { Out::Conn(pe.connect(to, &[proto]).await) });
        self.settle();
        id
    }

    /// A starts a dial of peer `peer` on `proto`, polled once so that nothing reached the wire.
    fn a_dials_start(&mut self, slot: usize, peer: usize, proto: u8) -> u32 {
        self.put(slot, peer, proto, true);
        let (a, to) = (self.a.clone(), self.p[peer].addr());
        let id = self.spawn(async move { Out::Conn(a.connect(to, &[proto]).await) });
        self.x.spin(&mut |_| {});
        id
    }

    /// Take the result of a dial task: keep the connection it gave; whether it gave one.
    fn took(&mut self, slot: usize, id: u32) -> bool {
        match self.result(id) {
            Out::Conn(Ok(c)) => {
                self.keep(slot, c);
                true
            }
            Out::Conn(Err(_)) => false,
            _ => panic!("not a dial"),
        }
    }

    /// The model's `arrive` and `decide` of a session peer `peer` opens on `proto`.
    fn arrive_in(&mut self, slot: usize, peer: usize, proto: u8) -> bool {
        self.arrive_line(slot, peer, proto, false);
        let id = self.peer_dials(slot, peer, proto);
        let _ = self.took(slot, id);
        self.decide(slot)
    }

    /// The model's `arrive` and `decide` of a session A dials to peer `peer` on `proto`.
    fn arrive_out(&mut self, slot: usize, peer: usize, proto: u8) -> bool {
        self.arrive_line(slot, peer, proto, true);
        let id = self.a_dials_start(slot, peer, proto);
        self.settle();
        let ok = self.took(slot, id);
        let live = self.decide(slot);
        assert_eq!(ok, live, "a dial that returned is a session that is live");
        live
    }

    fn arrive_line(&mut self, slot: usize, peer: usize, proto: u8, out: bool) {
        let pr = self.pr();
        let extra = format!(
            ",\"slot\":{slot},\"peer\":\"{}\",\"proto\":\"{}\",\"dir\":\"{}\"",
            nm(peer),
            proto as char,
            dir_name(out)
        );
        self.emit("arrive", &extra, &pr, true);
    }

    fn decide(&mut self, slot: usize) -> bool {
        let pr = self.pr();
        let live = self.live_of(&pr).contains(&slot);
        let extra = format!(",\"slot\":{slot},\"st\":\"{}\"", if live { "live" } else { "ended" });
        self.emit("decide", &extra, &pr, true);
        live
    }

    /// A session ends for another reason: closed by the handle the test holds for it.
    fn end_slot(&mut self, slot: usize) {
        let c = self.slots[slot - 1]
            .as_ref()
            .and_then(|s| s.conn.clone())
            .expect("the slot holds a connection");
        self.spawn(async move {
            c.close(0).await;
            Out::Unit
        });
        self.settle();
        let pr = self.pr();
        assert!(!self.live_of(&pr).contains(&slot), "the session is still live");
        self.emit("end", &format!(",\"slot\":{slot}"), &pr, true);
    }

    fn free(&mut self, slot: usize) {
        let pr = self.pr();
        assert!(!self.live_of(&pr).contains(&slot), "a live slot is not freed");
        self.slots[slot - 1] = None;
        self.settle();
        let pr = self.pr();
        self.emit("free", &format!(",\"slot\":{slot}"), &pr, true);
    }

    /// The `expire` and `lapse` lines of what `before` held and the gate no longer does; the last carries the probes.
    fn drops(&mut self, before: &GateProbe) {
        let after = self.pr();
        let mut ev = Vec::new();
        for i in 0..self.ids.len() {
            if before.cache[i].is_some() && after.cache[i].is_none() {
                ev.push(("expire", i));
            }
        }
        for i in 0..self.ids.len() {
            if before.known[i].is_some() && after.known[i].is_none() {
                ev.push(("lapse", i));
            }
        }
        let last = ev.len().saturating_sub(1);
        for (k, (op, i)) in ev.into_iter().enumerate() {
            self.emit(op, &format!(",\"peer\":\"{}\"", nm(i)), &after, k == last);
        }
    }

    /// A revokes peer `peer`; whether it did. `drops` follows when `split`.
    fn revoke_id(&mut self, id: NodeId, name: usize, split: bool) -> bool {
        let before = self.pr();
        let a = self.a.clone();
        let t = self.spawn(async move { Out::Rev(a.revoke(&id).await) });
        self.settle();
        let ok = match self.result(t) {
            Out::Rev(Ok(())) => true,
            Out::Rev(Err(e)) => {
                assert_eq!(e.kind(), ErrorKind::Busy);
                false
            }
            _ => panic!("not a revoke"),
        };
        let pr = self.pr();
        let extra = format!(",\"peer\":\"{}\",\"ok\":{ok}", nm(name));
        self.emit("revoke", &extra, &pr, !split);
        if split {
            self.drops(&before);
        }
        ok
    }

    fn revoke(&mut self, peer: usize, split: bool) -> bool {
        self.revoke_id(self.ids[peer], peer, split)
    }

    fn lift(&mut self, peer: usize, split: bool) {
        let before = self.pr();
        assert!(self.a.unrevoke(&self.ids[peer]), "the peer was revoked");
        self.settle();
        let pr = self.pr();
        self.emit("lift", &format!(",\"peer\":\"{}\"", nm(peer)), &pr, !split);
        if split {
            self.drops(&before);
        }
    }

    fn admit(&mut self, peer: usize, proto: u8, out: bool) -> bool {
        let ans = self.a.admit(
            &self.ids[peer],
            &[proto],
            if out { Direction::Outbound } else { Direction::Inbound },
        );
        let pr = self.pr();
        let extra = format!(
            ",\"peer\":\"{}\",\"proto\":\"{}\",\"dir\":\"{}\",\"ans\":{ans}",
            nm(peer),
            proto as char,
            dir_name(out)
        );
        self.emit("admit", &extra, &pr, true);
        ans
    }

    /// The next call of the hook takes the core's lock as seen from inside: it writes `toggle` and an `admit` of peer
    /// 0 on protocol `a` inbound, as a layer above would ask in the middle of an endpoint call.
    fn arm_inside(&mut self) {
        let (a, out, live, id) = (self.a.clone(), Rc::clone(&self.out), Rc::clone(&self.live), self.ids[0]);
        let n = self.ids.len();
        let ids = self.ids.clone();
        *self.hook.inside.borrow_mut() = Some(Box::new(move || {
            assert!(a.trace_busy(), "the hook runs while the core is held");
            let state = || {
                let rv: Vec<String> = (0..n).filter(|&i| a.is_revoked(&ids[i])).map(nm).collect();
                format!(",\"live\":{:?},\"revoked\":{rv:?}", live.borrow())
            };
            let st = state();
            writeln!(out.borrow_mut(), "{{\"op\":\"toggle\"{st}}}").unwrap();
            let ans = a.admit(&id, b"a", Direction::Inbound);
            let st = state();
            writeln!(
                out.borrow_mut(),
                "{{\"op\":\"admit\",\"peer\":\"p1\",\"proto\":\"a\",\"dir\":\"in\",\"ans\":{ans}{st}}}"
            )
            .unwrap();
        }));
    }

    /// The call that held the core returned: the model's second `toggle`, with the live set it had before.
    fn toggle_back(&mut self) {
        assert!(!self.a.trace_busy());
        assert!(self.hook.inside.borrow().is_none(), "the hook ran inside the call");
        let st = {
            let live = self.live.borrow().clone();
            format!(",\"live\":{live:?},\"revoked\":{:?}", self.revoked())
        };
        writeln!(self.out.borrow_mut(), "{{\"op\":\"toggle\"{st}}}").unwrap();
    }

    fn expire(&mut self, peer: usize) {
        let before = self.pr();
        assert!(before.cache[peer].is_some(), "an answer to expire");
        self.a.trace_expire(&self.ids[peer]);
        let pr = self.pr();
        assert!(pr.cache[peer].is_none());
        self.emit("expire", &format!(",\"peer\":\"{}\"", nm(peer)), &pr, true);
    }

    fn lapse(&mut self, peer: usize) {
        let before = self.pr();
        assert!(before.known[peer].is_some(), "a remembered allow to lapse");
        self.a.trace_lapse(&self.ids[peer]);
        let pr = self.pr();
        assert!(pr.known[peer].is_none());
        self.emit("lapse", &format!(",\"peer\":\"{}\"", nm(peer)), &pr, true);
    }

    /// Move the clock to `to` ns, one timer at a time, settling after each.
    fn move_clock(&mut self, to: u64) {
        for _ in 0..100_000 {
            let Some(ws) = self.w.advance_to(to) else {
                self.settle();
                return;
            };
            for k in ws {
                k.wake();
            }
            self.settle();
        }
        panic!("the clock did not reach {to}");
    }

    fn finish(&self, name: &str) -> String {
        let out = self.out.borrow().clone();
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join(name), &out).unwrap();
        }
        out
    }
}

const ROWS: [(usize, u8, &str); 4] = [(0, b'a', "in"), (0, b'a', "out"), (0, b'b', "in"), (1, b'a', "in")];

#[test]
fn trace_facade_revoke() {
    let mut g = world(11, 2, &ROWS, true);
    g.init();
    // p1 dials on `a`, which the hook allows: the endpoint asks, caches an allow and the facade remembers (a, in).
    assert!(g.arrive_in(1, 0, b'a'));
    // p2 dials on `b`, which the hook refuses for p2: the endpoint's answer allows p2 on `a`, and the session on `b` is
    // turned away where it comes up.
    assert!(!g.arrive_in(2, 1, b'b'));
    g.free(2);
    // A dials p1 on `a`: the cached allow lets it up, and the hook allows (a, out).
    assert!(g.arrive_out(2, 0, b'a'));
    assert!(g.admit(0, b'a', true));
    assert!(!g.admit(0, b'b', true));
    // The hook runs inside the endpoint call that decides p2's session: the layer above asks admit from inside it.
    g.arm_inside();
    g.arrive_line(3, 1, b'a', false);
    let id = g.peer_dials(3, 1, b'a');
    g.toggle_back();
    assert!(g.took(3, id));
    assert!(g.decide(3));
    g.end_slot(1);
    g.free(1);
    g.expire(1);
    g.lapse(0);
    // Revoke p1: its session ends within the call, and the endpoint drops both answers.
    assert!(g.revoke(0, true));
    g.free(2);
    // p1 dials while revoked: turned away, and the endpoint holds a deny for it.
    assert!(!g.arrive_in(1, 0, b'b'));
    g.free(1);
    g.lift(0, true);
    assert!(g.arrive_in(1, 0, b'a'));
    assert!(g.revoke(1, true));
    g.free(3);
    assert!(!g.admit(1, b'a', false));
    assert!(g.admit(0, b'a', false));
    let out = g.finish("facade_revoke.ndjson");
    for (op, n) in [
        ("init", 1),
        ("arrive", 6),
        ("decide", 6),
        ("revoke", 2),
        ("lift", 1),
        ("end", 1),
        ("free", 5),
        ("expire", 3),
        ("lapse", 1),
        ("toggle", 2),
        ("admit", 5),
    ] {
        assert!(count(&out, op) >= n, "{op}: {} of {n}", count(&out, op));
    }
}

#[test]
fn trace_facade_revoke_full() {
    let rows = [(0, b'a', "in"), (1, b'a', "in")];
    let mut g = world(12, 2, &rows, true);
    // Fill all but one place of the revoked table with ids that are not traced.
    for k in 0..(pinc::REVOKED_MAX - 1) {
        let mut bytes = [0xEE; 32];
        bytes[..8].copy_from_slice(&(k as u64 + 1).to_le_bytes());
        let other = NodeId {
            alg: IdentityAlg::Ed25519,
            bytes,
        };
        let a = g.a.clone();
        let t = g.spawn(async move { Out::Rev(a.revoke(&other).await) });
        g.settle();
        assert!(matches!(g.result(t), Out::Rev(Ok(()))), "revoke {k} of the filler ids");
    }
    g.init();
    assert!(g.arrive_in(1, 0, b'a'));
    assert!(g.arrive_in(2, 1, b'a'));
    // The last place goes to p1; p2 is refused and nothing changes.
    assert!(g.revoke(0, true));
    g.free(1);
    assert!(!g.revoke(1, true));
    assert!(g.admit(1, b'a', false));
    g.lift(0, true);
    assert!(g.revoke(1, true));
    g.free(2);
    assert!(!g.admit(1, b'a', false));
    let out = g.finish("facade_revoke_full.ndjson");
    for (op, n) in [
        ("init", 1),
        ("arrive", 2),
        ("decide", 2),
        ("revoke", 3),
        ("lift", 1),
        ("free", 2),
        ("expire", 2),
        ("lapse", 2),
        ("admit", 2),
    ] {
        assert!(count(&out, op) >= n, "{op}: {} of {n}", count(&out, op));
    }
    assert!(out.contains("\"ok\":false"), "a refused revoke was traced");
}

/// A decide line of the acp trace: the endpoint's answer lets the session through (`ep`) and the facade took it up (`up`).
fn acp_decide<H: Hosted + 'static>(g: &mut G<H>, slot: usize, peer: usize, proto: u8, out: bool, ok: bool) {
    let pr = g.pr();
    let up = g.live_of(&pr).contains(&slot);
    assert_eq!(
        up,
        ok,
        "session {} {} was decided as intended",
        proto as char,
        dir_name(out)
    );
    let ep = pr.cache[peer] == Some(true);
    let extra = format!(
        ",\"peer\":\"{}\",\"proto\":\"{}\",\"dir\":\"{}\",\"ep\":{ep},\"up\":{up}",
        nm(peer),
        proto as char,
        dir_name(out)
    );
    g.emit("decide", &extra, &pr, true);
}

fn acp_in<H: Hosted + 'static>(g: &mut G<H>, slot: usize, proto: u8, ok: bool) {
    let id = g.peer_dials(slot, 0, proto);
    let _ = g.took(slot, id);
    acp_decide(g, slot, 0, proto, false, ok);
}

/// The slot's session ends: the line `end`, then the slot is free.
fn acp_end<H: Hosted + 'static>(g: &mut G<H>, slot: usize, close: bool) {
    let (proto, out) = {
        let s = g.slots[slot - 1].as_ref().unwrap();
        (s.proto, s.out)
    };
    if close {
        let c = g.slots[slot - 1]
            .as_ref()
            .and_then(|s| s.conn.clone())
            .expect("a handle");
        g.spawn(async move {
            c.close(0).await;
            Out::Unit
        });
        g.settle();
    }
    let pr = g.pr();
    assert!(!g.live_of(&pr).contains(&slot), "the session ended");
    let extra = format!(
        ",\"peer\":\"p1\",\"proto\":\"{}\",\"dir\":\"{}\"",
        proto as char,
        dir_name(out)
    );
    g.emit("end", &extra, &pr, true);
    g.slots[slot - 1] = None;
}

fn acp_line<H: Hosted + 'static>(g: &mut G<H>, op: &str, extra: &str) {
    let pr = g.pr();
    g.emit(op, extra, &pr, true);
}

#[test]
fn trace_facade_acp() {
    let rows = [(0, b'a', "in"), (0, b'b', "out")];
    let mut g = world(13, 1, &rows, false);
    g.init();
    // p1 dials on `a`: the endpoint asks, caches an allow, the facade remembers (a, in) and takes the session up.
    acp_in(&mut g, 1, b'a', true);
    // A dials p1 on `b`: the cached allow lets the session up, and the hook allows (b, out).
    let id = g.a_dials_start(2, 0, b'b');
    acp_line(&mut g, "dial", ",\"peer\":\"p1\",\"proto\":\"b\"");
    g.settle();
    assert!(g.took(2, id));
    acp_decide(&mut g, 2, 0, b'b', true, true);
    // A hangs up that session.
    let c = g.slots[1].as_ref().and_then(|s| s.conn.clone()).unwrap();
    g.spawn(async move {
        c.close(0).await;
        Out::Unit
    });
    g.settle();
    acp_line(&mut g, "hangup", ",\"peer\":\"p1\"");
    acp_end(&mut g, 2, false);
    // The clock passes the recheck point of the answer (25 s of its 30): the session asks again.
    let calls = g.hook.calls.get();
    g.move_clock(26_000_000_000);
    assert!(g.hook.calls.get() > calls, "the session asked again");
    let pr = g.pr();
    assert!(g.live_of(&pr).contains(&1), "the session is still up");
    assert_eq!(pr.cache[0], Some(true));
    acp_line(
        &mut g,
        "recheck",
        ",\"peer\":\"p1\",\"proto\":\"a\",\"dir\":\"in\",\"allow\":true",
    );
    acp_end(&mut g, 1, true);
    // The host takes (a, in) out of its table and tells the endpoint: both answers go.
    g.rows.retain(|r| *r != (0, b'a', "in"));
    g.rebuild_hook();
    g.a.admission_changed(&g.ids[0]);
    g.settle();
    let pr = g.pr();
    assert!(pr.cache[0].is_none() && pr.known[0].is_none());
    acp_line(&mut g, "rehook", ",\"peer\":\"p1\",\"proto\":\"a\",\"dir\":\"in\"");
    // p1 dials on `a`, which the hook now refuses, while it allows (b, out): let through, turned away.
    acp_in(&mut g, 1, b'a', false);
    acp_end_closed(&mut g, 1);
    // Revoke: both answers go in the call, and a dial is refused before anything is sent.
    let a = g.a.clone();
    let id0 = g.ids[0];
    let t = g.spawn(async move { Out::Rev(a.revoke(&id0).await) });
    g.settle();
    assert!(matches!(g.result(t), Out::Rev(Ok(()))));
    let pr = g.pr();
    assert!(pr.cache[0].is_none() && pr.known[0].is_none());
    acp_line(&mut g, "revoke", ",\"peer\":\"p1\"");
    let a = g.a.clone();
    let to = g.p[0].addr();
    let t = g.spawn(async move { Out::Conn(a.connect(to, b"a").await) });
    g.settle();
    match g.result(t) {
        Out::Conn(Err(e)) => assert_eq!(e.kind(), ErrorKind::Refused),
        _ => panic!("a dial to a revoked peer is refused"),
    }
    acp_line(&mut g, "dial", ",\"peer\":\"p1\",\"proto\":\"a\"");
    // p1 dials while revoked: turned away, a deny cached.
    acp_in(&mut g, 1, b'b', false);
    acp_end_closed(&mut g, 1);
    assert_eq!(g.pr().cache[0], Some(false));
    // Lift: the deny goes.
    assert!(g.a.unrevoke(&g.ids[0]));
    g.settle();
    assert!(g.pr().cache[0].is_none());
    acp_line(&mut g, "lift", ",\"peer\":\"p1\"");
    g.rows.push((0, b'a', "in"));
    g.rebuild_hook();
    g.a.admission_changed(&g.ids[0]);
    g.settle();
    acp_line(&mut g, "rehook", ",\"peer\":\"p1\",\"proto\":\"a\",\"dir\":\"in\"");
    // Answers that run out: by the probes, then by the clock.
    acp_in(&mut g, 1, b'a', true);
    acp_end(&mut g, 1, true);
    g.a.trace_expire(&g.ids[0]);
    assert!(g.pr().cache[0].is_none());
    acp_line(&mut g, "expire", ",\"peer\":\"p1\"");
    g.a.trace_lapse(&g.ids[0]);
    assert!(g.pr().known[0].is_none());
    acp_line(&mut g, "lapse", ",\"peer\":\"p1\"");
    acp_in(&mut g, 1, b'a', true);
    acp_end(&mut g, 1, true);
    let pr = g.pr();
    assert!(pr.cache[0].is_some() && pr.known[0].is_some());
    g.move_clock(57_000_000_000);
    let pr = g.pr();
    assert!(pr.cache[0].is_none() && pr.known[0].is_none(), "both answers ran out");
    acp_line(&mut g, "expire", ",\"peer\":\"p1\"");
    // `Clear` (a full table of allows emptied by one more peer) is not reached by this run: it needs KNOWN_MAX live
    // allows, so no `clear` line is written.
    let out = g.finish("facade_acp.ndjson");
    for (op, n) in [
        ("init", 1),
        ("decide", 6),
        ("recheck", 1),
        ("dial", 2),
        ("hangup", 1),
        ("end", 4),
        ("revoke", 1),
        ("lift", 1),
        ("rehook", 2),
        ("expire", 2),
        ("lapse", 1),
    ] {
        assert!(count(&out, op) >= n, "{op}: {} of {n}", count(&out, op));
    }
}

/// A session the facade turned away has no live record; the test lets go of its handle without an `end` line (the
/// model keeps no question for a session that was not taken up).
fn acp_end_closed<H: Hosted + 'static>(g: &mut G<H>, slot: usize) {
    g.slots[slot - 1] = None;
    g.settle();
}
