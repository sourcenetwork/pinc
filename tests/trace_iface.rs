//! Trace generation for interfaces, link changes and suspension: scripted and seeded events of a real `pinc-core`
//! endpoint (built with the `trace` feature) with four peers and several interfaces, written as ndjson
//! (`iface.ndjson`) for the TLA+ trace check (`TraceIface.tla`).
//!
//! Node 0 holds established sessions (some with standby paths) and one still in its handshake. Each event (an
//! interface going down or coming back, an address change, a suspension, a resume, on live and dead interface ids) is
//! recorded with the view before and after it (the interfaces, the flags, every slot with its state, doubt, probe
//! timeout and paths, `quiet_until` in 16-bit limbs) and the calls the endpoint made on connections. A session closed
//! for a redial is dialed again by the test before the next step. Addresses are written as ids: local `L1` to `L6` as
//! 1 to 6, the remote addresses of node `n` as `10 * n` and `10 * n + 1, ...`.
//!
//! The test keeps its own copy of which sessions are asleep and whether they were in doubt at their first sleep, and
//! asserts the module documentation of `iface.rs` on every event, so it is meaningful without the proof tools. A
//! failed assertion is collected, the file is written, and the test fails at the end. A second test builds the case of
//! a session timing out at its sleep and then suspended a second time.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::large_stack_arrays,
    unreachable_pub,
    clippy::int_plus_one,
    clippy::panic
)]

use std::collections::HashMap;
use std::fmt::Write as _;
use std::net::SocketAddr;

use pinc_core::{
    Command, EndReason, Event, IfaceEvent, IfaceId, MAX_IFACES, RESUME_QUIET, Role, SessionId, TraceEvent, Value,
};
use pinc_tests::*;

/// How long keepalives stay quiet after a link return, an address change or a resume.
const S10: u64 = RESUME_QUIET;

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn list<T: std::fmt::Display>(v: impl IntoIterator<Item = T>) -> String {
    format!(
        "[{}]",
        v.into_iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
    )
}

/// The local address `Lk` of node 0.
fn l(k: u8) -> SocketAddr {
    if k == 1 {
        ([10, 0, 0, 1], 4433).into()
    } else {
        ([10, 0, k, 1], 4433).into()
    }
}

fn drain(net: &mut CoreNet) -> Vec<TraceEvent> {
    let mut v = Vec::new();
    while let Some(r) = net.nodes[0].ep.poll_trace() {
        v.push(r.event);
    }
    v
}

/// Whether the session in `slot` of node 0 shows a probe timeout.
fn pto(net: &CoreNet, slot: usize) -> bool {
    net.nodes[0].ep.trace_iface_slot(slot).is_some_and(|v| v.3)
}

/// Drop every datagram to or from the addresses in `blocked`.
fn block(net: &mut CoreNet, blocked: &[SocketAddr]) {
    let v = blocked.to_vec();
    net.loss = Some(Box::new(move |from, to, _| v.contains(&from) || v.contains(&to)));
}

/// Open a unidirectional stream of `s` on node 0 and write `n` bytes.
fn write(net: &mut CoreNet, s: SessionId, n: usize) {
    let now = net.now;
    let Value::Stream(id) = net.nodes[0]
        .cmd(
            now,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!("no stream")
    };
    net.nodes[0]
        .cmd(
            now,
            Command::Write {
                session: s,
                stream: id,
                data: &vec![0x5a; n],
            },
        )
        .unwrap();
}

/// What the test sees of the endpoint after a call.
#[derive(PartialEq, Clone)]
struct Ses {
    st: u8,
    act: u64,
    pto: bool,
    doubt: bool,
    genj: u32,
    paths: Vec<(u64, u64)>,
}

#[derive(PartialEq, Clone)]
struct View {
    ifs: [u64; MAX_IFACES],
    dark: bool,
    susp: bool,
    moved: bool,
    ses: Vec<Ses>,
}

impl View {
    fn json(&self) -> String {
        let ses = self.ses.iter().map(|s| {
            let st = ["free", "hs", "est", "other"][usize::from(s.st)];
            let paths = s.paths.iter().map(|(l, r)| format!(r#"{{"l":{l},"r":{r}}}"#));
            format!(
                r#"{{"st":"{st}","act":{},"pto":{},"doubt":{},"gen":{},"paths":{}}}"#,
                s.act,
                s.pto,
                s.doubt,
                s.genj,
                list(paths)
            )
        });
        format!(
            r#"{{"ifs":{},"dark":{},"susp":{},"moved":{},"ses":{}}}"#,
            list(self.ifs),
            self.dark,
            self.susp,
            self.moved,
            list(ses)
        )
    }

    /// Session `i` is established (or, with `hs`, in its handshake) and its active path leaves from `local`.
    fn leaves(&self, i: usize, local: u64, hs: bool) -> bool {
        let s = &self.ses[i];
        (s.st == 2 || (hs && s.st == 1)) && local != 0 && s.act == local
    }
}

#[derive(Clone, Copy)]
enum Ev {
    Down,
    Up,
    Addr(u64),
    Suspend,
    Resume(bool),
}

#[derive(Default)]
struct Summary {
    events: u32,
    redials: u32,
    wakes: u32,
    rebinds: u32,
    replaces: u32,
    dead: u32,
    redialed_sessions: u32,
}

struct Run {
    net: CoreNet,
    local: HashMap<SocketAddr, u64>,
    remote: HashMap<SocketAddr, u64>,
    out: String,
    fails: Vec<String>,
    asleep: [bool; CK],
    doubt: [bool; CK],
    gens: [u32; CK],
    /// The session of node 0 to each peer node, and the peer of each session.
    cur: HashMap<usize, SessionId>,
    peer: HashMap<SessionId, usize>,
    pending: Vec<SessionId>,
    seen: usize,
    st: Summary,
    /// Notes for the summary line.
    notes: Vec<&'static str>,
}

impl Run {
    fn lid(&self, a: SocketAddr) -> u64 {
        *self
            .local
            .get(&a)
            .unwrap_or_else(|| panic!("a local address the test does not know: {a}"))
    }

    fn rid(&self, a: SocketAddr) -> u64 {
        *self
            .remote
            .get(&a)
            .unwrap_or_else(|| panic!("a remote address the test does not know: {a}"))
    }

    fn view(&self) -> (View, u64) {
        let ep = &self.net.nodes[0].ep;
        let (dark, susp, moved, quiet) = ep.trace_iface_flags();
        let ses = (0..CK)
            .map(|i| {
                let (st, genj, doubt, pto, act) = ep.trace_iface_slot(i).unwrap();
                Ses {
                    st,
                    act: act.map_or(0, |(a, _)| self.lid(a)),
                    pto,
                    doubt,
                    genj,
                    paths: ep
                        .trace_slot_paths(i)
                        .map(|(a, r)| (self.lid(a), self.rid(r)))
                        .collect(),
                }
            })
            .collect();
        let view = View {
            ifs: std::array::from_fn(|j| ep.trace_iface(j).map_or(0, |a| self.lid(a))),
            dark,
            susp,
            moved,
            ses,
        };
        (view, quiet)
    }

    fn check(&mut self, ok: bool, msg: impl FnOnce() -> String) {
        if !ok {
            self.fails.push(msg());
        }
    }

    /// One event of node 0 at the current time: `id` is the interface id plus one, 0 for a command.
    fn ev(&mut self, id: usize, ev: Ev) {
        let now = self.net.now;
        drain(&mut self.net);
        let (vb, qb) = self.view();
        for i in 0..CK {
            if vb.ses[i].genj != self.gens[i] {
                self.gens[i] = vb.ses[i].genj;
                self.asleep[i] = false;
                self.doubt[i] = false;
            }
        }
        let dropped = self.net.nodes[0].ep.trace_dropped();
        match (id, ev) {
            (0, Ev::Suspend) => {
                self.net.nodes[0].cmd(now, Command::Suspend).unwrap();
            }
            (0, Ev::Resume(moved)) => {
                self.net.nodes[0].cmd(now, Command::Resume { moved }).unwrap();
            }
            (0, _) => panic!("only a suspension and a resume are commands"),
            (id, ev) => {
                let e = match ev {
                    Ev::Down => IfaceEvent::Down,
                    Ev::Up => IfaceEvent::Up,
                    Ev::Addr(a) => IfaceEvent::AddrChange(l(a as u8)),
                    Ev::Suspend => IfaceEvent::Suspend,
                    Ev::Resume(moved) => IfaceEvent::Resume { moved },
                };
                self.net.nodes[0].ep.iface_event(now, IfaceId(id - 1), e);
            }
        }
        let calls: Vec<(usize, u64)> = drain(&mut self.net)
            .into_iter()
            .filter_map(|e| match e {
                TraceEvent::Iface { slot, call } => Some((slot as usize, call)),
                _ => None,
            })
            .collect();
        let (va, qa) = self.view();
        assert_eq!(
            self.net.nodes[0].ep.trace_dropped(),
            dropped,
            "the trace ring dropped records during an event"
        );
        let (k, a, m) = match ev {
            Ev::Down => ("down", 0, false),
            Ev::Up => ("up", 0, false),
            Ev::Addr(a) => ("addr", a, false),
            Ev::Suspend => ("suspend", 0, false),
            Ev::Resume(m) => ("resume", 0, m),
        };
        let kinds = ["", "down", "up", "sleep", "wake", "redial", "rebind", "replace"];
        let calls_json = list(
            calls
                .iter()
                .map(|(slot, kind)| format!(r#"{{"slot":{slot},"kind":"{}"}}"#, kinds[*kind as usize])),
        );
        let _ = writeln!(
            self.out,
            r#"{{"t":"iface","id":{id},"ev":{{"k":"{k}","a":{a},"m":{m}}},"now":{},"qb":{},"qa":{},"b":{},"a":{},"calls":{calls_json}}}"#,
            limbs(now),
            limbs(qb),
            limbs(qa),
            vb.json(),
            va.json(),
        );
        self.st.events += 1;
        for (_, kind) in &calls {
            match kind {
                4 => self.st.wakes += 1,
                5 => self.st.redials += 1,
                6 => self.st.rebinds += 1,
                7 => self.st.replaces += 1,
                _ => {}
            }
        }
        self.assert_event(id, ev, now, (&vb, qb), (&va, qa), &calls);
    }

    /// The module documentation of `iface.rs`, asserted on one event.
    fn assert_event(
        &mut self,
        id: usize,
        ev: Ev,
        now: u64,
        (vb, qb): (&View, u64),
        (va, qa): (&View, u64),
        calls: &[(usize, u64)],
    ) {
        let tag = |s: &str| format!("{s} (interface id {id})");
        let quiet = now.saturating_add(S10);
        if id > 0 && (id - 1 >= MAX_IFACES || vb.ifs[id - 1] == 0) {
            self.st.dead += 1;
            self.check(vb == va && calls.is_empty() && qb == qa, || {
                tag("an event on an id that names no address changed something")
            });
            return;
        }
        let established: Vec<usize> = (0..CK).filter(|&i| vb.ses[i].st == 2).collect();
        match ev {
            Ev::Down | Ev::Up => {
                let local = vb.ifs[id - 1];
                let kind = if matches!(ev, Ev::Down) { 1 } else { 2 };
                let want: Vec<(usize, u64)> = (0..CK)
                    .filter(|&i| vb.leaves(i, local, true))
                    .map(|i| (i, kind))
                    .collect();
                self.check(calls == want, || tag(&format!("the calls {calls:?} are not {want:?}")));
                if kind == 1 {
                    self.check(va.dark && qa == qb, || {
                        tag("a link down left the node not dark or moved quiet")
                    });
                } else {
                    self.check(qa == quiet, || tag("a link back did not set quiet to now plus 10 s"));
                }
            }
            Ev::Addr(new) => {
                let old = vb.ifs[id - 1];
                self.check(va.ifs[id - 1] == new, || {
                    tag("the interface does not name the new address")
                });
                self.check(qa == quiet, || {
                    tag("an address change did not set quiet to now plus 10 s")
                });
                if vb.susp {
                    self.check(va.moved, || tag("an address change while suspended did not set moved"));
                }
                for i in 0..CK {
                    let npaths = vb.ses[i].paths.iter().filter(|(pl, _)| *pl == old).count();
                    let wake = vb.leaves(i, old, false);
                    let mine: Vec<u64> = calls.iter().filter(|c| c.0 == i).map(|c| c.1).collect();
                    let moves = |ks: &[u64]| ks.iter().all(|k| matches!(k, 6 | 7));
                    let ok = if wake {
                        mine.len() == npaths + 2 && mine[npaths..] == [1, 2] && moves(&mine[..npaths])
                    } else {
                        mine.len() == npaths && moves(&mine)
                    };
                    self.check(ok, || {
                        tag(&format!(
                            "slot {i}: the calls {mine:?} do not move {npaths} paths (wake {wake})"
                        ))
                    });
                    for (pl, r) in &vb.ses[i].paths {
                        if *pl == old {
                            let held = va.ses[i].paths.contains(&(new, *r));
                            self.check(held, || {
                                tag(&format!("slot {i} holds no path from the new address to {r}"))
                            });
                        }
                    }
                }
            }
            Ev::Suspend => {
                let want: Vec<(usize, u64)> = established.iter().map(|&i| (i, 3)).collect();
                self.check(calls == want, || tag(&format!("the calls {calls:?} are not {want:?}")));
                self.check(va.susp, || tag("the node is not suspended after a suspension"));
                for &i in &established {
                    if !self.asleep[i] {
                        self.asleep[i] = true;
                        self.doubt[i] = vb.ses[i].pto || vb.dark;
                    }
                }
            }
            Ev::Resume(moved) => {
                let want: Vec<(usize, u64)> = established
                    .iter()
                    .map(|&i| (i, if moved || vb.moved || self.doubt[i] { 5 } else { 4 }))
                    .collect();
                self.check(calls == want, || tag(&format!("the calls {calls:?} are not {want:?}")));
                self.check(!va.dark && !va.susp && !va.moved, || {
                    tag("a flag stays set after a resume")
                });
                self.check(qa == quiet, || tag("a resume did not set quiet to now plus 10 s"));
                for &i in &established {
                    self.asleep[i] = false;
                    self.doubt[i] = false;
                }
            }
        }
    }

    fn run_for(&mut self, ms: u64) {
        self.net.run_for(ms * MS_NS);
    }

    fn block(&mut self, node2: bool) {
        let mut v = vec![self.net.nodes[4].addr];
        if node2 {
            v.push(self.net.nodes[2].addr);
        }
        block(&mut self.net, &v);
    }

    /// Dial again every session closed for a redial, once the node can.
    fn redial_closed(&mut self) {
        let now = self.net.now;
        self.net.nodes[0].service(now);
        for (_, e) in &self.net.nodes[0].events[self.seen..] {
            if let Event::Closed {
                session,
                reason: EndReason::Redial,
            } = e
            {
                self.pending.push(*session);
            }
        }
        self.seen = self.net.nodes[0].events.len();
        let (dark, susp, _, _) = self.net.nodes[0].ep.trace_iface_flags();
        if dark || susp {
            return;
        }
        for s in std::mem::take(&mut self.pending) {
            let Some(&k) = self.peer.get(&s) else { continue };
            let (n, _) = self.net.connect_pair(0, k, ALPN_A, Role::Other);
            self.cur.insert(k, n);
            self.peer.insert(n, k);
            self.st.redialed_sessions += 1;
        }
    }

    /// Node 0 loses node 2 and writes to it until its session shows a probe timeout; the session's slot.
    fn timing_out(&mut self) -> usize {
        self.block(true);
        let s2 = self.cur[&2];
        write(&mut self.net, s2, 3000);
        let slot = s2.slot();
        let end = self.net.now + 5 * SEC_NS;
        assert!(
            self.net.run(end, |n| pto(n, slot)),
            "the session to node 2 never showed a probe timeout"
        );
        slot
    }
}

#[test]
fn trace_iface() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        for tag in 1..=5 {
            net.add(tag);
        }
        for k in 2..=6 {
            net.nodes[0].extra.push(l(k));
        }
        let (a22, a33): (SocketAddr, SocketAddr) = (([10, 0, 0, 22], 4433).into(), ([10, 0, 0, 33], 4433).into());
        net.nodes[1].extra.push(a22);
        net.nodes[3].extra.push(a33);
        let local: HashMap<SocketAddr, u64> = (1..=6u8).map(|k| (l(k), u64::from(k))).collect();
        let mut remote = HashMap::new();
        for (n, node) in net.nodes.iter().enumerate().take(5).skip(1) {
            remote.insert(node.addr, 10 * n as u64);
            for (j, a) in node.extra.iter().enumerate() {
                remote.insert(*a, 10 * n as u64 + 1 + j as u64);
            }
        }
        let (s1, _) = net.connect_pair(0, 1, ALPN_A, Role::Other);
        let (s2, _) = net.connect_pair(0, 2, ALPN_A, Role::Other);
        assert_eq!(net.nodes[0].ep.add_iface(l(2)), Some(IfaceId(1)));
        net.nodes[0].ep.remove_iface(IfaceId(0));
        let (s3, _) = net.connect_pair(0, 3, ALPN_A, Role::Other);
        assert_eq!(net.nodes[0].ep.add_iface(l(1)), Some(IfaceId(0)));
        let now = net.now;
        net.nodes[0]
            .cmd(now, Command::Punch { session: s1, addr: a22 })
            .unwrap();
        net.nodes[0]
            .cmd(now, Command::Punch { session: s3, addr: a33 })
            .unwrap();
        let (node4, a4) = (net.nodes[4].node, net.nodes[4].addr);
        block(&mut net, &[a4]);
        let rep = net.nodes[0].connect(now, node4, ALPN_A, a4, Role::Other).unwrap();
        let s4 = net.nodes[0].session(&rep);
        net.run_for(2 * SEC_NS);

        let mut r = Run {
            net,
            local,
            remote,
            out: String::new(),
            fails: Vec::new(),
            asleep: [false; CK],
            doubt: [false; CK],
            gens: [0; CK],
            cur: HashMap::from([(1, s1), (2, s2), (3, s3), (4, s4)]),
            peer: HashMap::from([(s1, 1), (s2, 2), (s3, 3), (s4, 4)]),
            pending: Vec::new(),
            seen: 0,
            st: Summary::default(),
            notes: Vec::new(),
        };
        r.seen = r.net.nodes[0].events.len();

        // 1: links down and back on the interfaces the sessions use, the handshaking one included
        r.ev(1, Ev::Down);
        r.run_for(200);
        r.ev(1, Ev::Up);
        r.ev(2, Ev::Down);
        r.ev(2, Ev::Up);
        // 2: events on dead ids
        r.ev(6, Ev::Up);
        r.ev(9, Ev::Down);
        r.ev(8, Ev::Addr(6));
        // 3: an address change of interface 0
        r.ev(1, Ev::Addr(5));
        r.run_for(1000);
        // 4: a suspension and a resume
        r.ev(0, Ev::Suspend);
        r.run_for(500);
        r.ev(0, Ev::Resume(false));
        r.redial_closed();
        // 5: a session in doubt by a timeout is redialed on resume, the others woken
        r.timing_out();
        r.ev(0, Ev::Suspend);
        r.block(false);
        r.run_for(500);
        r.ev(0, Ev::Resume(false));
        r.redial_closed();
        // 6: dark, then the link comes back while suspended
        r.ev(1, Ev::Down);
        r.ev(0, Ev::Suspend);
        r.ev(1, Ev::Up);
        r.ev(0, Ev::Resume(false));
        r.redial_closed();
        // 7: the node moves while suspended
        r.ev(0, Ev::Suspend);
        r.ev(2, Ev::Addr(4));
        r.ev(0, Ev::Resume(false));
        r.redial_closed();
        // 8: the host says the node moved
        r.ev(0, Ev::Suspend);
        r.ev(0, Ev::Resume(true));
        r.redial_closed();
        // 9: suspended twice, one of them through an interface
        r.ev(0, Ev::Suspend);
        r.run_for(100);
        r.ev(1, Ev::Suspend);
        r.ev(2, Ev::Resume(false));
        r.redial_closed();
        // 10: the pattern of the second test: timing out at the sleep, the timeout gone, a second suspension
        let slot = r.timing_out();
        r.block(false);
        let a2 = r.net.nodes[2].addr;
        let mark = r.net.nodes[0].sent.len();
        let end = r.net.now + 5 * SEC_NS;
        r.net.run(end, |n| n.nodes[0].sent[mark..].iter().any(|s| s.1 == a2));
        r.ev(0, Ev::Suspend);
        let end = r.net.now + 5 * SEC_NS;
        if r.net.run(end, |n| !pto(n, slot)) {
            r.ev(0, Ev::Suspend);
        } else {
            r.notes
                .push("step 10: the probe timeout never cleared while asleep, the second suspension was skipped");
        }
        r.ev(0, Ev::Resume(false));
        r.redial_closed();
        // 11: seeded events
        let mut rng = SplitMix64::traced(0x6966_6163_6500_0001);
        for _ in 0..150 {
            let pick = rng.next_u64() % 11;
            let id = if pick < 2 { 0 } else { pick as usize - 1 };
            let kind = if id == 0 {
                8 + (rng.next_u64() % 2) as usize
            } else {
                match rng.next_u64() % 10 {
                    0..3 => 0,
                    3..6 => 1,
                    6..8 => 2,
                    8 => 3,
                    _ => 4,
                }
            };
            let moved = rng.next_u64().is_multiple_of(4);
            let ev = match kind {
                0 => Ev::Down,
                1 => Ev::Up,
                2 => {
                    let taken: Vec<u64> = (0..MAX_IFACES)
                        .filter(|&j| id == 0 || j != id - 1)
                        .filter_map(|j| r.net.nodes[0].ep.trace_iface(j))
                        .map(|a| r.lid(a))
                        .collect();
                    let free: Vec<u64> = (1..=6).filter(|k| !taken.contains(k)).collect();
                    Ev::Addr(free[(rng.next_u64() % free.len() as u64) as usize])
                }
                3 | 8 => Ev::Suspend,
                _ => Ev::Resume(moved),
            };
            r.ev(id, ev);
            let span = [0, 10, 200, 1000][(rng.next_u64() % 4) as usize];
            r.run_for(span);
            if matches!(ev, Ev::Resume(_)) {
                r.redial_closed();
            }
        }
        let st = &r.st;
        eprintln!(
            "trace_iface: events {} redials {} wakes {} rebinds {} replaces {} dead ids {} sessions dialed again {} {:?}",
            st.events, st.redials, st.wakes, st.rebinds, st.replaces, st.dead, st.redialed_sessions, r.notes
        );
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("iface.ndjson"), &r.out).unwrap();
        }
        assert!(
            r.fails.is_empty(),
            "{} assertion(s) of the module documentation failed, the first ones:\n{}",
            r.fails.len(),
            r.fails.iter().take(10).cloned().collect::<Vec<_>>().join("\n")
        );
    });
}

/// A session already timing out when its sleep went out is redialed on resume even when the probe it had in flight is
/// acknowledged while it sleeps and the suspension is reported again: a second suspension sends no SLEEP, so it keeps
/// what the first one saw.
#[test]
fn a_session_timing_out_at_its_sleep_redials_after_a_second_suspend() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        for tag in 1..=3 {
            net.add(tag);
        }
        let (_s1, _) = net.connect_pair(0, 1, ALPN_A, Role::Other);
        let (s2, _) = net.connect_pair(0, 2, ALPN_A, Role::Other);
        net.run_for(2 * SEC_NS);
        let a2 = net.nodes[2].addr;
        block(&mut net, &[a2]);
        write(&mut net, s2, 3000);
        let slot = s2.slot();
        let end = net.now + 5 * SEC_NS;
        assert!(
            net.run(end, |n| pto(n, slot)),
            "the session to node 2 never showed a probe timeout"
        );
        net.loss = None;
        let mark = net.nodes[0].sent.len();
        let end = net.now + 5 * SEC_NS;
        assert!(
            net.run(end, |n| n.nodes[0].sent[mark..].iter().any(|s| s.1 == a2)),
            "no probe left for node 2 once it was reachable"
        );
        assert!(pto(&net, slot), "the probe timeout cleared before the suspension");
        let now = net.now;
        net.nodes[0].cmd(now, Command::Suspend).unwrap();
        assert!(
            net.nodes[0].ep.trace_iface_slot(slot).unwrap().2,
            "the session timing out at its sleep is not in doubt"
        );
        let end = net.now + 5 * SEC_NS;
        assert!(
            net.run(end, |n| !pto(n, slot)),
            "the probe timeout never cleared while the session slept, so the case cannot be built"
        );
        let now = net.now;
        net.nodes[0].cmd(now, Command::Suspend).unwrap();
        assert!(
            net.nodes[0].ep.trace_iface_slot(slot).unwrap().2,
            "a second suspension dropped the doubt of the first"
        );
        net.nodes[0].cmd(now, Command::Resume { moved: false }).unwrap();
        let closed = |net: &CoreNet| {
            net.nodes[0].saw(|e| matches!(e, Event::Closed { session, reason: EndReason::Redial } if *session == s2))
        };
        assert!(
            closed(&net) || {
                net.nodes[0].service(now);
                closed(&net)
            },
            "the session that timed out at its first sleep was woken, not redialed"
        );
    });
}
