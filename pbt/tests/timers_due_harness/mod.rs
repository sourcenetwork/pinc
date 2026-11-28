//! The driver of `timers_due.rs`: two real endpoints (`core_harness`) that connect and then live through a generated
//! script of what an application and a network do to them (streams that fill a window, a reader that stops, datagrams,
//! pings, a link that drops everything, loss, an interface that goes down, suspend and resume, a probe of a path nobody
//! answers, a close, a shutdown, a second dial), with the timer rule checked after every step.
//!
//! The rule: `Endpoint::poll_timeout` is "the next time `handle_timeout` must run" (the transport's
//! `Connection::poll_timeout`, crates/pinc-transport/src/conn/timer.rs:29, and pinc-core's endpoint), and "a timer is
//! reported only while it can still act (a stale deadline would make a driver spin)" (timer.rs:3). So once a host has
//! had `handle_timeout(t)` at `t = poll_timeout()`, then `service` and `poll_transmit` until `None` (the documented
//! driver loop) with nothing else in between, `poll_timeout()` is `None` or later than `t`.
#![allow(dead_code, clippy::unwrap_used, clippy::panic, clippy::indexing_slicing)]

use std::net::SocketAddr;

use super::core_harness::{self, ALPN_A, HostCfg, MS, Net, SEC, Violation};
use ephyra::gens;
use pinc_core::{Command, Event, IfaceEvent, IfaceId, Role, SessionId, Value};

/// What the application or the network does next. `from` and `host` are 0 for the dialer, 1 for the server.
#[derive(Clone, Debug, PartialEq, Eq, ephyra::Arbitrary)]
pub enum Op {
    /// Nothing for this many ms.
    Wait(
        #[ephyra(gen = gens::frequency(vec![(3, gens::int(1u64..=600).boxed()), (1, gens::int(1u64..=40_000).boxed())]))]
         u64,
    ),
    /// A new bidirectional stream with `len` bytes, finished when `fin`.
    Write {
        #[ephyra(gen = gens::int(0u8..=1))]
        from: u8,
        #[ephyra(gen = gens::frequency(vec![(3, gens::int(0usize..=4_000).boxed()), (1, gens::int(0usize..=600_000).boxed())]))]
        len: usize,
        fin: bool,
    },
    Datagram {
        #[ephyra(gen = gens::int(0u8..=1))]
        from: u8,
        #[ephyra(gen = gens::int(1usize..=1_500))]
        len: usize,
    },
    Ping(#[ephyra(gen = gens::int(0u8..=1))] u8),
    /// The host reads (or stops reading) its streams, so the peer's credit runs out.
    Read {
        #[ephyra(gen = gens::int(0u8..=1))]
        host: u8,
        on: bool,
    },
    /// The link drops everything for this many ms.
    Cut(
        #[ephyra(gen = gens::frequency(vec![(3, gens::int(1u64..=3_000).boxed()), (1, gens::int(1u64..=90_000).boxed())]))]
         u64,
    ),
    /// The link loses this many per mille from now on.
    Loss(
        #[ephyra(gen = gens::frequency(vec![(2, gens::constant(0u16).boxed()), (1, gens::int(1u16..=1000).boxed())]))]
        u16,
    ),
    /// 0 down, 1 up, 2 suspend, 3 resume, 4 resume on a new address.
    Iface {
        #[ephyra(gen = gens::int(0u8..=1))]
        host: u8,
        #[ephyra(gen = gens::int(0u8..=4))]
        ev: u8,
    },
    /// `Command::Suspend`.
    Sleep(#[ephyra(gen = gens::int(0u8..=1))] u8),
    /// `Command::Resume`.
    Wake {
        #[ephyra(gen = gens::int(0u8..=1))]
        host: u8,
        moved: bool,
    },
    Close(#[ephyra(gen = gens::int(0u8..=1))] u8),
    Shutdown(#[ephyra(gen = gens::int(0u8..=1))] u8),
    /// The dialer dials the server again.
    Redial,
    /// A punch toward an address nobody answers on, so a path is probed until it gives up.
    Punch {
        #[ephyra(gen = gens::int(0u8..=1))]
        from: u8,
        #[ephyra(gen = gens::int(1u16..=4))]
        port: u16,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, ephyra::Arbitrary)]
pub struct Case {
    pub seed: u64,
    pub split: bool,
    pub room: bool,
    #[ephyra(gen = gens::frequency(vec![(3, gens::int(1u64..=40).boxed()), (1, gens::int(1u64..=400).boxed())]))]
    pub delay_ms: u64,
    #[ephyra(gen = gens::frequency(vec![(2, gens::constant(0u64).boxed()), (1, gens::int(1u64..=30).boxed())]))]
    pub jitter_ms: u64,
    #[ephyra(gen = gens::vec(ephyra::any::<Op>()).len(0..=14))]
    pub ops: Vec<Op>,
}

pub fn in_support(c: &Case) -> bool {
    (1..=400).contains(&c.delay_ms) && c.jitter_ms <= 30 && c.ops.len() <= 14
}

/// What a signature names: the kind of the last step before the timer stayed due.
fn kind(op: Option<&Op>) -> &'static str {
    match op {
        None => "a timer stays due after handle_timeout ran at its time (connecting)",
        Some(Op::Wait(_)) => "a timer stays due after handle_timeout ran at its time (after a wait)",
        Some(Op::Write { .. }) => "a timer stays due after handle_timeout ran at its time (after a write)",
        Some(Op::Datagram { .. }) => "a timer stays due after handle_timeout ran at its time (after a datagram)",
        Some(Op::Ping(_)) => "a timer stays due after handle_timeout ran at its time (after a ping)",
        Some(Op::Read { .. }) => "a timer stays due after handle_timeout ran at its time (after a reader change)",
        Some(Op::Cut(_)) => "a timer stays due after handle_timeout ran at its time (while the link drops everything)",
        Some(Op::Loss(_)) => "a timer stays due after handle_timeout ran at its time (on a lossy link)",
        Some(Op::Iface { .. }) => "a timer stays due after handle_timeout ran at its time (after an interface event)",
        Some(Op::Sleep(_)) => "a timer stays due after handle_timeout ran at its time (asleep)",
        Some(Op::Wake { .. }) => "a timer stays due after handle_timeout ran at its time (after a resume)",
        Some(Op::Close(_)) => "a timer stays due after handle_timeout ran at its time (closing)",
        Some(Op::Shutdown(_)) => "a timer stays due after handle_timeout ran at its time (shutting down)",
        Some(Op::Redial) => "a timer stays due after handle_timeout ran at its time (after a second dial)",
        Some(Op::Punch { .. }) => "a timer stays due after handle_timeout ran at its time (probing a dead path)",
    }
}

/// The pair, its sessions and what ran so far.
pub struct World {
    pub net: Net,
    pub a: usize,
    pub b: usize,
    pub sa: SessionId,
    pub sb: Option<SessionId>,
    pub done: Vec<Op>,
    pub known: bool,
    /// The known cause was met (with `known`): the rest of the case is skipped.
    pub ended: bool,
}

fn fail(v: Option<Violation>) {
    if let Some(v) = v {
        ephyra::signature(v.sig);
        panic!("{}: {}", v.sig, v.detail);
    }
}

/// Whether host `i` last heard that a peer sleeps (a `PeerAsleep` with no `PeerAwake` after it).
fn peer_asleep(n: &Net, i: usize) -> bool {
    n.hosts[i]
        .events
        .iter()
        .rev()
        .find_map(|(_, e)| match e {
            Event::PeerAsleep { .. } => Some(true),
            Event::PeerAwake { .. } => Some(false),
            _ => None,
        })
        .unwrap_or(false)
}

/// The rule, on every host at the net's instant: a host that is due gets its `handle_timeout`, `service` and
/// `poll_transmit` until `None`, and must then be due later. With `known`, a host whose peer sleeps is let through
/// (the keepalive that cannot leave while the ring is full, `repro_transport2.rs`): the check returns true and the
/// case ends there, since the run would spin at that instant.
fn check(n: &mut Net, done: &[Op], known: bool) -> bool {
    let now = n.now;
    for i in 0..n.hosts.len() {
        if n.hosts[i].ep.poll_timeout().is_none_or(|d| d > now) {
            continue;
        }
        n.hosts[i].ep.handle_timeout(now);
        n.hosts[i].service(now);
        n.pump(i);
        let after = n.hosts[i].ep.poll_timeout();
        if known && after.is_some_and(|d| d <= now) && peer_asleep(n, i) {
            return true;
        }
        if after.is_some_and(|d| d <= now) {
            let s = n.hosts[i].ep.node_stats();
            let last: Vec<_> = n.hosts[i]
                .events
                .iter()
                .rev()
                .take(4)
                .map(|(t, e)| {
                    (
                        t.saturating_sub(10 * SEC) / MS,
                        format!("{e:?}").chars().take(40).collect::<String>(),
                    )
                })
                .collect();
            let h = &n.hosts[i];
            let ss: Vec<_> = h
                .opened
                .iter()
                .chain(&h.dialed)
                .filter_map(|s| h.stats(*s))
                .map(|st| {
                    (
                        st.established,
                        st.pto_count,
                        st.pto,
                        st.pulse_due,
                        st.held,
                        st.heard.saturating_sub(10 * SEC) / MS,
                    )
                })
                .collect();
            let sig = kind(done.last());
            ephyra::signature(sig);
            panic!(
                "{sig}: host {i} at {now} (t0 + {} ms): poll_timeout {after:?} after handle_timeout; sessions {} half_open {}; sessions (established, pto_count, pto, pulse_due, held, heard ms) {ss:?}; last events {last:?}; steps {done:?}",
                now.saturating_sub(10 * SEC) / MS,
                s.sessions,
                s.half_open,
            );
        }
    }
    false
}

impl World {
    /// Run the net to `deadline` with the rule checked at every step.
    pub fn run_to(&mut self, deadline: u64) {
        if self.ended {
            return;
        }
        let (done, known) = (self.done.clone(), self.known);
        let (mut first, mut ended) = (true, false);
        self.net.run(deadline, |n| {
            if !first {
                ended = check(n, &done, known);
            }
            first = false;
            ended
        });
        if ended {
            self.ended = true;
            return;
        }
        fail(self.net.first_violation());
        self.net.now = self.net.now.max(deadline);
    }

    pub fn run_for(&mut self, ms: u64) {
        let end = self.net.now.saturating_add(ms * MS);
        self.run_to(end);
    }

    fn session(&self, side: u8) -> Option<(usize, SessionId)> {
        if side == 0 {
            Some((self.a, self.sa))
        } else {
            self.sb.map(|s| (self.b, s))
        }
    }

    fn host(&self, side: u8) -> usize {
        if side == 0 { self.a } else { self.b }
    }

    fn dial(&mut self) -> Option<SessionId> {
        let (addr, peer) = (self.net.hosts[self.b].addr, self.net.hosts[self.b].id);
        let now = self.net.now;
        match self.net.hosts[self.a].cmd(
            now,
            Command::Connect {
                node: peer,
                alpn: ALPN_A,
                addrs: &[addr],
                role: Role::Other,
            },
        ) {
            Ok(core_harness::Reply2 {
                value: Value::Session(s),
            }) => Some(s),
            _ => None,
        }
    }

    /// The server's newest session.
    fn incoming(&self) -> Option<SessionId> {
        self.net.hosts[self.b].events.iter().rev().find_map(|(_, e)| match e {
            Event::Incoming { session, .. } => Some(*session),
            _ => None,
        })
    }

    pub fn apply(&mut self, op: &Op) {
        if self.ended {
            return;
        }
        let now = self.net.now;
        self.done.push(op.clone());
        match *op {
            Op::Wait(ms) => return self.run_for(ms),
            Op::Write { from, len, fin } => {
                if let Some((h, s)) = self.session(from)
                    && self.net.hosts[h].opened.contains(&s)
                    && let Ok(core_harness::Reply2 {
                        value: Value::Stream(st),
                    }) = self.net.hosts[h].cmd(now, Command::OpenStream { session: s, bidi: true })
                {
                    let data = (0..len).map(|i| (i % 251) as u8).collect();
                    self.net.hosts[h].write(now, s, st, data, fin);
                }
            }
            Op::Datagram { from, len } => {
                if let Some((h, s)) = self.session(from) {
                    let _ = self.net.hosts[h].cmd(
                        now,
                        Command::SendDatagram {
                            session: s,
                            data: &vec![9; len],
                        },
                    );
                }
            }
            Op::Ping(from) => {
                if let Some((h, s)) = self.session(from) {
                    let _ = self.net.hosts[h].cmd(now, Command::Ping { session: s });
                }
            }
            Op::Read { host, on } => {
                let h = self.host(host);
                self.net.hosts[h].auto_read = on;
            }
            Op::Cut(ms) => {
                self.net.faults.cut = true;
                self.run_for(ms);
                self.net.faults.cut = false;
            }
            Op::Loss(pm) => self.net.faults.loss = pm,
            Op::Iface { host, ev } => {
                let h = self.host(host);
                let ev = match ev {
                    0 => IfaceEvent::Down,
                    1 => IfaceEvent::Up,
                    2 => IfaceEvent::Suspend,
                    3 => IfaceEvent::Resume { moved: false },
                    _ => IfaceEvent::Resume { moved: true },
                };
                self.net.hosts[h].ep.iface_event(now, IfaceId(0), ev);
            }
            Op::Sleep(host) => {
                let h = self.host(host);
                let _ = self.net.hosts[h].cmd(now, Command::Suspend);
            }
            Op::Wake { host, moved } => {
                let h = self.host(host);
                let _ = self.net.hosts[h].cmd(now, Command::Resume { moved });
            }
            Op::Close(from) => {
                if let Some((h, s)) = self.session(from) {
                    let _ = self.net.hosts[h].cmd(now, Command::Close { session: s, error: 0 });
                }
            }
            Op::Shutdown(host) => {
                let h = self.host(host);
                let _ = self.net.hosts[h].cmd(now, Command::Shutdown);
            }
            Op::Redial => {
                if let Some(s) = self.dial() {
                    self.sa = s;
                }
            }
            Op::Punch { from, port } => {
                if let Some((h, s)) = self.session(from) {
                    let addr: SocketAddr = ([198, 51, 100, 7], 9000 + port).into();
                    let _ = self.net.hosts[h].cmd(now, Command::Punch { session: s, addr });
                }
            }
        }
        self.run_for(30);
        self.sb = self.incoming().or(self.sb);
    }
}

/// A connected pair (or a dial that failed, which the script then runs on), with the clock starting at `start`.
pub fn world(c: &Case, start: u64) -> World {
    let mut net = Net::new(c.seed);
    net.now = start;
    net.delay = c.delay_ms * MS;
    net.faults.jitter = c.jitter_ms * MS;
    let cfg = HostCfg {
        split: c.split,
        room: c.room,
        ..HostCfg::default()
    };
    let (a, b) = (net.add(1, cfg), net.add(2, cfg));
    let (addr, peer, now) = (net.hosts[b].addr, net.hosts[b].id, net.now);
    let Ok(core_harness::Reply2 {
        value: Value::Session(sa),
    }) = net.hosts[a].cmd(
        now,
        Command::Connect {
            node: peer,
            alpn: ALPN_A,
            addrs: &[addr],
            role: Role::Other,
        },
    )
    else {
        panic!("the dial was refused")
    };
    let mut w = World {
        net,
        a,
        b,
        sa,
        sb: None,
        done: Vec::new(),
        known: false,
        ended: false,
    };
    let deadline = w.net.now.saturating_add(31 * SEC);
    let done = Vec::new();
    let mut first = true;
    w.net.run(deadline, |n| {
        if !first {
            check(n, &done, false);
        }
        first = false;
        n.hosts[a].opened.contains(&sa) && n.hosts[b].count(|e| matches!(e, Event::Incoming { .. })) > 0
    });
    fail(w.net.first_violation());
    w.sb = w.incoming();
    w
}

/// The whole case: connect, the script, then 70 s more so that idle timeouts, closes and probes run out.
pub fn run(c: &Case) {
    run_at(c, 10 * SEC);
}

pub fn run_at(c: &Case, start: u64) {
    run_with(c, start, false);
}

/// [`run_at`], letting the known cause pass when `known`.
pub fn run_with(c: &Case, start: u64, known: bool) {
    let mut w = world(c, start);
    w.known = known;
    for op in &c.ops {
        w.apply(op);
    }
    w.run_for(70_000);
}
