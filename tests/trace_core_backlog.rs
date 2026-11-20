//! Trace generation for the accept room of a hub: a host that keeps a queue of `qcap` places, takes every `Incoming` of
//! its endpoint (`session_taken`), tells the endpoint how many places are free (`set_backlog_room`) and accepts the
//! oldest waiting session now and then, recorded as ndjson (`core_backlog.ndjson`) for the TLA+ trace check
//! (`TraceCoreBacklog.tla`).
//!
//! A `call` line follows every step of the pump: the half-open slots live, those that are owed to the host, the slots
//! made and freed since the last step, the first flights refused and the sessions owed. A `take` line follows every
//! `Incoming` the host reads, an `accept` line every session it accepts. The host is the test's own: the facade's
//! host code is not used.
//!
//! The runs are scripted (six dialers for each room, one cut off after its first flight, one that closes at once, one
//! `Incoming` read twice; they end at 60 s, and a dialer whose dial failed dials again, because the retries of dialers
//! that dialed together are synchronised by the doubling of the handshake timeout, so one room admits one of them per
//! retry instant and the fifth is admitted only by a second dial) and 16 seeded random ones. The test asserts, without the model: the sessions the endpoint
//! owes equal the live slots marked owed after every step; a `Reserved` answer always finds a place; a first flight is
//! refused in every scripted run; every dialer that is not cut off gets its `Incoming`; and `Gone` and `Unreserved`
//! each occur in the scripted runs. The trace is written to the directory in `PINC_TRACE_DIR` when it is set;
//! otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::manual_is_multiple_of,
    clippy::needless_range_loop,
    clippy::similar_names
)]

use std::collections::VecDeque;
use std::fmt::Write as _;

use pinc_core::{Answer, Command, Event, Query, Role, SessionId, Taken};
use pinc_tests::*;

const SLOTS: usize = 8;

struct Host {
    hub: usize,
    qcap: usize,
    queue: VecDeque<SessionId>,
    seen: usize,
    /// Incomings whose take waits until the time (a host that reads late).
    later: Vec<(u64, SessionId)>,
    /// Members whose `Incoming` the host reads late.
    late: Vec<usize>,
    /// A session read once more after it was taken.
    twice: Option<SessionId>,
    twice_done: bool,
    accept_after: u64,
    accept_odds: (u64, u64),
    rng: SplitMix64,
    prev: [Option<u64>; SLOTS],
    refused: u64,
    out: String,
    gone: u32,
    unreserved: u32,
    incoming_from: Vec<usize>,
}

fn list(v: &[usize]) -> String {
    format!("[{}]", v.iter().map(usize::to_string).collect::<Vec<_>>().join(","))
}

impl Host {
    fn new(hub: usize, qcap: usize, accept_after: u64, accept_odds: (u64, u64), seed: u64) -> Self {
        Self {
            hub,
            qcap,
            queue: VecDeque::new(),
            seen: 0,
            later: Vec::new(),
            late: Vec::new(),
            twice: None,
            twice_done: false,
            accept_after,
            accept_odds,
            rng: SplitMix64::new(seed),
            prev: [None; SLOTS],
            refused: 0,
            out: format!("{{\"t\":\"init\",\"qcap\":{qcap}}}\n"),
            gone: 0,
            unreserved: 0,
            incoming_from: Vec::new(),
        }
    }

    fn room(&self, net: &mut CoreNet) {
        net.nodes[self.hub].ep.set_backlog_room(self.qcap - self.queue.len());
    }

    /// The `call` of this step; also checks the sessions owed against the slots marked owed.
    fn call(&mut self, net: &CoreNet) {
        let ep = &net.nodes[self.hub].ep;
        let (mut live, mut ow, mut made, mut freed) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
        let mut now = [None; SLOTS];
        for i in 0..SLOTS {
            if let Some(h) = ep.half_open_slot(i) {
                live.push(i);
                if h.owed {
                    ow.push(i);
                }
                now[i] = Some(h.created);
            }
            if now[i].is_some() && now[i] != self.prev[i] {
                made.push(i);
            }
            if self.prev[i].is_some() && now[i] != self.prev[i] {
                freed.push(i);
            }
        }
        let st = ep.node_stats();
        assert_eq!(
            st.owed,
            ow.len(),
            "the sessions owed are not the slots marked owed at {}",
            net.now
        );
        let refused = st.backlog_refused - self.refused;
        self.refused = st.backlog_refused;
        self.prev = now;
        writeln!(
            self.out,
            r#"{{"t":"call","live":{},"ow":{},"made":{},"freed":{},"refused":{refused},"owed":{}}}"#,
            list(&live),
            list(&ow),
            list(&made),
            list(&freed),
            st.owed
        )
        .unwrap();
    }

    fn take(&mut self, net: &mut CoreNet, s: SessionId) {
        let hub = self.hub;
        let (res, alive, owed, placed) = match net.nodes[hub].ep.session_taken(s) {
            Taken::Reserved => {
                assert!(self.queue.len() < self.qcap, "a reserved session found no place");
                self.queue.push_back(s);
                ("reserved", 1, 0, 1)
            }
            Taken::Unreserved { owed } => {
                self.unreserved += 1;
                let placed = self.queue.len() + owed < self.qcap;
                if placed {
                    self.queue.push_back(s);
                } else {
                    let now = net.now;
                    let _ = net.nodes[hub].cmd(now, Command::Close { session: s, error: 0 });
                }
                ("unreserved", 1, owed, usize::from(placed))
            }
            Taken::Gone => {
                self.gone += 1;
                ("gone", 0, 0, 0)
            }
        };
        self.room(net);
        writeln!(
            self.out,
            r#"{{"t":"take","slot":{},"alive":{alive},"res":"{res}","owed":{owed},"placed":{placed},"room":{}}}"#,
            s.slot(),
            self.qcap - self.queue.len()
        )
        .unwrap();
    }

    /// One closure call of the pump.
    fn step(&mut self, net: &mut CoreNet) -> bool {
        self.call(net);
        let hub = self.hub;
        let new: Vec<(SessionId, pinc_crypto::NodeId)> = net.nodes[hub].events[self.seen..]
            .iter()
            .filter_map(|(_, e)| match e {
                Event::Incoming { session, node, .. } => Some((*session, *node)),
                _ => None,
            })
            .collect();
        self.seen = net.nodes[hub].events.len();
        for (s, node) in new {
            let from = (0..net.nodes.len()).find(|n| net.nodes[*n].node == node).unwrap();
            self.incoming_from.push(from);
            if self.late.contains(&from) {
                self.later.push((net.now + 3 * SEC_NS, s));
                continue;
            }
            self.take(net, s);
            if self.twice.is_none() && !self.twice_done {
                self.twice = Some(s);
            }
        }
        let due: Vec<SessionId> = self
            .later
            .iter()
            .filter(|(t, _)| *t <= net.now)
            .map(|(_, s)| *s)
            .collect();
        self.later.retain(|(t, _)| *t > net.now);
        for s in due {
            self.take(net, s);
        }
        if let Some(s) = self.twice.take() {
            self.twice_done = true;
            self.take(net, s);
        }
        let (num, den) = self.accept_odds;
        if net.now >= self.accept_after && !self.queue.is_empty() && self.rng.next_u64() % den < num {
            let s = self.queue.pop_front().unwrap();
            self.room(net);
            writeln!(self.out, r#"{{"t":"accept","room":{}}}"#, self.qcap - self.queue.len()).unwrap();
            if self.rng.next_u64() % 2 == 0 {
                let now = net.now;
                let _ = net.nodes[hub].cmd(now, Command::Close { session: s, error: 0 });
            }
        }
        false
    }

    fn run(&mut self, net: &mut CoreNet, until: u64) {
        net.run(until, |n| self.step(n));
        net.now = net.now.max(until);
    }
}

/// The first session of member `m`, by a walk of its endpoint.
fn first_session(net: &CoreNet, m: usize) -> Option<SessionId> {
    match net.nodes[m].ep.query(Query::SessionAt(0)) {
        Answer::Stats(st) => Some(st.session),
        _ => None,
    }
}

fn dial(net: &mut CoreNet, m: usize, hub: usize) {
    let (peer, to, now) = (net.nodes[hub].node, net.nodes[hub].addr, net.now);
    // A refusal (the member's table is full) is part of the run.
    let _ = net.nodes[m].connect(now, peer, ALPN_A, to, Role::Other);
}

#[derive(Default)]
struct Totals {
    gone: u32,
    unreserved: u32,
}

fn scripted(out: &mut String, tot: &mut Totals, qcap: usize) {
    let mut net = CoreNet::new(5 * MS_NS);
    let hub = net.add(1);
    let members: Vec<usize> = (2..=7).map(|t| net.add(t)).collect();
    let (closer, cut) = (members[4], members[5]);
    let start = net.now;
    let mut host = Host::new(hub, qcap, start + 2 * SEC_NS, (1, 4), 0xb10c + qcap as u64);
    host.late.push(closer);
    host.room(&mut net);
    let cut_addr = net.nodes[cut].addr;
    let mut sent = 0u32;
    net.loss = Some(Box::new(move |from, _, _| {
        if from != cut_addr {
            return false;
        }
        sent += 1;
        sent > 1
    }));
    for &m in &members {
        dial(&mut net, m, hub);
    }
    let mut closed = false;
    let mut redials = [0usize; 6];
    for k in 1..=600u64 {
        host.run(&mut net, start + k * 100 * MS_NS);
        // A dialer whose dial ended dials again (the cut one included: its flights are lost all the same).
        for (i, &m) in members.iter().enumerate() {
            let failed = net.nodes[m].count(|e| matches!(e, Event::ConnectFailed { .. }));
            if failed > redials[i] {
                redials[i] = failed;
                dial(&mut net, m, hub);
            }
        }
        if !closed
            && let Some(s) = first_session(&net, closer)
            && net.nodes[closer].saw(|e| matches!(e, Event::Connected { .. }))
        {
            let now = net.now;
            let _ = net.nodes[closer].cmd(now, Command::Close { session: s, error: 0 });
            closed = true;
        }
    }
    let ns = net.nodes[hub].ep.node_stats();
    assert!(
        ns.backlog_refused > 0 || qcap >= 6,
        "no first flight was refused with a room of {qcap}"
    );
    for (i, &m) in members.iter().enumerate() {
        assert!(
            m == cut || host.incoming_from.contains(&m),
            "member {i} never got its Incoming with a room of {qcap}"
        );
    }
    tot.gone += host.gone;
    tot.unreserved += host.unreserved;
    out.push_str(&host.out);
}

fn random(out: &mut String, seed: u64) {
    let mut rng = SplitMix64::new(seed);
    let qcap = 1 + (rng.next_u64() % 4) as usize;
    let odds = [(1, 8), (1, 4), (1, 2)][(rng.next_u64() % 3) as usize];
    let mut net = CoreNet::new(5 * MS_NS);
    let hub = net.add(1);
    let members: Vec<usize> = (2..=7).map(|t| net.add(t)).collect();
    let start = net.now;
    let mut host = Host::new(hub, qcap, start, odds, seed ^ 0x5eed);
    host.room(&mut net);
    // (time in ms, member, dial or close)
    let mut plan: Vec<(u64, usize, bool)> = Vec::new();
    for &m in &members {
        plan.push((rng.next_u64() % 10_000, m, true));
        if rng.next_u64() % 2 == 0 {
            plan.push((rng.next_u64() % 15_000, m, false));
        }
    }
    plan.sort_unstable();
    for (ms, m, dials) in plan {
        host.run(&mut net, start + ms * MS_NS);
        if dials {
            dial(&mut net, m, hub);
        } else if let Some(s) = first_session(&net, m) {
            let now = net.now;
            let _ = net.nodes[m].cmd(now, Command::Close { session: s, error: 0 });
        }
    }
    host.run(&mut net, start + 30 * SEC_NS);
    out.push_str(&host.out);
}

#[test]
fn core_backlog_traces() {
    let out = big_stack(|| {
        let mut out = String::new();
        let mut tot = Totals::default();
        for qcap in [1, 2, 3, 5] {
            scripted(&mut out, &mut tot, qcap);
        }
        assert!(tot.gone > 0, "no Incoming was read after its session ended");
        assert!(tot.unreserved > 0, "no session was read twice");
        for seed in 0..16 {
            random(&mut out, seed);
        }
        out
    });
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("core_backlog.ndjson"), out).unwrap();
    }
}
