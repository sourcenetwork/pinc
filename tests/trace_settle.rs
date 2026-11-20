//! Trace generation for the settle step of a connected session: pairs of real endpoints (`pinc-core`, built with the
//! `trace` feature) run on the in-memory network of `CoreNet`, and every settle of a connected session that is not
//! closing is recorded as one ndjson line (`core/settle.ndjson` under `PINC_TRACE_DIR`) for the TLA+ trace check
//! (`TraceSettle.tla`).
//!
//! A line carries what `settle_core` read (the role, the side, whether the path is direct, the last send, the last
//! receive, the last application data, the end of the quiet period, the flight, the pulse flag), what the plan decided
//! (the ping and the review moment), whether the plan changed and the interval then handed to the connection, and what
//! the deadline was made of (the connection's own timer, the least standby ping, the access recheck, the end of an
//! unauthenticated life, the due flag, the deadline). A `u64` is written as four 16-bit limbs, least significant first
//! (TLC cannot read a number above 2^31), an absent value as `[]`. The session is named by its id with the scenario and
//! the node in the top byte (`scenario * 4 + node`), so ids of different endpoints and scenarios never meet.
//!
//! The scenarios: a hub session watched by a member (silence, then writes every 7 s); a plain session past the 90 s
//! window, written to, then idling out; a pulse handed to the layer above; a resume's quiet period; a close; and 16
//! seeded random runs of every command that moves an input. The test checks by itself that no record was dropped, that
//! every role, both sides, a pulse and a due ping, a quiet period and a plan with no ping were seen, that the deadline
//! is the least of its parts and that a ping is due exactly when it is at or before now in a pulse. The plan and the
//! interval the connection holds are checked by `TraceSettle.tla`.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::many_single_char_names
)]

use std::fmt::Write as _;

use pinc_core::{Answer, Command, Event, Query, Role, SETTLE_CAPACITY, SessionId, SettleRecord, Value};
use pinc_tests::{ALPN_A, CoreNet, MS_NS, SEC_NS, SplitMix64, big_stack};

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn opt(v: Option<u64>) -> String {
    v.map_or_else(|| "[]".to_string(), limbs)
}

fn role_name(r: Role) -> &'static str {
    match r {
        Role::Hub => "hub",
        Role::Member => "member",
        Role::Other => "other",
    }
}

/// The records read so far: the ndjson text, and each record with the node it came from and its scenario.
struct Log {
    out: String,
    all: Vec<(u64, usize, SettleRecord)>,
    scenario: u64,
}

impl Log {
    /// Read every settle record of every node of `net` into the log.
    fn drain(&mut self, net: &mut CoreNet) {
        for k in 0..net.nodes.len() {
            while let Some(r) = net.nodes[k].ep.poll_settle() {
                let tag = self.scenario * 4 + k as u64;
                assert!(tag <= 255, "the scenario and node tag does not fit a byte");
                assert_eq!(r.session >> 56, 0, "a session id uses the byte kept for the tag");
                let _ = writeln!(
                    self.out,
                    r#"{{"t":"settle","sid":{},"role":"{}","dialer":{},"direct":{},"now":{},"tx":{},"rx":{},"app":{},"qu":{},"flight":{},"pulse":{},"ping":{},"review":{},"changed":{},"interval":{},"own":{},"standby":{},"acp":{},"end":{},"due":{},"deadline":{}}}"#,
                    limbs(r.session | (tag << 56)),
                    role_name(r.role),
                    r.dialer,
                    r.direct,
                    limbs(r.now),
                    limbs(r.last_tx),
                    limbs(r.last_rx),
                    limbs(r.last_app),
                    limbs(r.quiet_until),
                    r.in_flight,
                    r.pulse,
                    opt(r.ping_at),
                    opt(r.review_at),
                    r.changed,
                    opt(r.interval),
                    limbs(r.own),
                    opt(r.standby),
                    opt(r.acp),
                    opt(r.end),
                    r.pulse_due,
                    opt(r.deadline),
                );
                self.all.push((self.scenario, k, r));
            }
        }
    }

    /// The end of a scenario: nothing dropped, and something recorded.
    fn finish(&mut self, net: &mut CoreNet) {
        self.drain(net);
        for (k, n) in net.nodes.iter().enumerate() {
            assert_eq!(
                n.ep.settle_dropped(),
                0,
                "scenario {}: node {k} dropped settle records (the ring holds {SETTLE_CAPACITY})",
                self.scenario
            );
        }
        assert!(
            self.all.iter().any(|(s, _, _)| *s == self.scenario),
            "scenario {}: no settle was recorded",
            self.scenario
        );
    }
}

/// Run for `span` nanoseconds of virtual time, reading the records as they come.
fn pump(net: &mut CoreNet, span: u64, log: &mut Log) {
    let end = net.now + span;
    net.run(end, |n| {
        log.drain(n);
        false
    });
    net.now = end;
    log.drain(net);
}

/// `connect_pair` of `CoreNet`, reading the records as they come.
fn dial(net: &mut CoreNet, a: usize, b: usize, role: Role, log: &mut Log) -> (SessionId, SessionId) {
    let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
    let na = net.nodes[a].count(|e| matches!(e, Event::Connected { .. }));
    let nb = net.nodes[b].count(|e| matches!(e, Event::Incoming { .. }));
    let rep = net.nodes[a].connect(now, peer, ALPN_A, to, role).unwrap();
    let sa = net.nodes[a].session(&rep);
    let ok = net.run(now + 10 * SEC_NS, |n| {
        log.drain(n);
        n.nodes[a].count(|e| matches!(e, Event::Connected { .. })) > na
            && n.nodes[b].count(|e| matches!(e, Event::Incoming { .. })) > nb
    });
    assert!(ok, "no session: {:?} / {:?}", net.nodes[a].events, net.nodes[b].events);
    log.drain(net);
    let sb = net.nodes[b]
        .events
        .iter()
        .rev()
        .find_map(|(_, e)| match e {
            Event::Incoming { session, .. } => Some(*session),
            _ => None,
        })
        .unwrap();
    (sa, sb)
}

/// A new stream on `session` of node `k` with `n` bytes written; whether both worked.
fn write(net: &mut CoreNet, k: usize, session: SessionId, n: usize) -> bool {
    let now = net.now;
    let data = vec![7u8; n];
    let Ok(rep) = net.nodes[k].cmd(now, Command::OpenStream { session, bidi: false }) else {
        return false;
    };
    let Value::Stream(stream) = rep.value else { return false };
    let wrote = net.nodes[k]
        .cmd(
            now,
            Command::Write {
                session,
                stream,
                data: &data,
            },
        )
        .is_ok();
    // A peer gives credit for a new stream only after it has read one to its end: a one-way stream ends with the
    // finish, a two-way one only when the peer ends its half too.
    wrote && net.nodes[k].cmd(now, Command::Finish { session, stream }).is_ok()
}

fn command(net: &mut CoreNet, k: usize, c: Command<'_, pinc_transport::stream::NoSource>) -> bool {
    let now = net.now;
    net.nodes[k].cmd(now, c).is_ok()
}

fn new_net() -> (CoreNet, usize, usize) {
    let mut net = CoreNet::new(5 * MS_NS);
    let a = net.add(1);
    let b = net.add(2);
    (net, a, b)
}

/// A hub session watched by a member: silence, then a write every 7 s.
fn watched_hub(log: &mut Log) {
    let (mut net, a, b) = new_net();
    let (_, sb) = dial(&mut net, a, b, Role::Hub, log);
    assert!(command(
        &mut net,
        b,
        Command::SetRole {
            session: sb,
            role: Role::Member
        }
    ));
    pump(&mut net, 200 * SEC_NS, log);
    for _ in 0..10 {
        assert!(write(&mut net, b, sb, 100));
        pump(&mut net, 7 * SEC_NS, log);
    }
    pump(&mut net, 100 * SEC_NS, log);
    log.finish(&mut net);
}

/// A plain session: idle past the 90 s window, written to for 30 s, then idle until it ends.
fn plain_session(log: &mut Log) {
    let (mut net, a, b) = new_net();
    let (sa, _) = dial(&mut net, a, b, Role::Other, log);
    pump(&mut net, 120 * SEC_NS, log);
    for _ in 0..10 {
        assert!(write(&mut net, a, sa, 100));
        pump(&mut net, 3 * SEC_NS, log);
    }
    pump(&mut net, 150 * SEC_NS, log);
    log.finish(&mut net);
}

/// A pulse: the layer above sends the keepalive when the session reports it due.
fn pulse(log: &mut Log) {
    let (mut net, a, b) = new_net();
    let (sa, _) = dial(&mut net, a, b, Role::Hub, log);
    assert!(command(&mut net, a, Command::SetPulse { session: sa, on: true }));
    for _ in 0..5 {
        pump(&mut net, 20 * SEC_NS, log);
        if matches!(net.nodes[a].ep.query(Query::Stats(sa)), Answer::Stats(s) if s.pulse_due) {
            assert!(command(
                &mut net,
                a,
                Command::Pulse {
                    session: sa,
                    sent: true
                }
            ));
            pump(&mut net, 50 * MS_NS, log);
            assert!(command(
                &mut net,
                a,
                Command::Pulse {
                    session: sa,
                    sent: false
                }
            ));
        }
    }
    assert!(command(&mut net, a, Command::SetPulse { session: sa, on: false }));
    pump(&mut net, 100 * SEC_NS, log);
    log.finish(&mut net);
}

/// Three suspensions and resumptions: each starts a quiet period.
fn quiet_period(log: &mut Log) {
    let (mut net, a, b) = new_net();
    let _ = dial(&mut net, a, b, Role::Hub, log);
    for _ in 0..3 {
        assert!(command(&mut net, a, Command::Suspend));
        pump(&mut net, 5 * SEC_NS, log);
        assert!(command(&mut net, a, Command::Resume { moved: false }));
        pump(&mut net, 60 * SEC_NS, log);
    }
    log.finish(&mut net);
}

/// A close: the closing settles are not recorded, so no record of the closed session is dated after it.
fn close(log: &mut Log) {
    let (mut net, a, b) = new_net();
    let (sa, _) = dial(&mut net, a, b, Role::Other, log);
    pump(&mut net, 30 * SEC_NS, log);
    let closed_at = net.now;
    assert!(command(&mut net, a, Command::Close { session: sa, error: 0 }));
    pump(&mut net, 10 * SEC_NS, log);
    log.finish(&mut net);
    let late = log
        .all
        .iter()
        .filter(|(s, k, r)| *s == log.scenario && *k == a && r.session == sa.0 && r.now > closed_at)
        .count();
    assert_eq!(
        late, 0,
        "{late} records of the closed session are dated after the close"
    );
}

/// One seeded random run: 40 commands and spans of time on a pair of sessions of drawn roles.
fn random(seed: u64, log: &mut Log) {
    let mut rng = SplitMix64::new(seed);
    let roles = [Role::Hub, Role::Member, Role::Other];
    let draw = |rng: &mut SplitMix64| roles[(rng.next_u64() % 3) as usize];
    let (mut net, a, b) = new_net();
    let (dialer_role, other_role) = (draw(&mut rng), draw(&mut rng));
    let (sa, sb) = dial(&mut net, a, b, dialer_role, log);
    let _ = command(
        &mut net,
        b,
        Command::SetRole {
            session: sb,
            role: other_role,
        },
    );
    let side = [(a, sa), (b, sb)];
    let mut pulsing = [false; 2];
    for _ in 0..40 {
        let s = (rng.next_u64() % 2) as usize;
        let (k, session) = side[s];
        match rng.next_u64() % 6 {
            0 => {
                let span = rng.next_u64() % (30 * SEC_NS) + MS_NS;
                pump(&mut net, span, log);
            }
            1 => {
                let n = (rng.next_u64() % 1200 + 1) as usize;
                let _ = write(&mut net, k, session, n);
            }
            2 => {
                pulsing[s] = !pulsing[s];
                let _ = command(
                    &mut net,
                    k,
                    Command::SetPulse {
                        session,
                        on: pulsing[s],
                    },
                );
            }
            3 => {
                let sent = rng.next_u64() % 2 == 0;
                let _ = command(&mut net, k, Command::Pulse { session, sent });
            }
            4 => {
                let _ = command(&mut net, k, Command::Suspend);
                let _ = command(&mut net, k, Command::Resume { moved: false });
            }
            _ => {
                let role = draw(&mut rng);
                let _ = command(&mut net, k, Command::SetRole { session, role });
            }
        }
    }
    log.finish(&mut net);
}

/// What every record says without the model: the deadline is the least of its parts, a ping is due when it is at or
/// before now in a pulse.
fn check(scenario: u64, r: &SettleRecord) {
    let ping_later = r.ping_at.filter(|p| r.pulse && *p > r.now);
    let want = [Some(r.own), r.review_at, ping_later, r.standby, r.acp, r.end]
        .into_iter()
        .flatten()
        .min();
    assert!(
        r.deadline.is_some() && r.deadline == want,
        "scenario {scenario}: the deadline is not the least of its parts: {r:?}"
    );
    assert_eq!(
        r.pulse_due,
        r.pulse && r.ping_at.is_some_and(|p| p <= r.now),
        "scenario {scenario}: pulse_due is not 'a ping at or before now in a pulse': {r:?}"
    );
    assert!(
        r.changed || r.interval.is_none(),
        "scenario {scenario}: an interval with no change: {r:?}"
    );
}

#[test]
fn every_settle_of_a_connected_session_is_recorded_for_the_model() {
    let out = big_stack(|| {
        let mut log = Log {
            out: String::new(),
            all: Vec::new(),
            scenario: 0,
        };
        let scenarios: [fn(&mut Log); 5] = [watched_hub, plain_session, pulse, quiet_period, close];
        for (n, f) in scenarios.iter().enumerate() {
            log.scenario = n as u64 + 1;
            f(&mut log);
        }
        for seed in 1..=16 {
            log.scenario = 5 + seed;
            random(seed, &mut log);
        }
        for (s, _, r) in &log.all {
            check(*s, r);
        }
        let any = |f: &dyn Fn(&SettleRecord) -> bool| log.all.iter().any(|(_, _, r)| f(r));
        assert!(any(&|r| r.role == Role::Hub), "no record of a hub session");
        assert!(any(&|r| r.role == Role::Member), "no record of a member session");
        assert!(any(&|r| r.role == Role::Other), "no record of a plain session");
        assert!(any(&|r| r.dialer), "no record of a dialing side");
        assert!(any(&|r| !r.dialer), "no record of an answering side");
        assert!(any(&|r| r.pulse && r.pulse_due), "no record of a due ping in a pulse");
        assert!(
            any(&|r| r.quiet_until > r.now && !r.in_flight),
            "no record in a quiet period"
        );
        assert!(any(&|r| !r.changed), "no record of an unchanged plan");
        assert!(any(&|r| r.ping_at.is_none()), "no record of a plan with no ping");
        log.out
    });
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = format!("{dir}/core");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(format!("{dir}/settle.ndjson"), out).unwrap();
    }
}
