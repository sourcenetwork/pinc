//! Trace generation for what `drive` does per session and for the pending dials (`client/drive.rs`): the real
//! `Connectivity` of one relay driven against an endpoint stub whose session statistics the test sets, recorded as
//! ndjson (`connect_drive.ndjson`) for the TLA+ trace check (`TraceConnectDrive.tla`).
//!
//! A session run dials one peer and then changes the stub's statistics (resends, established, the route, probe
//! timeouts, the last application data, the round trip), arms the punch timer and drives at clocks that step forward
//! and back; after each drive the commands the layer sent for the session are recorded (hold and unhold of the
//! flight, the paths, the carrier word, a punch round). A pending run dials many peers with no record and no hints,
//! lets the stub forget their sessions and records how many lookups are outstanding after each drive. Where the code
//! differs from its documentation (a drive drops the lookups of at most eight ended dials) the trace records what the
//! code does and the count is not pinned.
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::struct_excessive_bools,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::single_match_else
)]

mod connect_common;

use core::net::SocketAddr;
use std::collections::{BTreeSet, HashMap};

use connect_common::{SEC, big_stack, ed, id, nid};
use pinc_connect::client::dial::LATE_START;
use pinc_connect::client::{Config, Connectivity, Port, RelayCfg};
use pinc_core::{Command, CommandError, Events, NodeStats, PeerInfo, Reply, Role, SessionId, SessionStats, Value};
use pinc_crypto::{Drbg, NodeId, Software};
use pinc_security::{ConnId, Env};
use pinc_tests::{Host, SplitMix64};

/// The clock base: every dial is after `LATE_START`, so a hub's dial can go direct first.
const B: u64 = 1000 * SEC + LATE_START + SEC;
/// Milliseconds and seconds, in the whole microseconds the events keep.
const MS: i64 = 1000;
const S: i64 = 1_000_000;
/// Nanoseconds in a millisecond.
const NS_MS: u64 = 1_000_000;

type Conn = Connectivity<Software, 1, 4>;

/// A command the layer sent for a session, as far as the trace tells them apart.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Cmd {
    Hold(bool),
    Paths,
    Heard,
    Punch,
    First,
}

/// What the stub reports for a session.
#[derive(Clone, Copy)]
struct St {
    est: bool,
    /// 0 no route yet, 1 the relay path, 2 a direct path.
    kind: u8,
    pto: bool,
    valid: bool,
    last_app: u64,
    retx: u64,
    srtt: u64,
}

impl St {
    /// A dial in its handshake.
    const fn handshake() -> Self {
        Self {
            est: false,
            kind: 0,
            pto: false,
            valid: false,
            last_app: 0,
            retx: 0,
            srtt: 0,
        }
    }
}

/// The endpoint: it names the sessions, keeps the commands the layer sent and answers statistics from a table the
/// test sets.
struct Stub {
    next: u64,
    log: Vec<(SessionId, Cmd)>,
    st: HashMap<SessionId, St>,
    local: SocketAddr,
    relay: SocketAddr,
    direct: SocketAddr,
}

impl Port for Stub {
    type Src = pinc_transport::stream::NoSource;

    fn command(&mut self, _: u64, cmd: Command<'_, Self::Src>) -> Result<Reply, CommandError> {
        let value = match cmd {
            Command::Connect { .. } => {
                self.next += 1;
                let session = SessionId(self.next);
                self.st.insert(session, St::handshake());
                Value::Session(session)
            }
            Command::HoldFlight { session, hold } => {
                self.log.push((session, Cmd::Hold(hold)));
                Value::None
            }
            Command::FlightPaths { session, .. } => {
                self.log.push((session, Cmd::Paths));
                Value::None
            }
            Command::CarrierHeard { session, .. } => {
                self.log.push((session, Cmd::Heard));
                Value::None
            }
            Command::ReachOut { session, .. } | Command::Punch { session, .. } => {
                self.log.push((session, Cmd::Punch));
                Value::None
            }
            Command::FirstResend { session, .. } => {
                self.log.push((session, Cmd::First));
                Value::None
            }
            _ => Value::None,
        };
        Ok(Reply {
            value,
            events: Events::default(),
        })
    }

    fn stats(&self, session: SessionId) -> Option<SessionStats> {
        let s = self.st.get(&session)?;
        let transport = pinc_transport::conn::Stats {
            handshake_retransmits: s.retx,
            srtt: s.srtt,
            ..Default::default()
        };
        Some(SessionStats {
            session,
            node: None,
            alpn: None,
            role: Role::Other,
            gossip: false,
            dialer: true,
            established: s.est,
            allowed: true,
            path: None,
            route: match s.kind {
                1 => Some((self.local, self.relay)),
                2 => Some((self.local, self.direct)),
                _ => None,
            },
            thin: false,
            held: 0,
            held_dropped: 0,
            pto: 0,
            pto_count: if s.pto { 3 } else { 0 },
            path_validated: s.valid,
            heard: 0,
            heard_any: 0,
            pulse_due: false,
            last_app: s.last_app,
            sub: false,
            answered: true,
            transport,
        })
    }

    fn node(&self) -> Option<NodeStats> {
        Some(NodeStats {
            sessions: self.st.len(),
            half_open: 0,
            lrtt: 0,
            tgr: 0,
            hs_floor: 0,
            thin: false,
            ledger: 0,
            datagrams_in: 0,
            datagrams_out: 0,
            dropped_in: 0,
            dropped_out: 0,
            reach_dropped: 0,
            ext_dropped: 0,
            held_by_ledger: 0,
            stalled_in: 0,
            events_dropped: 0,
            events_lost: 0,
            fragments_held: 0,
            fragments_replayed: 0,
            fragments_expired: 0,
            fragments_evicted: 0,
            fragments_waiting: 0,
            holders_refused: 0,
            first_too_short: 0,
            stateless_rejects: 0,
            stateless_refused: 0,
            events_queued: 0,
            backlog_refused: 0,
            owed: 0,
        })
    }

    fn peer(&self, _: &NodeId) -> Option<PeerInfo> {
        None
    }

    fn reach_body(&self, _: SessionId, _: &mut [u8; pinc_core::REACH_BODY_MAX]) -> usize {
        0
    }

    fn by_conn_id(&self, _: &ConnId) -> Option<SessionStats> {
        None
    }
}

/// The layer, the stub and the record of a run.
struct Drv {
    conn: Box<Conn>,
    ep: Stub,
    drbg: Drbg,
    out: Vec<String>,
    sid: SessionId,
    /// The clock of the last call, in microseconds after `B`.
    off: i64,
    /// The dial had no record and no hints: its flight is held while the address is looked up.
    holds: bool,
    gone_at: Option<usize>,
}

impl Drv {
    fn new() -> Self {
        let host = Box::new(Host::new(0x41, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let local: SocketAddr = "192.168.1.2:4433".parse().unwrap();
        let mut relays = [None; 1];
        relays[0] = Some(RelayCfg {
            id: id(&ed(0x77)),
            udp: Some("203.0.113.10:4433".parse().unwrap()),
            tcp: Some("203.0.113.10:443".parse().unwrap()),
            ws: None,
        });
        let cfg = Config {
            me: host.identity.node_id(),
            identity: host.identity,
            relays,
            phone: false,
            restarted: false,
            start: 1000 * SEC,
            v6: false,
            keep_learn: false,
        };
        let mut conn: Box<Conn> = Box::new(Connectivity::new(cfg, host.prekey_info.clone(), Software, 7));
        conn.set_local(&[local]);
        Self {
            conn,
            ep: Stub {
                next: 0,
                log: Vec::new(),
                st: HashMap::new(),
                local,
                relay: local,
                direct: "198.51.100.7:4433".parse().unwrap(),
            },
            drbg: Drbg::new(&[0x62; 32]),
            out: Vec::new(),
            sid: SessionId(0),
            off: 0,
            holds: false,
            gone_at: None,
        }
    }

    /// The clock at `off` microseconds after `B`.
    fn at(off: i64) -> u64 {
        (B as i64 + off * 1000) as u64
    }

    /// A time as the event keeps it: whole microseconds after `B`.
    fn rel(ns: u64) -> i64 {
        (ns as i64 - B as i64) / 1000
    }

    /// Start a session run.
    fn session_run() -> Self {
        let mut r = Self::new();
        r.out.push(r#"{"op":"sinit"}"#.to_owned());
        r
    }

    /// Dial `peer` at the clock `off`; the session of the run is the one it names.
    fn dial(&mut self, off: i64, peer: NodeId, role: Role, alpn: &[u8], hints: &[SocketAddr]) -> SessionId {
        self.off = off;
        let sid = self
            .conn
            .dial(Self::at(off), &mut self.ep, peer, alpn, role, hints)
            .unwrap();
        self.ep.relay = self.conn.path_addr(0, &peer);
        sid
    }

    /// Dial the peer of a session run and record it.
    fn dial_peer(&mut self, off: i64, hub: bool, hints: &[SocketAddr]) {
        let before = self.ep.log.len();
        let (peer, role, alpn): (NodeId, Role, &[u8]) = if hub {
            (id(&ed(0x77)), Role::Hub, &b"pinc/hub"[..])
        } else {
            (nid(0xb7), Role::Other, &b"app/1"[..])
        };
        self.sid = self.dial(off, peer, role, alpn, hints);
        self.holds = hints.is_empty() && !hub;
        let direct = self.ep.log[before..]
            .iter()
            .any(|(s, c)| *s == self.sid && *c == Cmd::First);
        self.out.push(format!(
            r#"{{"op":"dial","now":{off},"direct":{direct},"holds":{}}}"#,
            self.holds
        ));
    }

    /// Change the statistics of the session and record them.
    fn stat(&mut self, f: impl FnOnce(&mut St)) {
        let Some(s) = self.ep.st.get_mut(&self.sid) else { return };
        f(s);
        let s = *s;
        self.out.push(format!(
            r#"{{"op":"stats","est":{},"dialer":true,"retx":{},"pto":{},"rr":{},"valid":{},"last":{},"rtt":{}}}"#,
            s.est,
            s.retx,
            s.pto,
            s.kind == 1,
            s.valid,
            Self::rel(s.last_app),
            s.srtt / 1000
        ));
    }

    /// The stub stops answering for the session.
    fn gone(&mut self) {
        self.ep.st.remove(&self.sid);
        self.gone_at = Some(self.ep.log.len());
        self.out.push(r#"{"op":"gone"}"#.to_owned());
    }

    fn resume(&mut self, off: i64) {
        self.off = off;
        self.conn.resume_all(Self::at(off), &mut self.ep, false);
        self.out.push(format!(r#"{{"op":"resume","now":{off}}}"#));
    }

    /// Drive at the clock `off`; the commands for the session go back in order (the carrier word, a punch).
    fn run_drive(&mut self, off: i64) -> Vec<&'static str> {
        self.off = off;
        let now = Self::at(off);
        let before = self.ep.log.len();
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.drive(now, &mut self.ep, &mut env, None);
        let mut cmds: Vec<&'static str> = self.ep.log[before..]
            .iter()
            .filter(|(s, _)| *s == self.sid)
            .filter_map(|(_, c)| match c {
                Cmd::Hold(true) => Some("hold"),
                Cmd::Hold(false) => Some("unhold"),
                Cmd::Paths => Some("paths"),
                Cmd::Heard => Some("heard"),
                Cmd::Punch => Some("punch"),
                Cmd::First => None,
            })
            .collect();
        cmds.dedup_by(|a, b| a == b && *a == "punch");
        cmds
    }

    /// A drive of a session run: the checks that hold after every one, and the record.
    fn drive(&mut self, off: i64) -> Vec<&'static str> {
        let cmds = self.run_drive(off);
        match self.ep.st.get(&self.sid) {
            Some(st) => {
                let last_hold = self
                    .ep
                    .log
                    .iter()
                    .rev()
                    .find_map(|(s, c)| match c {
                        Cmd::Hold(h) if *s == self.sid => Some(*h),
                        _ => None,
                    })
                    .unwrap_or(false);
                assert_eq!(
                    last_hold,
                    self.holds && !st.est,
                    "the flight is held exactly while the dial waits for its peer's address"
                );
            }
            None => {
                let at = self.gone_at.unwrap_or(0);
                assert!(
                    self.ep.log[at..].iter().all(|(s, _)| *s != self.sid),
                    "a command for a session the endpoint no longer has"
                );
            }
        }
        let list: Vec<String> = cmds.iter().map(|c| format!(r#""{c}""#)).collect();
        self.out
            .push(format!(r#"{{"op":"drive","now":{off},"cmds":[{}]}}"#, list.join(",")));
        cmds
    }

    /// A drive of a pending run.
    fn pdrive(&mut self, off: i64) {
        self.run_drive(off);
        let lookups = self.conn.lookups_outstanding();
        self.out
            .push(format!(r#"{{"op":"pdrive","now":{off},"lookups":{lookups}}}"#));
    }

    /// Dial peer `k` of a pending run: no record, no hints.
    fn pdial(&mut self, off: i64, k: u8) -> SessionId {
        let sid = self.dial(off, nid(0x10 + k), Role::Other, b"app/1", &[]);
        let lookups = self.conn.lookups_outstanding();
        self.out.push(format!(
            r#"{{"op":"pdial","now":{off},"peer":{k},"sid":{},"lookups":{lookups}}}"#,
            sid.0
        ));
        sid
    }

    /// The stub forgets session `sid` of a pending run.
    fn pend(&mut self, sid: SessionId) {
        if self.ep.st.remove(&sid).is_some() {
            self.out.push(format!(r#"{{"op":"pend","sid":{}}}"#, sid.0));
        }
    }
}

fn count(cmds: &[&str], what: &str) -> usize {
    cmds.iter().filter(|c| **c == what).count()
}

/// Run 1: the dial waits for its peer's address while its tries go on, then it is established, loses its path and
/// is forgotten.
fn run1(out: &mut Vec<String>) {
    let mut r = Drv::session_run();
    r.dial_peer(0, false, &[]);
    r.drive(0);
    r.stat(|s| s.retx = 1);
    r.drive(100 * MS);
    r.stat(|s| s.retx = 2);
    r.drive(200 * MS);
    r.stat(|s| s.retx = 3);
    r.drive(300 * MS);
    r.stat(|s| {
        s.est = true;
        s.kind = 2;
        s.valid = true;
    });
    r.drive(400 * MS);
    r.stat(|s| {
        s.kind = 1;
        s.pto = true;
    });
    r.drive(500 * MS);
    r.gone();
    r.drive(600 * MS);
    r.drive(700 * MS);
    out.append(&mut r.out);
}

/// Run 2: a hub dialed direct first gets its relay copy and then its relay path back, once each.
fn run2(out: &mut Vec<String>) {
    let mut r = Drv::session_run();
    r.dial_peer(0, true, &["203.0.113.10:4433".parse().unwrap()]);
    assert_eq!(
        count(&r.drive(100 * MS), "paths"),
        0,
        "a path in the drive that has nothing due"
    );
    assert_eq!(
        count(&r.drive(300 * MS), "paths"),
        1,
        "the relay copy of a direct-first flight"
    );
    r.stat(|s| s.retx = 1);
    r.drive(400 * MS);
    r.stat(|s| s.est = true);
    assert_eq!(count(&r.drive(2 * S), "paths"), 1, "the relay path given back");
    assert_eq!(
        count(&r.drive(3 * S), "paths"),
        0,
        "a path in the drive that has nothing due"
    );
    out.append(&mut r.out);
}

/// Run 3: an established direct session punches when the node's link changed and the timer is due.
fn run3(out: &mut Vec<String>) {
    let mut r = Drv::session_run();
    r.dial_peer(0, false, &["198.51.100.7:4433".parse().unwrap()]);
    r.stat(|s| {
        s.est = true;
        s.kind = 2;
        s.valid = true;
        s.last_app = B;
        s.srtt = 5 * NS_MS;
    });
    r.resume(S);
    assert_eq!(
        count(&r.drive(S + 50 * MS), "punch"),
        0,
        "a punch before the timer is due"
    );
    assert_eq!(
        count(&r.drive(S + 100 * MS), "punch"),
        1,
        "no punch when the timer is due"
    );
    r.stat(|s| {
        s.srtt = 50 * NS_MS;
        s.last_app = B;
    });
    r.drive(70 * S);
    r.stat(|s| s.last_app = 0);
    r.drive(140 * S);
    r.drive(S);
    out.append(&mut r.out);
}

/// Run 4: a handshake that never completes, with the clock jumping.
fn run4(out: &mut Vec<String>) {
    let mut r = Drv::session_run();
    r.dial_peer(0, false, &["198.51.100.7:4433".parse().unwrap()]);
    r.resume(0);
    r.drive(200 * MS);
    r.stat(|s| s.retx = 5);
    r.drive(10 * S);
    r.drive(5 * S);
    r.gone();
    r.drive(20 * S);
    out.append(&mut r.out);
}

/// One seeded session run: a dial and 30 random steps.
fn seeded(seed: u64, out: &mut Vec<String>, deltas: &mut BTreeSet<i64>) {
    let mut r = Drv::session_run();
    let mut rng = SplitMix64::traced(0xD21E_0000 + seed);
    let hints: Vec<SocketAddr> = if seed % 2 == 0 {
        vec!["198.51.100.7:4433".parse().unwrap()]
    } else {
        Vec::new()
    };
    r.dial_peer(0, false, &hints);
    for step in 0..30 {
        let gone = r.gone_at.is_some();
        let est = r.ep.st.get(&r.sid).is_some_and(|s| s.est);
        // 0 resend, 1 established, 2 relay route, 3 direct route, 4 probe timeouts, 5 last app, 6 round trip,
        // 7 resume, 8 gone, 9 drive
        let mut ops = vec![7u8, 9, 9, 9];
        if !gone {
            ops.extend([2, 3, 4, 5, 6]);
            if !est {
                ops.extend([0, 1]);
            }
            if step >= 24 {
                ops.push(8);
            }
        }
        match ops[(rng.next_u64() % ops.len() as u64) as usize] {
            0 => r.stat(|s| s.retx += 1),
            1 => r.stat(|s| s.est = true),
            2 => r.stat(|s| {
                s.kind = 1;
                s.valid = false;
            }),
            3 => r.stat(|s| {
                s.kind = 2;
                s.valid = true;
            }),
            4 => {
                let pto = rng.next_u64() % 2 == 0;
                r.stat(|s| s.pto = pto);
            }
            5 => {
                let last = [0, B, Drv::at(r.off)][(rng.next_u64() % 3) as usize];
                r.stat(|s| s.last_app = last);
            }
            6 => {
                let rtt = (if rng.next_u64() % 2 == 0 { 5 } else { 50 }) * NS_MS;
                r.stat(|s| s.srtt = rtt);
            }
            7 => r.resume(r.off),
            8 => r.gone(),
            _ => {
                let step_us = [100 * MS, 2 * S, -S, 65 * S][(rng.next_u64() % 4) as usize];
                let off = (r.off + step_us).clamp(-200 * S, 200 * S);
                deltas.insert(step_us);
                r.drive(off);
            }
        }
    }
    out.append(&mut r.out);
}

/// Run 5: twelve peers wait for an address, ten of their dials end, then the other two.
fn run5(out: &mut Vec<String>) {
    let mut r = Drv::new();
    r.out.push(r#"{"op":"pinit"}"#.to_owned());
    let sids: Vec<SessionId> = (1..=12).map(|k| r.pdial(0, k)).collect();
    assert_eq!(r.conn.lookups_outstanding(), 12, "a lookup for each of the dials");
    for s in &sids[..10] {
        r.pend(*s);
    }
    r.pdrive(S);
    assert!(
        r.conn.lookups_outstanding() < 12,
        "the dials that ended kept all their lookups"
    );
    for s in &sids[10..] {
        r.pend(*s);
    }
    r.pdrive(2 * S);
    r.pdrive(3 * S);
    out.append(&mut r.out);
}

/// Run 6: dials ended before and after a drive.
fn run6(out: &mut Vec<String>) {
    let mut r = Drv::new();
    r.out.push(r#"{"op":"pinit"}"#.to_owned());
    let mut sids: Vec<SessionId> = (1..=4).map(|k| r.pdial(0, k)).collect();
    r.pend(sids[0]);
    r.pend(sids[1]);
    r.pdrive(S);
    sids.extend((5..=8).map(|k| r.pdial(S, k)));
    for s in sids {
        r.pend(s);
    }
    r.pdrive(2 * S);
    r.pdrive(3 * S);
    out.append(&mut r.out);
}

#[test]
fn connect_drive_trace() {
    big_stack(|| {
        let mut out = Vec::new();
        run1(&mut out);
        run2(&mut out);
        run3(&mut out);
        run4(&mut out);
        let mut deltas = BTreeSet::new();
        for seed in 0..40 {
            let before = out.len();
            seeded(seed, &mut out, &mut deltas);
            // every call writes one line: the stub's start, the dial and 30 steps
            assert_eq!(out.len() - before, 32, "seed {seed}");
        }
        run5(&mut out);
        run6(&mut out);
        assert_eq!(out.len(), 93 + 40 * 32, "the trace holds {} events", out.len());
        let seen = |needle: &str| out.iter().any(|l| l.contains(needle));
        for needle in [
            r#""holds":true"#,
            r#""holds":false"#,
            r#""op":"stats","est":true"#,
            r#""op":"resume""#,
            r#""op":"gone""#,
            r#""hold""#,
            r#""unhold""#,
            r#""punch""#,
        ] {
            assert!(seen(needle), "no run reached {needle}");
        }
        assert_eq!(
            deltas.into_iter().collect::<Vec<_>>(),
            [-S, 100 * MS, 2 * S, 65 * S],
            "the seeded runs did not take every clock step"
        );
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::write(format!("{dir}/connect_drive.ndjson"), out.join("\n") + "\n").unwrap();
        }
    });
}
