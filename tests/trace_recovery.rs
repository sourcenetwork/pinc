//! Trace generation for loss recovery: seeded random runs of a real `Recovery` engine (`vinc-transport`, built with
//! the `trace` feature) driven through the calls a connection makes, recorded as ndjson (`recovery.ndjson`) for the
//! TLA+ trace check (`TraceRecovery.tla`) and the Lean replay (`Vinc/TraceRecovery.lean`).
//!
//! A run sends packets (some repair packets, some path MTU probes, with data frames or none) on several paths,
//! acknowledges ranges (cumulative, out of order, with gaps, reversed and past the largest sent number), fires the
//! loss and probe timers when they are due, flushes the flight, switches and follows paths (direct and relay),
//! puts the peer to sleep and the link down, and, in a few runs, waits past the ghost retention. After every call
//! the engine shows its state (`trace_view`): the ring slot by slot, the byte accounts, the round-trip estimate, the
//! probe timer, the paths and the reorder lens. The checkers replay each call with the operators of the model
//! (`RecoveryOps.tla`, `Vinc.TransportRecovery`) and require the state they compute, the events the call reported
//! and the error it returned to be the ones recorded. The tail repair tracker is traced on its own.
//!
//! The test asserts what it can itself (the accounts balance, a packet is reported at most once as acknowledged, lost
//! and late-acknowledged, never lost after it was acknowledged) so it is meaningful without the proof tools. Times are
//! nanoseconds below 2^31 (the checker has 32-bit integers). The trace is written to `VINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::collections::HashSet;
use std::fmt::Write as _;

use vinc_tests::SplitMix64;
use vinc_transport::recovery::trace::RecoveryView;
use vinc_transport::recovery::{
    Event, FrameRef, FrameRefs, Health, MS, PathKind, Recovery, RecoveryError, Sent, TailRepair,
};

const N: usize = 6;
const PATHS: u8 = 4;

fn b(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

fn opt(x: Option<u64>) -> i64 {
    x.map_or(-1, |v| i64::try_from(v).unwrap())
}

/// The largest value of a 32-bit checker integer: a timer value at or above it is shown as this one, which the
/// model's saturating arithmetic reaches in the same cases.
const TOP: u64 = (1 << 31) - 1;

fn opt_top(x: Option<u64>) -> i64 {
    opt(x.map(|v| v.min(TOP)))
}

fn err_name(e: Result<(), RecoveryError>) -> &'static str {
    match e {
        Ok(()) => "ok",
        Err(RecoveryError::PacketNumberOutOfRange) => "PacketNumberOutOfRange",
        Err(RecoveryError::AckOfUnsentPacket) => "AckOfUnsentPacket",
        Err(RecoveryError::InvalidAckRange) => "InvalidAckRange",
        Err(RecoveryError::PacketNumberNotIncreasing) => "PacketNumberNotIncreasing",
        Err(RecoveryError::RingFull) => "RingFull",
        Err(RecoveryError::PathOutOfRange) => "PathOutOfRange",
    }
}

/// Whether a ghost keeps the frame (stream data with bytes and no end).
fn is_data(f: &FrameRef) -> bool {
    matches!(f, FrameRef::Stream { len, fin: false, .. } if *len > 0)
}

fn bools(v: &[bool]) -> String {
    let s: Vec<&str> = v.iter().map(|x| b(*x)).collect();
    format!("[{}]", s.join(","))
}

fn view_json(v: &RecoveryView) -> String {
    let slots: Vec<String> = v
        .slots
        .iter()
        .map(|s| {
            format!(
                r#"{{"pn":{},"time":{},"size":{},"path":{},"rep":{},"probe":{},"fr":{},"st":{},"at":{}}}"#,
                s.pn,
                s.time,
                s.size,
                s.path,
                b(s.repair),
                b(s.probe),
                bools(&s.frames),
                s.state,
                s.lost_at
            )
        })
        .collect();
    let late: Vec<String> = v.late_sends.iter().map(|(p, t)| format!("[{p},{t}]")).collect();
    let reo: Vec<String> = v.reorder.iter().map(|(e, s)| format!("[{e},{}]", opt(*s))).collect();
    let prtt: Vec<String> = v.path_rtt.iter().map(ToString::to_string).collect();
    let (lat, sm, var, mn, has) = v.rtt;
    format!(
        r#"{{"ring":[{}],"ls":{},"la":{},"sent":{},"acked":{},"lost":{},"inf":{},"infp":{},"lt":{},"pc":{},"lp":{},"asleep":{},"down":{},"hrd":{},"clock":{},"tgr":{},"lrtt":{},"rtt":{{"lat":{},"sm":{sm},"var":{var},"mn":{},"has":{}}},"rel":{},"prtt":[{}],"act":{},"flip":{},"late":[{}],"saved":{},"reo":[{}],"gs":{},"lat":{},"nt":{}}}"#,
        slots.join(","),
        opt(v.largest_sent),
        opt(v.largest_acked),
        v.bytes[0],
        v.bytes[1],
        v.bytes[2],
        v.bytes[3],
        v.in_flight_packets,
        opt_top(v.loss_time),
        v.pto_count,
        v.last_pto,
        b(v.asleep),
        b(v.link_down),
        v.last_heard,
        v.clock,
        v.node_rtt[0],
        v.node_rtt[1],
        opt(lat),
        opt(mn),
        b(has),
        bools(&v.relay),
        prtt.join(","),
        v.active,
        opt(v.flip_at),
        late.join(","),
        opt(v.saved),
        reo.join(","),
        v.ghost_scan,
        v.largest_acked_time,
        opt_top(v.next_timeout)
    )
}

/// What the engine reported for one call.
#[derive(Default)]
struct Log {
    events: Vec<String>,
}

fn event_json(e: &Event<'_>, log: &mut Log, seen: &mut Seen) {
    match e {
        Event::Acked {
            pn,
            size,
            frames,
            mtu_probe,
            repair,
            ..
        } => {
            assert!(seen.acked.insert(*pn), "packet {pn} acknowledged twice");
            assert!(
                !seen.lost.contains(pn),
                "packet {pn} acknowledged after it was declared lost"
            );
            let fr: Vec<bool> = frames.iter().map(is_data).collect();
            log.events.push(format!(
                r#"["acked",{pn},{size},{},{},{}]"#,
                bools(&fr),
                b(*mtu_probe),
                b(*repair)
            ));
        }
        Event::LateAcked { pn, frames } => {
            assert!(seen.lost.contains(pn), "packet {pn} late-acknowledged but never lost");
            assert!(seen.late.insert(*pn), "packet {pn} late-acknowledged twice");
            let fr: Vec<bool> = frames.iter().map(is_data).collect();
            assert!(fr.iter().all(|x| *x), "a late acknowledgement acts on stream data only");
            log.events
                .push(format!(r#"["late",{pn},0,{},false,false]"#, bools(&fr)));
        }
        Event::Lost {
            pn,
            size,
            frames,
            requeue,
            mtu_probe,
        } => {
            assert!(seen.lost.insert(*pn), "packet {pn} declared lost twice");
            assert!(
                !seen.acked.contains(pn),
                "packet {pn} declared lost after it was acknowledged"
            );
            let fr: Vec<bool> = frames.iter().map(is_data).collect();
            log.events.push(format!(
                r#"["lost",{pn},{size},{},{},{}]"#,
                bools(&fr),
                b(*requeue),
                b(*mtu_probe)
            ));
        }
    }
}

#[derive(Default)]
struct Seen {
    acked: HashSet<u64>,
    lost: HashSet<u64>,
    late: HashSet<u64>,
}

struct Run<'o> {
    r: Recovery<N>,
    rng: SplitMix64,
    out: &'o mut String,
    id: u32,
    now: u64,
    seen: Seen,
    long_gap: bool,
}

impl Run<'_> {
    fn below(&mut self, n: u64) -> u64 {
        self.rng.next_u64() % n.max(1)
    }

    fn chance(&mut self, pct: u64) -> bool {
        self.below(100) < pct
    }

    /// Record an event with the view after it, and check what the test can check itself.
    fn log(&mut self, head: &str) {
        let v = self.r.trace_view();
        assert_eq!(
            v.bytes[0],
            v.bytes[1] + v.bytes[2] + v.bytes[3],
            "the accounts do not balance"
        );
        assert!(v.slots.len() <= N, "the ring overflowed");
        let run = self.id;
        let _ = writeln!(self.out, r#"{{"t":"rc","run":{run},{head},"v":{}}}"#, view_json(&v));
    }

    fn logged(&mut self, head: &str, log: &Log) {
        let evs = log.events.join(",");
        self.log(&format!(r#"{head},"evs":[{evs}]"#));
    }

    fn sum(s: &vinc_transport::recovery::Summary) -> String {
        format!(
            "[{},{},{},{},{}]",
            s.acked_packets, s.acked_bytes, s.late_acked_packets, s.lost_packets, s.lost_bytes
        )
    }

    fn advance(&mut self) {
        let d = [0, MS, 3 * MS, 10 * MS, 30 * MS, 80 * MS][self.below(6) as usize];
        self.now += d;
    }

    fn send(&mut self) {
        let pn = self.r.next_pn() + u64::from(self.chance(15));
        let mut frames = FrameRefs::new();
        for k in 0..self.below(4) {
            let f = match self.below(4) {
                0 => FrameRef::Stream {
                    id: 4,
                    offset: pn * 10 + k,
                    len: 100,
                    fin: false,
                },
                1 => FrameRef::Stream {
                    id: 4,
                    offset: pn * 10 + k,
                    len: 0,
                    fin: true,
                },
                2 => FrameRef::Stream {
                    id: 8,
                    offset: pn * 10 + k,
                    len: 50,
                    fin: true,
                },
                _ => FrameRef::Control { kind: 3, id: k },
            };
            frames.push(f).unwrap();
        }
        let path = if self.chance(4) {
            PATHS * 2
        } else {
            self.below(u64::from(PATHS)) as u8
        };
        let p = Sent {
            pn,
            time: self.now,
            size: 1200 + self.below(300) as u32,
            path,
            is_repair: self.chance(8),
            is_mtu_probe: self.chance(8),
            frames,
        };
        let e = self.r.on_packet_sent(p);
        let fr: Vec<bool> = p.frames.iter().map(is_data).collect();
        self.log(&format!(
            r#""op":"send","pn":{pn},"time":{},"size":{},"path":{path},"rep":{},"probe":{},"fr":{},"err":"{}""#,
            p.time,
            p.size,
            b(p.is_repair),
            b(p.is_mtu_probe),
            bools(&fr),
            err_name(e)
        ));
    }

    fn untracked(&mut self) {
        let pn = self.r.next_pn() + u64::from(self.chance(30));
        let pn = if self.chance(5) { pn.saturating_sub(1) } else { pn };
        let e = self.r.on_packet_untracked(pn);
        self.log(&format!(r#""op":"untracked","pn":{pn},"err":"{}""#, err_name(e)));
    }

    fn ack(&mut self) {
        let Some(ls) = self.r.largest_sent() else { return };
        let mut ranges: Vec<(u64, u64)> = Vec::new();
        match self.below(6) {
            0 => ranges.push((0, ls)),
            1 => {
                let lo = self.below(ls + 1);
                ranges.push((lo, ls));
            }
            2 => {
                let a = self.below(ls + 1);
                let z = a + self.below(ls + 1 - a);
                ranges.push((a, z));
            }
            3 => {
                let hi = self.below(ls + 1);
                let lo = self.below(hi + 1);
                ranges.push((hi, hi));
                ranges.push((lo, lo));
            }
            4 => {
                // a reversed range, or one past the largest sent number
                if self.chance(50) && ls > 0 {
                    ranges.push((ls, ls - 1));
                } else {
                    ranges.push((ls, ls + 1));
                }
            }
            _ => {
                let a = self.below(ls + 1);
                ranges.push((a, ls));
                if a > 1 {
                    ranges.push((0, a - 2));
                }
            }
        }
        let mut log = Log::default();
        let now = self.now;
        let inclusive: Vec<_> = ranges.iter().map(|&(a, z)| a..=z).collect();
        let res = {
            let seen = &mut self.seen;
            self.r
                .on_ack_received(now, inclusive, |e| event_json(&e, &mut log, seen))
        };
        let rgs: Vec<String> = ranges.iter().map(|(a, z)| format!("[{a},{z}]")).collect();
        let (s, e) = match res {
            Ok(s) => (s, "ok"),
            Err(e) => (vinc_transport::recovery::Summary::default(), err_name(Err(e))),
        };
        // the summary of a refused acknowledgement is not returned; the checker compares the events instead
        let sum = if e == "ok" { Self::sum(&s) } else { "[]".to_string() };
        self.logged(
            &format!(
                r#""op":"ack","now":{now},"rgs":[{}],"sum":{sum},"err":"{e}""#,
                rgs.join(",")
            ),
            &log,
        );
    }

    fn timeout(&mut self) {
        if let Some(t) = self.r.next_timeout()
            && !self.long_gap
            && t > self.now
            && t <= 700 * MS
            && self.chance(75)
        {
            self.now = t;
        }
        let mut log = Log::default();
        let now = self.now;
        let to = {
            let seen = &mut self.seen;
            self.r.on_timeout(now, |e| event_json(&e, &mut log, seen))
        };
        self.logged(
            &format!(
                r#""op":"timeout","now":{now},"sum":{},"ping":{}"#,
                Self::sum(&to.summary),
                b(to.ping)
            ),
            &log,
        );
    }

    fn flush(&mut self) {
        let mut log = Log::default();
        let now = self.now;
        let s = {
            let seen = &mut self.seen;
            self.r.flush_in_flight(now, |e| event_json(&e, &mut log, seen))
        };
        self.logged(&format!(r#""op":"flush","now":{now},"sum":{}"#, Self::sum(&s)), &log);
    }

    fn health(&mut self) {
        let now = self.now;
        let h = match self.r.health(now) {
            Health::Healthy => "Healthy",
            Health::Degraded => "Degraded",
            Health::Dead => "Dead",
        };
        self.log(&format!(r#""op":"health","now":{now},"h":"{h}""#));
    }

    fn config(&mut self) {
        match self.below(9) {
            0 => {
                let p = self.below(u64::from(PATHS) + 1) as u8;
                let relay = self.chance(50);
                let e = self
                    .r
                    .set_path_kind(p, if relay { PathKind::Relay } else { PathKind::Direct });
                self.log(&format!(
                    r#""op":"kind","path":{p},"relay":{},"err":"{}""#,
                    b(relay),
                    err_name(e)
                ));
            }
            1 => {
                let p = self.below(u64::from(PATHS) + 1) as u8;
                let r = self.r.switch_path(p);
                let (re, e) = match r {
                    Ok(x) => (x, "ok"),
                    Err(_) => (false, "PathOutOfRange"),
                };
                self.log(&format!(
                    r#""op":"switch","path":{p},"restarted":{},"err":"{e}""#,
                    b(re)
                ));
            }
            2 => {
                let p = self.below(u64::from(PATHS) + 1) as u8;
                let e = self.r.follow_path(p);
                self.log(&format!(r#""op":"follow","path":{p},"err":"{}""#, err_name(e)));
            }
            3 => {
                let a = self.chance(40);
                self.r.set_peer_asleep(a);
                self.log(&format!(r#""op":"asleep","b":{}"#, b(a)));
            }
            4 => {
                let a = self.chance(40);
                self.r.set_link_down(a);
                self.log(&format!(r#""op":"down","b":{}"#, b(a)));
            }
            5 => {
                self.r.note_peer_activity(self.now);
                self.log(&format!(r#""op":"activity","now":{}"#, self.now));
            }
            6 => {
                let x = [MS / 2, 2 * MS, 9 * MS, 40 * MS][self.below(4) as usize];
                self.r.seed_rtt(x);
                self.log(&format!(r#""op":"seed","x":{x}"#));
            }
            7 => {
                let x = [MS, 20 * MS, 270 * MS][self.below(3) as usize];
                self.r.set_node_rtt(x);
                self.log(&format!(r#""op":"node","x":{x}"#));
            }
            _ => {
                let x = [MS, 20 * MS, 270 * MS][self.below(3) as usize];
                self.r.set_handshake_rtt(x);
                self.log(&format!(r#""op":"hs","x":{x}"#));
            }
        }
    }

    fn step(&mut self) {
        self.advance();
        match self.below(100) {
            0..=34 => self.send(),
            35..=39 => self.untracked(),
            40..=64 => self.ack(),
            65..=79 => self.timeout(),
            80..=82 => self.flush(),
            83..=85 => self.health(),
            _ => self.config(),
        }
    }
}

fn run(seed: u64, out: &mut String, id: u32, long_gap: bool) {
    let mut r = Run {
        r: Recovery::<N>::new(1_350),
        rng: SplitMix64::traced(seed),
        out,
        id,
        now: 0,
        seen: Seen::default(),
        long_gap,
    };
    r.log(r#""op":"init""#);
    // The checker has 32-bit integers: a run ends before its clock gets near 2^31 ns.
    let end = if long_gap { 20 * MS } else { 600 * MS };
    for _ in 0..140 {
        r.step();
        if r.now > end {
            break;
        }
    }
    if r.long_gap {
        // Everything in flight is lost or acknowledged, then time passes beyond the ghost retention and a late
        // acknowledgement meets an expired ghost.
        r.flush();
        r.now += 2_005 * MS;
        let n = r.r.largest_sent().unwrap_or(0);
        let mut log = Log::default();
        let now = r.now;
        let inclusive = std::iter::once(0..=n);
        let res = {
            let seen = &mut r.seen;
            r.r.on_ack_received(now, inclusive, |e| event_json(&e, &mut log, seen))
        };
        let (s, e) = match res {
            Ok(s) => (Run::sum(&s), "ok"),
            Err(e) => ("[]".to_string(), err_name(Err(e))),
        };
        r.logged(
            &format!(r#""op":"ack","now":{now},"rgs":[[0,{n}]],"sum":{s},"err":"{e}""#),
            &log,
        );
    }
    r.log(r#""op":"end""#);
}

/// A flight that is never acknowledged: each probe timeout backs off until the path is reported degraded.
fn ladder(out: &mut String, id: u32) {
    let mut r = Run {
        r: Recovery::<N>::new(1_350),
        rng: SplitMix64::new(7),
        out,
        id,
        now: 0,
        seen: Seen::default(),
        long_gap: false,
    };
    r.log(r#""op":"init""#);
    r.r.seed_rtt(2 * MS);
    r.log(&format!(r#""op":"seed","x":{}"#, 2 * MS));
    for _ in 0..6 {
        r.send();
        r.now += MS;
    }
    for _ in 0..5 {
        r.now = r.r.next_timeout().unwrap();
        r.timeout();
        r.health();
    }
    r.log(r#""op":"end""#);
}

fn tail_runs(out: &mut String) {
    let mut rng = SplitMix64::traced(0x5441_494c);
    for id in 1..=6u32 {
        let mut t = TailRepair::new();
        let mut pn = 0u64;
        let _ = writeln!(out, r#"{{"t":"tr","run":{id},"op":"init"}}"#);
        for _ in 0..60 {
            if rng.next_u64().is_multiple_of(4) {
                let c = t.on_drain();
                let (burst, cand) = t.trace_view();
                let _ = writeln!(
                    out,
                    r#"{{"t":"tr","run":{id},"op":"drain","c":{},"burst":{burst},"cand":{}}}"#,
                    opt(c),
                    opt(cand)
                );
            } else {
                pn += 1 + rng.next_u64() % 2;
                let plain = !rng.next_u64().is_multiple_of(3);
                let inel = rng.next_u64().is_multiple_of(5);
                t.on_packet(pn, plain, inel);
                let (burst, cand) = t.trace_view();
                let _ = writeln!(
                    out,
                    r#"{{"t":"tr","run":{id},"op":"pkt","pn":{pn},"plain":{},"inel":{},"burst":{burst},"cand":{}}}"#,
                    b(plain),
                    b(inel),
                    opt(cand)
                );
            }
        }
    }
}

#[test]
fn recovery_runs_match_the_models() {
    let mut out = String::new();
    for run_id in 1..=240u32 {
        run(
            0x5245_434f_5645_0000 + u64::from(run_id),
            &mut out,
            run_id,
            run_id % 6 == 0,
        );
    }
    ladder(&mut out, 100);
    tail_runs(&mut out);
    for op in [
        "send",
        "untracked",
        "ack",
        "timeout",
        "flush",
        "health",
        "kind",
        "switch",
        "follow",
        "asleep",
        "down",
        "seed",
        "node",
        "hs",
        "activity",
    ] {
        assert!(out.contains(&format!(r#""op":"{op}""#)), "no {op} event");
    }
    // The runs reach the interesting steps: every error, a loss by the count rule and by a timer, a probe timeout, a
    // late acknowledgement, a repair packet lost, a full ring, a restored window.
    for needle in [
        r#""err":"RingFull""#,
        r#""err":"AckOfUnsentPacket""#,
        r#""err":"InvalidAckRange""#,
        r#""err":"PacketNumberNotIncreasing""#,
        r#""err":"PathOutOfRange""#,
        r#"["late","#,
        r#"["lost","#,
        r#""ping":true"#,
        r#""h":"Degraded""#,
    ] {
        assert!(
            vinc_tests::soaking() || out.contains(needle),
            "the runs never reach {needle}"
        );
    }
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("recovery.ndjson"), &out).unwrap();
    }
}
