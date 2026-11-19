//! Trace generation for the signing work and the suspension of the client layer (`client/signing.rs`,
//! `client/timers.rs` suspend and resume, the beacon of `client/drive.rs`): the real `Connectivity` of the rig of
//! `connect_rig.rs` with its home carrier open, driven through its public API by ten fixed runs and 30 seeded ones,
//! and recorded as ndjson (`connect_sleep.ndjson`) for the TLA+ trace check (`TraceConnectSleep.tla`).
//!
//! After every call the test reads the signing job the layer waits on (a sleep notice, a record or a beacon), the
//! datagrams it queued (the sleep notices, the beacons), the `SignFailed` notices and the carrier closes it asked of
//! the host. On its own it asserts that a refused signature raises exactly one `SignFailed` and sends nothing, that
//! sleep notices go out in pairs and only when a notice was signed, and (in the fixed runs) that no close follows a
//! resume and that a suspension closes only after its notice was answered. Where the code differs from its
//! documentation (a second suspend, a notice behind a record job, a tick without a wall clock) the trace records what
//! the code does and the order is not asserted.
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
    clippy::if_same_then_else,
    clippy::manual_is_multiple_of
)]

mod connect_common;
mod connect_rig;

use core::net::SocketAddr;

use connect_common::{SEC, big_stack};
use connect_rig::{Ans, Custody, Rig};
use pinc_connect::client::link::State;
use pinc_connect::client::{Io, Notice};
use pinc_connect::local::{GROUP_V4, PORT};
use pinc_connect::record::Record;
use pinc_connect::relay::datagram::Datagram;
use pinc_connect::relay::sleep;
use pinc_crypto::Software;
use pinc_security::{Env, KeyRequest, KeyResponse};
use pinc_tests::{Answer, Host, SplitMix64};

/// One millisecond and one second, in the whole microseconds the events keep.
const MS: i64 = 1000;
const S: i64 = 1_000_000;
/// The clock of a call at `u64::MAX`.
const MAXC: i64 = i64::MAX;

struct Soft(Box<Host>);

impl Custody for Soft {
    fn answer(&mut self, now: u64, req: &KeyRequest<'_>) -> Ans {
        match self.0.answer(now, req) {
            Answer::Sig(b, n) => Ans::Sig(b[..n].to_vec()),
            Answer::Secret(s) => Ans::Secret(s),
            Answer::Failed => panic!("the software keys failed"),
        }
    }
}

/// How an answer to the signing request goes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// The custody's signature.
    Ok,
    /// A signature of the wrong length.
    Short,
    /// The host's key refused.
    Failed,
}

/// What a call left behind.
struct Snap {
    job: &'static str,
    jr: u8,
    udp: Vec<u8>,
    bcn: usize,
    fails: usize,
    closes: Vec<u8>,
}

/// A rig with its home carrier open and the record of a run.
struct Run {
    rig: Rig,
    keys: Soft,
    t0: u64,
    /// The clock of the last call, in microseconds after `t0` (or [`MAXC`]).
    d: i64,
    out: Vec<String>,
    alt: bool,
    /// The close of a suspension comes in a tick after its notice was answered.
    order: bool,
    /// No close follows a resume.
    strict: bool,
    resumed: bool,
    slept: bool,
}

impl Run {
    fn new(discovery: bool, fixed: bool) -> Self {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut keys = Soft(host);
        let mut rig = Rig::new(&identity, prekey);
        let mut answered = 0;
        let t0 = rig.bring_up(&mut keys, 1000 * SEC, &mut answered);
        for _ in 0..8 {
            rig.shuttle(&mut keys, t0, &mut answered);
        }
        rig.conn.set_local_discovery(discovery);
        for _ in 0..8 {
            let Some(ans) = rig.conn.sign_request().map(|r| keys.answer(t0, &r)) else {
                break;
            };
            rig.conn.sign_response(t0, ans.response());
        }
        assert_eq!(rig.conn.carrier_state(0), State::Open, "the home carrier is open");
        let mut run = Self {
            rig,
            keys,
            t0,
            d: 0,
            out: Vec::new(),
            alt: false,
            order: false,
            strict: fixed,
            resumed: false,
            slept: false,
        };
        // what bring-up left behind is not part of the run
        run.snap();
        run.out.push(r#"{"op":"init","job":"none","link":"open"}"#.to_owned());
        run
    }

    /// The clock of a call at `d`; a call at `u64::MAX` is made only while the carrier is not open.
    fn clock(&mut self, d: i64) -> u64 {
        self.d = d;
        if d == MAXC {
            assert_ne!(
                self.rig.conn.carrier_state(0),
                State::Open,
                "a call at u64::MAX on an open carrier"
            );
            return u64::MAX;
        }
        (self.t0 as i64 + d * 1000) as u64
    }

    /// The event's `now`: whole microseconds, or 2147483647 for `u64::MAX`.
    fn dj(d: i64) -> i64 {
        if d == MAXC { 2_147_483_647 } else { d }
    }

    /// The job the layer waits on: its name and whether it is owed to relay 1 (the notice, the home) or none.
    fn job_of(&self) -> (&'static str, u8) {
        match self.rig.conn.sign_request() {
            Some(KeyRequest::Sign { message, .. }) => {
                if message.starts_with(sleep::LABEL) {
                    ("sleep", 1)
                } else {
                    let mut b = message.to_vec();
                    b.extend_from_slice(&[0u8; 64]);
                    if Record::parse(&b).is_ok() {
                        ("record", 1)
                    } else {
                        ("beacon", 0)
                    }
                }
            }
            _ => ("none", 0),
        }
    }

    /// Read the state and drain the queues the way the host does.
    fn snap(&mut self) -> Snap {
        let (job, jr) = self.job_of();
        let group = SocketAddr::new(GROUP_V4.into(), PORT);
        let (mut udp, mut bcn) = (Vec::new(), 0);
        let mut buf = vec![0u8; 4096];
        while let Some((_, to, n)) = self.rig.conn.poll_udp_from(&mut buf) {
            if to == self.rig.udp && matches!(Datagram::decode(&buf[..n]), Ok(Datagram::Sleep { .. })) {
                udp.push(1);
            } else if to == group {
                bcn += 1;
            }
        }
        let mut fails = 0;
        while let Some(n) = self.rig.conn.poll_notice() {
            fails += usize::from(n == Notice::SignFailed);
        }
        let mut closes = Vec::new();
        while let Some(io) = self.rig.conn.poll_io() {
            if matches!(io, Io::Close { relay: 0 }) && closes.is_empty() {
                closes.push(1);
            }
        }
        Snap {
            job,
            jr,
            udp,
            bcn,
            fails,
            closes,
        }
    }

    /// Record the event after a call. `answer` is `(mode, the request was a sleep notice)` for an answer.
    fn emit(&mut self, op: &str, extra: &str, answer: Option<(Mode, bool)>) {
        let s = self.snap();
        assert_eq!(s.udp.len() % 2, 0, "sleep notices go out in pairs");
        if !s.udp.is_empty() {
            assert!(
                answer.is_some_and(|(m, sleep)| m == Mode::Ok && sleep),
                "a sleep notice went out other than by the signature of one"
            );
        }
        if let Some((Mode::Short | Mode::Failed, _)) = answer {
            assert_eq!(s.fails, 1, "a refused signature raises exactly one SignFailed");
            assert!(s.udp.is_empty(), "a refused signature sent a notice");
        }
        if !s.closes.is_empty() {
            if self.order {
                assert!(
                    op == "tick" && self.slept,
                    "the carriers closed in a {op} before the notice was answered"
                );
            }
            assert!(!(self.strict && self.resumed), "a close after a resume");
        }
        let link = match self.rig.conn.carrier_state(0) {
            State::Down => "down",
            State::Dialing => "dialing",
            State::Open => "open",
        };
        let list = |v: &[u8]| v.iter().map(u8::to_string).collect::<Vec<_>>().join(",");
        self.out.push(format!(
            r#"{{"op":"{op}",{extra}"job":"{}","jr":{},"link":"{link}","udp":[{}],"bcn":{},"fails":{},"closes":[{}]}}"#,
            s.job,
            s.jr,
            list(&s.udp),
            s.bcn,
            s.fails,
            list(&s.closes)
        ));
    }

    fn suspend(&mut self, d: i64) {
        let now = self.clock(d);
        self.rig.conn.suspend(now, now / 1_000_000);
        self.resumed = false;
        self.slept = false;
        self.emit("suspend", &format!(r#""now":{},"#, Self::dj(d)), None);
    }

    fn resume(&mut self, d: i64) {
        let now = self.clock(d);
        self.rig.conn.resume(now);
        self.resumed = true;
        self.emit("resume", &format!(r#""now":{},"#, Self::dj(d)), None);
    }

    fn tick(&mut self, d: i64, w: bool) {
        let now = self.clock(d);
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.rig.drbg,
        };
        self.rig.conn.tick(now, &mut env, w.then_some(now / 1_000_000));
        self.emit("tick", &format!(r#""now":{},"w":{w},"#, Self::dj(d)), None);
    }

    fn drive(&mut self, d: i64, w: bool) {
        let now = self.clock(d);
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.rig.drbg,
        };
        self.rig
            .conn
            .drive(now, &mut *self.keys.0.ep, &mut env, w.then_some(now / 1_000_000));
        self.emit("drive", &format!(r#""now":{},"w":{w},"#, Self::dj(d)), None);
    }

    /// Answer the request outstanding at the clock `d`; nothing happens when none is.
    fn answer_at(&mut self, d: i64, mode: Mode) {
        if self.rig.conn.sign_request().is_none() {
            return;
        }
        let now = self.clock(d);
        let (job, _) = self.job_of();
        let Some(ans) = self.rig.conn.sign_request().map(|r| self.keys.answer(now, &r)) else {
            return;
        };
        match mode {
            Mode::Ok => self.rig.conn.sign_response(now, ans.response()),
            Mode::Short => self.rig.conn.sign_response(now, KeyResponse::Signature(&[0u8; 10])),
            Mode::Failed => self.rig.conn.sign_response(now, KeyResponse::Failed),
        }
        let sleep = job == "sleep";
        self.slept |= sleep;
        self.emit(
            "answer",
            &format!(r#""now":{},"ok":{},"#, Self::dj(d), mode == Mode::Ok),
            Some((mode, sleep)),
        );
    }

    /// Answer at the clock of the last call.
    fn answer(&mut self, mode: Mode) {
        self.answer_at(self.d, mode);
    }

    /// Answer with the custody's signature while a request is outstanding (at most eight).
    fn answer_all(&mut self) {
        for _ in 0..8 {
            if self.rig.conn.sign_request().is_none() {
                break;
            }
            self.answer(Mode::Ok);
        }
    }

    fn want(&mut self) {
        let _ = self.rig.conn.set_hints(&[0x01, 0x02]);
        self.emit("want", "", None);
    }

    /// The network ended the carrier.
    fn link(&mut self, d: i64) {
        let now = self.clock(d);
        self.rig.conn.stream_closed(now, 0);
        self.emit("link", &format!(r#""now":{},"#, Self::dj(d)), None);
    }

    fn finish(self, out: &mut Vec<String>) {
        out.extend(self.out);
    }
}

fn fixed(order: bool, discovery: bool) -> Run {
    let mut r = Run::new(discovery, true);
    r.order = order;
    r
}

fn run1(out: &mut Vec<String>) {
    let mut r = fixed(true, false);
    r.suspend(MS);
    r.answer(Mode::Ok);
    r.tick(MS, true);
    r.tick(2 * MS, true);
    r.resume(3 * MS);
    r.tick(4 * MS, true);
    r.finish(out);
}

/// A refused signature of the notice (`mode` Short or Failed): the close comes anyway.
fn run_refused(out: &mut Vec<String>, mode: Mode) {
    let mut r = fixed(true, false);
    r.suspend(MS);
    r.answer(mode);
    r.tick(2 * MS, true);
    r.finish(out);
}

fn run4(out: &mut Vec<String>) {
    let mut r = fixed(true, false);
    r.want();
    r.tick(MS, true);
    r.suspend(MS);
    r.answer(Mode::Ok);
    r.answer(Mode::Ok);
    r.tick(3 * MS, true);
    r.finish(out);
}

fn run5(out: &mut Vec<String>) {
    let mut r = fixed(false, false);
    r.suspend(MS);
    r.resume(MS);
    r.tick(2 * MS, true);
    r.tick(3 * MS, true);
    r.finish(out);
}

/// A second suspend before the closing tick: recorded as the code does it.
fn run6(out: &mut Vec<String>) {
    let mut r = fixed(false, false);
    r.suspend(MS);
    r.answer(Mode::Ok);
    r.suspend(MS);
    r.tick(2 * MS, true);
    r.answer(Mode::Ok);
    r.finish(out);
}

/// A tick without a wall clock.
fn run7(out: &mut Vec<String>) {
    let mut r = fixed(false, false);
    r.want();
    r.tick(MS, false);
    r.answer(Mode::Ok);
    r.finish(out);
}

fn run8(out: &mut Vec<String>) {
    let mut r = fixed(false, false);
    r.suspend(5 * MS);
    r.answer_at(-200 * S, Mode::Ok);
    r.tick(-100 * S, true);
    r.tick(MAXC, true);
    r.suspend(MAXC);
    r.tick(MAXC, true);
    r.resume(10 * MS);
    r.tick(11 * MS, true);
    r.finish(out);
}

fn run9(out: &mut Vec<String>) {
    let mut r = fixed(false, false);
    r.link(MS);
    r.suspend(2 * MS);
    r.tick(3 * MS, true);
    r.resume(4 * MS);
    r.finish(out);
}

fn run10(out: &mut Vec<String>) {
    let mut r = fixed(false, true);
    r.drive(MS, true);
    r.answer(Mode::Ok);
    r.drive(2 * MS, false);
    r.drive(600 * MS, true);
    r.answer(Mode::Ok);
    r.suspend(601 * MS);
    r.answer_all();
    r.tick(602 * MS, true);
    r.finish(out);
}

/// One seeded run: 50 calls in a random order at a clock that steps, jumps back and forward, and stops at the end.
fn seeded(seed: u64, out: &mut Vec<String>) {
    let mut r = Run::new(seed % 2 == 1, false);
    let mut rng = SplitMix64::traced(0x51EE_0000 + seed);
    let mut linked = false;
    for _ in 0..50 {
        let pick = rng.next_u64() % 100;
        let d = if r.d == MAXC {
            MAXC
        } else if pick < 4 && r.rig.conn.carrier_state(0) != State::Open {
            MAXC
        } else if pick < 14 {
            (r.d - 100 * S).clamp(-500_000_000, 1_000_000_000)
        } else if pick < 19 {
            (r.d + 60 * S).clamp(-500_000_000, 1_000_000_000)
        } else {
            (r.d + MS).clamp(-500_000_000, 1_000_000_000)
        };
        // 0 suspend, 1 resume, 2 tick, 3 drive, 4 answer, 5 want, 6 link
        let mut ops = vec![0u8, 1, 2, 3, 5];
        if r.rig.conn.sign_request().is_some() {
            ops.push(4);
        }
        if !linked {
            ops.push(6);
        }
        let w = rng.next_u64() % 2 == 0;
        match ops[(rng.next_u64() % ops.len() as u64) as usize] {
            0 => r.suspend(d),
            1 => r.resume(d),
            2 => r.tick(d, w),
            3 => r.drive(d, w),
            4 => {
                let mode = if rng.next_u64() % 3 != 0 {
                    Mode::Ok
                } else {
                    r.alt = !r.alt;
                    if r.alt { Mode::Short } else { Mode::Failed }
                };
                r.answer_at(d, mode);
            }
            5 => r.want(),
            _ => {
                linked = true;
                r.link(d);
            }
        }
    }
    r.finish(out);
}

#[test]
fn connect_sleep_trace() {
    big_stack(|| {
        let mut out = Vec::new();
        run1(&mut out);
        run_refused(&mut out, Mode::Short);
        run_refused(&mut out, Mode::Failed);
        run4(&mut out);
        run5(&mut out);
        run6(&mut out);
        run7(&mut out);
        run8(&mut out);
        run9(&mut out);
        run10(&mut out);
        for seed in 0..30 {
            seeded(seed, &mut out);
        }
        assert!(out.len() > 1000, "the trace holds {} events", out.len());
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::write(format!("{dir}/connect_sleep.ndjson"), out.join("\n") + "\n").unwrap();
        }
    });
}
