//! Trace generation for the record's publish timer: a real `Connectivity` on the connect rig, driven call by call from
//! a node with no home to one whose home carrier is open and whose records are signed, recorded as ndjson
//! (`connect_own_timer.ndjson`) for the TLA+ trace check (`TraceConnectOwnTimer.tla`). One line per public call, with
//! the probe `trace_publish` read before and after it: `{op, now, w, ok, sent, before, after}`.
//!
//! The probe reads `next_publish` in milliseconds (the code's `None`, no time armed, as -1; a time of 0 is a time),
//! whether a record is wanted, a record job is outstanding, a wall clock is known, and whether a record can be asked
//! for now. The test keeps a plain reference of the rules (a record is asked for when the time is due, none is wanted
//! or outstanding and the home carrier is open, which disarms the timer; a change sets the time to now; the answer arms
//! the republish 1800 s on only when nothing armed it meanwhile, retries after 2 s when the signature failed, and
//! publishes at once when the carrier was gone; a tick with no wall clock keeps the one an earlier tick gave) and
//! requires every call's outcome to be one the reference allows. A class change while a record job is outstanding is in
//! the trace, and the answer keeps it. The clock moves in whole milliseconds. The trace is written to the directory in
//! `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_wrap,
    unreachable_pub
)]

mod connect_common;
mod connect_rig;

use std::fmt::Write as _;

use connect_common::{SEC, big_stack};
use connect_rig::{Ans, Custody, Rig};
use pinc_connect::client::{Io, PublishProbe};
use pinc_crypto::Software;
use pinc_security::{Env, KeyRequest, KeyResponse};
use pinc_tests::{Answer, Host};

const REPUB: i64 = 1_800_000;
const RETRY: i64 = 2_000;
const NONE: i64 = -1;

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

/// The part of the probe the rules act on, in milliseconds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct S {
    np: i64,
    want: bool,
    job: bool,
    wall: bool,
}

const NEW: S = S {
    np: NONE,
    want: false,
    job: false,
    wall: false,
};

fn publish(s: S, now: i64, can: bool) -> S {
    if s.np == NONE || now < s.np || s.want || s.job {
        s
    } else if can {
        S {
            want: true,
            np: NONE,
            ..s
        }
    } else {
        s
    }
}

fn changed(s: S, now: i64) -> S {
    S { np: now, ..s }
}

fn start(s: S, now: i64) -> Vec<S> {
    if s.job || !s.wall || !s.want {
        vec![s]
    } else {
        vec![
            S {
                want: false,
                job: true,
                ..s
            },
            S {
                want: false,
                np: now + RETRY,
                ..s
            },
        ]
    }
}

fn signed(s: S, now: i64, ok: bool, sent: bool) -> S {
    if !s.job {
        s
    } else if ok && sent {
        S {
            job: false,
            np: if s.np == NONE { now + REPUB } else { s.np },
            ..s
        }
    } else if ok {
        S {
            job: false,
            np: now,
            ..s
        }
    } else {
        S {
            job: false,
            np: now + RETRY,
            ..s
        }
    }
}

fn start_all(ss: &[S], now: i64) -> Vec<S> {
    ss.iter().flat_map(|s| start(*s, now)).collect()
}

#[allow(clippy::struct_excessive_bools, reason = "a trace record")]
struct Call<'a> {
    op: &'a str,
    now: i64,
    w: bool,
    ok: bool,
    sent: bool,
    can: bool,
}

/// Every state the reference allows after the call.
fn results(before: S, c: &Call<'_>) -> Vec<S> {
    let n = c.now;
    match c.op {
        "tick" => {
            let s0 = S {
                wall: before.wall || c.w,
                ..before
            };
            let ps: Vec<S> = [s0, changed(s0, n)].iter().map(|x| publish(*x, n, c.can)).collect();
            start_all(&ps, n)
        }
        "sign" => start(signed(before, n, c.ok, c.sent), n),
        "hints" => vec![S { want: true, ..before }],
        _ => {
            let base = [before, changed(before, n)];
            let mut v = base.to_vec();
            v.extend(start_all(&base, n));
            v.extend(start(before, n).into_iter().map(|x| changed(x, n)));
            v
        }
    }
}

struct Drv {
    rig: Box<Rig>,
    keys: Soft,
    out: String,
    last: S,
    can: bool,
}

impl Drv {
    fn read(&mut self) -> (S, bool, PublishProbe) {
        let p = self.rig.conn.trace_publish();
        let np = p.next_publish.map_or(NONE, |v| {
            assert!(
                v % 1_000_000 == 0 && v < u64::MAX,
                "the clock moves in whole milliseconds"
            );
            (v / 1_000_000) as i64
        });
        (
            S {
                np,
                want: p.want,
                job: p.job,
                wall: p.wall,
            },
            p.can,
            p,
        )
    }

    fn json(s: S, can: bool) -> String {
        format!(
            "{{\"np\":{},\"want\":{},\"job\":{},\"wall\":{},\"can\":{can}}}",
            s.np, s.want, s.job, s.wall
        )
    }

    /// Run one public call and record it.
    fn call(&mut self, op: &str, now: u64, w: bool, ok: bool, sent: bool, f: impl FnOnce(&mut Rig)) {
        let (before, bcan, _) = self.read();
        assert_eq!(before, self.last, "the state moved between two calls");
        f(&mut self.rig);
        let (after, can, _) = self.read();
        let c = Call {
            op,
            now: (now / 1_000_000) as i64,
            w,
            ok,
            sent,
            can,
        };
        assert!(
            results(before, &c).contains(&after),
            "{op} at {} ms: {before:?} -> {after:?} is no outcome of the rules",
            c.now
        );
        let _ = writeln!(
            self.out,
            "{{\"op\":\"{op}\",\"now\":{},\"w\":{w},\"ok\":{ok},\"sent\":{sent},\"before\":{},\"after\":{}}}",
            c.now,
            Self::json(before, bcan),
            Self::json(after, can)
        );
        self.last = after;
        self.can = can;
    }

    fn tick(&mut self, now: u64, wall: Option<u64>) {
        self.call("tick", now, wall.is_some(), false, false, |rig| {
            let Rig { conn, drbg, .. } = rig;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.tick(now, &mut env, wall);
        });
    }

    /// Answer the record job outstanding, with a good signature or a short one.
    fn sign(&mut self, now: u64, good: bool) {
        let sent = self.rig.conn.carrier_state(0) == pinc_connect::client::link::State::Open;
        let sig = {
            let req = self.rig.conn.sign_request().expect("a record job is outstanding");
            self.keys.answer(now, &req)
        };
        let Ans::Sig(sig) = sig else { panic!("a signature") };
        let sig = if good { sig } else { sig[..3].to_vec() };
        self.call("sign", now, false, good, good && sent, |rig| {
            rig.conn.sign_response(now, KeyResponse::Signature(&sig));
        });
    }

    fn other(&mut self, now: u64, f: impl FnOnce(&mut Rig)) {
        self.call("other", now, false, false, false, f);
    }

    /// Move the carrier bytes between the node and the relay, one recorded call at a time.
    fn pump(&mut self, now: u64) {
        for _ in 0..16 {
            let mut busy = false;
            while let Some(ans) = self.rig.conn.key_request(0).map(|r| self.keys.answer(now, &r)) {
                busy = true;
                self.other(now, |rig| {
                    let Rig { conn, drbg, .. } = rig;
                    let mut env = Env {
                        provider: &Software,
                        now,
                        drbg,
                    };
                    conn.key_response(now, &mut env, 0, ans.response());
                });
            }
            let mut out = vec![0u8; 32 * 1024];
            let mut n = 0;
            self.other(now, |rig| n = rig.conn.poll_stream(0, &mut out));
            if n > 0 {
                busy = true;
                let mut rest = &out[..n];
                while !rest.is_empty() {
                    let took = self.rig.rc.receive(rest);
                    rest = &rest[took..];
                    self.rig.relay_poll(now);
                    if took == 0 {
                        break;
                    }
                }
            }
            let mut back = vec![0u8; 32 * 1024];
            let m = self.rig.rc.transmit(&mut back);
            if m > 0 {
                busy = true;
                self.other(now, |rig| stream_data(rig, now, &back[..m]));
            }
            for rec in self.rig.sink.take() {
                if let connect_common::Rec::Carrier(_, plain) = rec {
                    busy = true;
                    let mut sealed = vec![0u8; 20 * 1024];
                    let k = self.rig.rc.seal_bytes(&Software, &plain, &mut sealed).unwrap();
                    self.other(now, |rig| stream_data(rig, now, &sealed[..k]));
                }
            }
            if !busy {
                break;
            }
        }
    }
}

fn stream_data(rig: &mut Rig, now: u64, bytes: &[u8]) {
    let Rig { conn, drbg, .. } = rig;
    let mut env = Env {
        provider: &Software,
        now,
        drbg,
    };
    conn.stream_data(now, &mut env, 0, bytes);
}

#[test]
fn the_publish_timer_follows_the_rules_from_no_home_to_a_signed_record() {
    big_stack(|| {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut drv = Drv {
            rig: Box::new(Rig::new(&identity, prekey)),
            keys: Soft(host),
            out: String::new(),
            last: NEW,
            can: false,
        };
        let mut now = 1000 * SEC;
        let wall = |now: u64| now / 1_000_000;

        // The relay answers the probe: the home is found.
        drv.other(now, |rig| {
            let Rig { conn, drbg, .. } = rig;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.probe_all(now, &mut env);
        });
        let mut buf = vec![0u8; 2048];
        let mut got = None;
        drv.other(now, |rig| got = rig.conn.poll_udp(&mut buf));
        let (to, n) = got.expect("a probe");
        drv.rig
            .relay
            .datagram(
                now,
                "198.51.100.5:20000".parse().unwrap(),
                None,
                &buf[..n],
                &mut drv.rig.sink,
            )
            .unwrap();
        let reply = drv
            .rig
            .sink
            .effects()
            .into_iter()
            .find_map(|r| {
                if let connect_common::Rec::Udp(_, b) = r {
                    Some(b)
                } else {
                    None
                }
            })
            .expect("the relay answers");
        drv.other(now, |rig| assert!(rig.conn.handle_udp(now, to, &reply)));

        // The home carrier opens, asked for by a tick that has no wall clock.
        drv.tick(now, None);
        let mut ios = Vec::new();
        loop {
            let mut io = None;
            drv.other(now, |rig| io = rig.conn.poll_io());
            let Some(io) = io else { break };
            ios.push(io);
        }
        assert!(
            ios.iter().any(|io| matches!(io, Io::Open { relay: 0, .. })),
            "the home carrier is asked for: {ios:?}, home {:?}",
            drv.rig.conn.home()
        );
        drv.other(now, |rig| {
            let Rig { conn, drbg, .. } = rig;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.stream_opened(now, &mut env, 0);
        });
        for _ in 0..8 {
            drv.pump(now);
        }
        assert!(drv.can, "the home carrier is open and the class is known");

        // A record is asked for, signed and taken: the republish is armed 1800 s on.
        now += SEC;
        drv.tick(now, Some(wall(now)));
        assert!(drv.last.job, "the carrier opening asks for a record");
        drv.sign(now, true);
        drv.pump(now);
        // A record whose signature is wrong retries after the period; one signed while the carrier is up is taken.
        for good in [true, false, true] {
            now += SEC;
            drv.call("hints", now, false, false, false, |rig| {
                assert!(rig.conn.set_hints(b"b"));
            });
            drv.tick(now, Some(wall(now)));
            assert!(drv.last.job, "a record wanted with a clock and a home is signed");
            drv.sign(now, good);
            if !good {
                assert_eq!(drv.last.np, now as i64 / 1_000_000 + RETRY);
            }
            drv.pump(now);
        }
        // The next record is asked for when its time comes.
        now = drv.last.np.cast_unsigned() * 1_000_000;
        drv.tick(now, Some(wall(now)));
        assert!(drv.last.job, "the republish asks for a record");
        // The class changes while the record job is outstanding: the answer keeps the change.
        assert_eq!(drv.last.np, NONE, "a record asked for disarms the timer");
        drv.other(now, |rig| rig.conn.set_local(&["198.51.100.5:20000".parse().unwrap()]));
        drv.tick(now, Some(wall(now)));
        assert_eq!(
            drv.last.np,
            now as i64 / 1_000_000,
            "the change is noted while the job is outstanding"
        );
        drv.sign(now, true);
        assert_eq!(drv.last.np, now as i64 / 1_000_000, "the answer keeps the change");
        drv.pump(now);

        // The carrier went away while the record was signed: it is asked for again as soon as the carrier opens.
        now += SEC;
        drv.call("hints", now, false, false, false, |rig| {
            assert!(rig.conn.set_hints(b"c"));
        });
        drv.tick(now, Some(wall(now)));
        assert!(drv.last.job);
        drv.other(now, |rig| rig.conn.stream_closed(now, 0));
        drv.sign(now, true);
        assert_eq!(drv.last.np, now as i64 / 1_000_000, "the record is asked for at once");

        assert!(drv.out.lines().count() > 40);
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("connect_own_timer.ndjson"), &drv.out).unwrap();
        }
    });
}

#[test]
fn a_tick_with_no_wall_clock_keeps_the_clock_an_earlier_tick_gave() {
    big_stack(|| {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut rig = Box::new(Rig::new(&identity, prekey));
        let tick = |rig: &mut Rig, now: u64, wall: Option<u64>| {
            let Rig { conn, drbg, .. } = rig;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.tick(now, &mut env, wall);
        };
        tick(&mut rig, 1000 * SEC, None);
        assert!(!rig.conn.trace_publish().wall);
        tick(&mut rig, 1000 * SEC, Some(1_000_000));
        assert!(rig.conn.trace_publish().wall);
        tick(&mut rig, 1001 * SEC, None);
        assert!(rig.conn.trace_publish().wall, "the clock an earlier tick gave is kept");
    });
}
