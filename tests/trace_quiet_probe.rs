//! Trace generation for the quiet-parent probe (`QUIET_PROBE`, #693): pairs of real endpoints (`pinc-core`, built with
//! the `trace` feature) run on the in-memory network of `CoreNet`, and every step of a probe is recorded as one ndjson
//! line (`core/quiet_probe.ndjson` under `PINC_TRACE_DIR`) for the TLA+ trace check (`TraceQuietProbe.tla`).
//!
//! The core records `TraceEvent::Probe` (the step, the dial's slot, the generation of the probed slot now and the one
//! the probe names, and the facts and outcome as bits); this test maps each dial's slot to its own number `w` (the
//! order of its `Connect`) and writes the lines: `start` (a new scenario), `dial` (every `Connect`, with the facts of
//! the session it would ride or probe, read before it chose, and whether it probed, failed or did neither), `cmd`
//! (every flight command sent, and whether the probing dial kept it), `stats`, `hear` (the settle gate saw a packet
//! on a probed session), `ride`, `lapse` (with whether it closed the probed session, the first address it flew to and
//! the commands applied), `fail` and `end`. A dial that reads no session carries no facts.
//!
//! The scenarios: a ride; a lapse that closes the quiet session; a lapse of a pulse session; a lapse with a write in
//! flight; a lapse after the probed session ended (another generation); two lapses that wait on one handshake; a
//! dial the application ends. Commands are kept on a ride as well as on a lapse. The test checks by itself that each
//! kind of line was seen.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    unreachable_pub
)]

use std::net::SocketAddr;

use pinc_core::{Answer, Command, Event, Query, Role, SessionId, TraceEvent, Value};
use pinc_tests::*;
use pinc_transport::stream::NoSource;

/// One `TraceEvent::Probe`: the step, the child slot, the generation now, the one the probe names, the bits.
type P = (u64, u64, u64, u64, u64);

/// A resolution waiting for the commands applied after it: the dial, the event, the facts, closed, first, applied.
type Pending<'a> = (u64, &'a str, String, bool, usize, Vec<&'a str>);

const FIRST: [&str; 4] = ["none", "caller", "learned", "wait"];
const CMD: [&str; 5] = ["", "paths", "resend", "hold", "unhold"];

/// The lines so far, the dial numbers and the probes still running.
#[derive(Default)]
struct Rec {
    out: String,
    dials: u64,
    /// The dial number of each child slot, and of each session id.
    slot_w: Vec<(u64, u64)>,
    sid_w: Vec<(SessionId, u64)>,
    probing: Vec<u64>,
}

fn facts((_, _, g, _, bits): P) -> String {
    format!(
        r#""gen":{g},"ours":{},"pulse":{},"heard":{},"infl":{}"#,
        bits & 64 != 0,
        bits & 1 != 0,
        bits & 2 != 0,
        bits & 4 != 0
    )
}

/// The probe records of node `a` since the last read.
fn read(net: &mut CoreNet, a: usize) -> Vec<P> {
    let mut v = Vec::new();
    while let Some(r) = net.nodes[a].ep.poll_trace() {
        if let TraceEvent::Probe {
            step,
            child,
            r#gen,
            of_gen,
            bits,
        } = r.event
        {
            v.push((step, child, r#gen, of_gen, bits));
        }
    }
    v
}

impl Rec {
    fn line(&mut self, s: &str) {
        self.out.push_str(s);
        self.out.push('\n');
    }

    fn start(&mut self) {
        self.line(r#"{"t":"qp","ev":"start","w":0}"#);
        *self = Self {
            out: std::mem::take(&mut self.out),
            ..Self::default()
        };
    }

    fn w_of(&self, child: u64) -> u64 {
        self.slot_w
            .iter()
            .rev()
            .find(|(c, _)| *c == child)
            .map_or(0, |(_, w)| *w)
    }

    fn w_of_session(&self, s: SessionId) -> u64 {
        self.sid_w.iter().find(|(x, _)| *x == s).map_or(0, |(_, w)| *w)
    }

    /// Write the lines of the steps a resolution made: the settle gate, a ride, a lapse (with the commands applied
    /// after it), a failed ride and an end.
    fn flush(&mut self, batch: &[P]) {
        let mut pending: Vec<Pending> = Vec::new();
        for p in batch {
            let w = self.w_of(p.1);
            match p.0 {
                1 => {
                    let f = facts(*p);
                    self.line(&format!(r#"{{"t":"qp","ev":"hear","w":0,{f}}}"#));
                }
                2 | 3 => {
                    pending.push((
                        w,
                        if p.0 == 2 { "ride" } else { "lapse" },
                        facts(*p),
                        p.4 & 8 != 0,
                        ((p.4 >> 4) & 3) as usize,
                        Vec::new(),
                    ));
                    self.probing.retain(|x| *x != w);
                }
                4 => {
                    let f = facts(*p);
                    self.line(&format!(r#"{{"t":"qp","ev":"fail","w":{w},{f}}}"#));
                    self.probing.retain(|x| *x != w);
                }
                6 => {
                    if let Some(q) = pending.iter_mut().rev().find(|q| q.0 == w) {
                        q.5.push(CMD[((p.4 >> 8) & 7) as usize]);
                    }
                }
                7 => {
                    self.line(&format!(r#"{{"t":"qp","ev":"end","w":{w}}}"#));
                    self.probing.retain(|x| *x != w);
                }
                _ => {}
            }
        }
        for (w, ev, f, closed, first, applied) in pending {
            let applied = applied.iter().map(|c| format!("\"{c}\"")).collect::<Vec<_>>().join(",");
            let extra = if ev == "lapse" {
                format!(r#","closed":{closed},"first":"{}""#, FIRST[first])
            } else {
                String::new()
            };
            self.line(&format!(
                r#"{{"t":"qp","ev":"{ev}","w":{w},{f}{extra},"applied":[{applied}]}}"#
            ));
        }
    }

    /// Read what the endpoint recorded and write the lines of any resolution in it.
    fn pump(&mut self, net: &mut CoreNet, a: usize) {
        let batch = read(net, a);
        self.flush(&batch);
    }

    /// Run for `span` or until `stop`, writing the resolutions that happen on the way.
    fn run(&mut self, net: &mut CoreNet, a: usize, span: u64, mut stop: impl FnMut(&mut CoreNet) -> bool) -> bool {
        let deadline = net.now + span;
        net.run(deadline, |n: &mut CoreNet| {
            self.pump(n, a);
            stop(n)
        })
    }

    /// `Connect` from `a` to `b`: the line of the dial, with the facts of the session it read.
    fn dial(&mut self, net: &mut CoreNet, a: usize, b: usize, alpn: &[u8]) -> Option<SessionId> {
        self.dials += 1;
        let w = self.dials;
        let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
        let rep = net.nodes[a].connect(now, peer, alpn, to, Role::Other);
        let batch = read(net, a);
        let read_of = batch.iter().find(|p| p.0 == 8).copied();
        let started = batch.iter().find(|p| p.0 == 0);
        let out = match (&rep, started) {
            (Err(_), _) => "fail",
            (Ok(_), Some(_)) => "probe",
            (Ok(_), None) => "other",
        };
        let f = read_of.map_or_else(String::new, |p| format!(",{}", facts(p)));
        self.line(&format!(
            r#"{{"t":"qp","ev":"dial","w":{w},"gave":true,"out":"{out}"{f}}}"#
        ));
        let sid = rep.as_ref().ok().map(|r| net.nodes[a].session(r));
        if let Some(p) = started {
            self.slot_w.push((p.1, w));
            self.probing.push(w);
        }
        if let Some(s) = sid {
            self.sid_w.push((s, w));
        }
        self.flush(&batch);
        sid
    }

    /// A flight command `c` to `session`: the line, with whether the probing dial kept it.
    fn cmd(&mut self, net: &mut CoreNet, a: usize, s: SessionId, command: Command<'_, NoSource>, c: &str) {
        let now = net.now;
        net.nodes[a].cmd(now, command).unwrap();
        let batch = read(net, a);
        let kept = batch.iter().any(|p| p.0 == 5);
        let w = self.w_of_session(s);
        self.line(&format!(r#"{{"t":"qp","ev":"cmd","w":{w},"c":"{c}","kept":{kept}}}"#));
        self.flush(&batch);
    }

    /// `Query::Stats` on `session`: what answered.
    fn stats(&mut self, net: &CoreNet, a: usize, s: SessionId) {
        let w = self.w_of_session(s);
        let ans = match net.nodes[a].ep.query(Query::Stats(s)) {
            Answer::Stats(st) if self.probing.contains(&w) => {
                assert!(!st.established, "a probing dial answered as established");
                "dial"
            }
            Answer::Stats(_) => "session",
            _ => "none",
        };
        self.line(&format!(r#"{{"t":"qp","ev":"stats","w":{w},"ans":"{ans}"}}"#));
    }
}

/// The three flight commands the connectivity client sends on a dial, one by one.
fn flight(rec: &mut Rec, net: &mut CoreNet, a: usize, s: SessionId, unhold: bool) {
    let x: SocketAddr = ([192, 0, 2, 77], 4433).into();
    rec.cmd(
        net,
        a,
        s,
        Command::FlightPaths {
            session: s,
            addrs: &[x],
            skip_primary: false,
        },
        "paths",
    );
    rec.cmd(net, a, s, Command::FirstResend { session: s, delay: 0 }, "resend");
    rec.cmd(net, a, s, Command::HoldFlight { session: s, hold: true }, "hold");
    if unhold {
        rec.cmd(
            net,
            a,
            s,
            Command::HoldFlight {
                session: s,
                hold: false,
            },
            "unhold",
        );
    }
}

fn connected(a: usize, s: SessionId) -> impl Fn(&mut CoreNet) -> bool {
    move |n| n.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == s))
}

fn drop_to(net: &mut CoreNet, b: usize) {
    let to = net.nodes[b].addr;
    net.loss = Some(Box::new(move |_, t, _| t == to));
}

#[test]
fn the_quiet_parent_probe_records_its_trace_for_the_model() {
    let out = big_stack(|| {
        let mut rec = Rec::default();
        // A ride: the peer answers the ping, commands are kept and applied to the ride.
        {
            rec.start();
            let (mut net, a, b) = silent_parent();
            let s = rec.dial(&mut net, a, b, ALPN_B).unwrap();
            flight(&mut rec, &mut net, a, s, false);
            rec.stats(&net, a, s);
            assert!(rec.run(&mut net, a, 3 * SEC_NS, connected(a, s)), "no ride");
            rec.stats(&net, a, s);
            rec.cmd(
                &mut net,
                a,
                s,
                Command::HoldFlight {
                    session: s,
                    hold: false,
                },
                "unhold",
            );
        }
        // A lapse that may close the quiet session, commands kept (a hold taken back) and applied to the handshake.
        {
            rec.start();
            let (mut net, a, b) = silent_parent();
            drop_to(&mut net, b);
            let s = rec.dial(&mut net, a, b, ALPN_B).unwrap();
            flight(&mut rec, &mut net, a, s, true);
            rec.stats(&net, a, s);
            rec.run(&mut net, a, 6 * SEC_NS, |_| false);
            // A second dial whose hold stays.
            let t = rec.dial(&mut net, a, b, ALPN_A).unwrap();
            flight(&mut rec, &mut net, a, t, false);
            rec.run(&mut net, a, 6 * SEC_NS, |_| false);
        }
        // A pulse session: its lapse never closes it.
        {
            rec.start();
            let (mut net, a, b) = silent_parent();
            let parent = net.nodes[a].ep.sessions().next().unwrap();
            let now = net.now;
            net.nodes[a]
                .cmd(
                    now,
                    Command::SetPulse {
                        session: parent,
                        on: true,
                    },
                )
                .unwrap();
            rec.run(&mut net, a, SEC_NS, |_| false);
            drop_to(&mut net, b);
            let s = rec.dial(&mut net, a, b, ALPN_B).unwrap();
            flight(&mut rec, &mut net, a, s, false);
            rec.run(&mut net, a, 6 * SEC_NS, |_| false);
        }
        // A write in flight on the quiet session: the lapse leaves it up.
        {
            rec.start();
            let (mut net, a, b, heard) = restarted_peer();
            net.run_for((heard + 21 * SEC_NS).saturating_sub(net.now));
            let parent = net.nodes[a].ep.sessions().next().unwrap();
            let s = rec.dial(&mut net, a, b, ALPN_B).unwrap();
            let now = net.now;
            let Value::Stream(id) = net.nodes[a]
                .cmd(
                    now,
                    Command::OpenStream {
                        session: parent,
                        bidi: false,
                    },
                )
                .unwrap()
                .value
            else {
                panic!()
            };
            net.nodes[a]
                .cmd(
                    now,
                    Command::Write {
                        session: parent,
                        stream: id,
                        data: b"payload",
                    },
                )
                .unwrap();
            flight(&mut rec, &mut net, a, s, false);
            rec.run(&mut net, a, 6 * SEC_NS, |_| false);
        }
        // The probed session ended during the window: the lapse sees another generation.
        {
            rec.start();
            let (mut net, a, b) = silent_parent();
            let parent = net.nodes[a].ep.sessions().next().unwrap();
            let s = rec.dial(&mut net, a, b, ALPN_B).unwrap();
            flight(&mut rec, &mut net, a, s, false);
            net.run_for(MS_NS);
            let now = net.now;
            net.nodes[a]
                .cmd(
                    now,
                    Command::Close {
                        session: parent,
                        error: 0,
                    },
                )
                .unwrap();
            rec.run(&mut net, a, 6 * SEC_NS, |_| false);
        }
        // Two dials for different protocols lapse together: the second waits on the first's handshake.
        {
            rec.start();
            let (mut net, a, b) = silent_parent();
            drop_to(&mut net, b);
            let one = rec.dial(&mut net, a, b, ALPN_B).unwrap();
            let two = rec.dial(&mut net, a, b, ALPN_A).unwrap();
            flight(&mut rec, &mut net, a, two, false);
            rec.run(&mut net, a, 6 * SEC_NS, |_| false);
            let _ = one;
        }
        // The application ends a dial while it probes.
        {
            rec.start();
            let (mut net, a, b) = silent_parent();
            drop_to(&mut net, b);
            let s = rec.dial(&mut net, a, b, ALPN_B).unwrap();
            flight(&mut rec, &mut net, a, s, false);
            let now = net.now;
            net.nodes[a].cmd(now, Command::Close { session: s, error: 0 }).unwrap();
            rec.pump(&mut net, a);
            rec.run(&mut net, a, SEC_NS, |_| false);
        }
        rec.out
    });
    let seen = |needles: &[&str]| out.lines().any(|l| needles.iter().all(|n| l.contains(n)));
    for (what, needles) in [
        ("a probe", &[r#""ev":"dial""#, r#""out":"probe""#][..]),
        ("a dial that did neither", &[r#""ev":"dial""#, r#""out":"other""#]),
        ("a packet heard on a probed session", &[r#""ev":"hear""#]),
        ("a ride", &[r#""ev":"ride""#]),
        (
            "a ride with commands applied",
            &[r#""ev":"ride""#, r#""applied":["paths""#],
        ),
        ("a lapse", &[r#""ev":"lapse""#]),
        ("a lapse that closed", &[r#""ev":"lapse""#, r#""closed":true"#]),
        ("a lapse that did not close", &[r#""ev":"lapse""#, r#""closed":false"#]),
        ("a lapse of a pulse session", &[r#""ev":"lapse""#, r#""pulse":true"#]),
        ("a lapse with a write in flight", &[r#""ev":"lapse""#, r#""infl":true"#]),
        ("a lapse of another generation", &[r#""ev":"lapse""#, r#""ours":false"#]),
        ("a lapse that waits", &[r#""ev":"lapse""#, r#""first":"wait""#]),
        (
            "a lapse that flew to the caller's address",
            &[r#""ev":"lapse""#, r#""first":"caller""#],
        ),
        (
            "a lapse with commands applied",
            &[r#""ev":"lapse""#, r#""applied":["#, r#""paths""#],
        ),
        ("a command kept", &[r#""ev":"cmd""#, r#""kept":true"#]),
        ("a command not kept", &[r#""ev":"cmd""#, r#""kept":false"#]),
        ("an unhold kept", &[r#""c":"unhold""#, r#""kept":true"#]),
        ("a stats of a dial", &[r#""ev":"stats""#, r#""ans":"dial""#]),
        ("a stats of a session", &[r#""ev":"stats""#, r#""ans":"session""#]),
        ("an end", &[r#""ev":"end""#]),
    ] {
        assert!(seen(needles), "no line of {what} was recorded");
    }
    eprintln!("quiet_probe: {} lines", out.lines().count());
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = format!("{dir}/core");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(format!("{dir}/quiet_probe.ndjson"), out).unwrap();
    }
}
