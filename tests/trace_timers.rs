//! Trace generation for the timers and the closing state of the VINCER connection: scripted pairs of real connections
//! (`vinc-transport`, built with the `trace` feature) driven call by call, recorded as ndjson (`timers.ndjson`) for
//! the TLA+ trace check (`TraceTimers.tla`) and the Lean replay (`Vinc/TraceTimers.lean`).
//!
//! Two connections are connected over the in-memory link, then the test takes over: every datagram either side writes
//! goes to a pool, and the script decides which reaches the other side, when, again (a duplicate) or altered (it
//! does not authenticate), or never. Each call of the connection's API is one event with the time, what the call
//! returned, the lifecycle events it reported and the state of the timers right after it ([`TimerView`]: the
//! lifecycle fields and every deadline `poll_timeout` reads). The calls are `poll_timeout`, `handle_timeout` (at the
//! time `poll_timeout` named, just before it, and at other times), `poll_transmit`, `handle_datagram`, `close`, frames
//! injected that do not decode or break a rule, `sleep`, `wake`, `set_link_down`, `set_keepalive`, `pulse` and the
//! application's opens and writes. The scenarios: random runs with traffic, loss, duplicates, sleep and wake, link
//! outages, keepalives and closes; the idle timeout on both sides; a local close and its one CLOSE; a close whose
//! connection reaches a timer first; violations; a sleeping peer held 120 s; an unanswered WAKE; a link outage past
//! 30 s; a dial nobody answers, until its handshake gives up; a close while handshaking; sessions whose probes time
//! out with nothing coming back while the relay's carrier answers (`set_carrier_heard`), on a relay path with a fresh
//! carrier, which a 4th probe timeout closes with a CLOSE (with and without a round-trip sample: a lost first flight
//! leaves the handshake with none), and the near misses (3 probe timeouts, a carrier heard 6 s ago, a carrier never
//! open, a direct path, the peer heard just before). Each call carries what the recovery timer read for that rule
//! (`CarrierView`), and the test checks that the rule's own decision, taken from those reads in nanoseconds and in the
//! rounded microseconds the checkers take, is the same, that the close happened exactly then, and that every case above
//! was reached.
//!
//! Times are written in whole microseconds, rounded up (every time the test drives is a whole microsecond, so each
//! comparison with a deadline keeps its result, and the minimum `poll_timeout` takes commutes with the rounding); a
//! component deadline at or past the largest 32-bit checker integer is written as it (it is never the minimum: the
//! idle deadline is always below it).
//!
//! The test checks by itself what it can see from outside: at most one CLOSE leaves a connection, a closed connection
//! has no timer, writes nothing and refuses datagrams and opens, and the idle timeout and the unanswered WAKE are
//! reported at the time the constants say.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::fn_params_excessive_bools,
    clippy::panic,
    clippy::large_stack_arrays,
    clippy::needless_range_loop,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_crypto::IdentityAlg;
use vinc_security::ClientTickets;
use vinc_tests::*;
use vinc_transport::conn::{CarrierView, CloseReason, Drop, Event, IDLE_TIMEOUT, PathId, PathInfo, TimerView, code};
use vinc_transport::recovery::PathKind;
use vinc_wire::Writer;

/// The largest integer TLC holds.
const TOP: i64 = 2_147_483_647;

/// A lifecycle time in whole microseconds, rounded up.
fn us(t: u64) -> i64 {
    let v = i64::try_from(t.div_ceil(1000)).unwrap();
    assert!(v < TOP, "a lifecycle time past the checker's integers: {t}");
    v
}

fn ous(t: Option<u64>) -> i64 {
    t.map_or(-1, us)
}

/// A component deadline in whole microseconds, rounded up, and held at `TOP`.
fn cus(t: Option<u64>) -> i64 {
    t.map_or(-1, |t| i64::try_from(t.div_ceil(1000)).unwrap_or(TOP).min(TOP))
}

/// The recovery timer's reads of a `handle_timeout` call for the carrier rule, as the checkers take them: times in whole
/// microseconds (the carrier's and the peer's are whole already; the smoothed and node round trips are rounded up), and
/// the call's own probe timeout and dead path. A call whose recovery timer did not run reads nothing.
fn probe_json(p: Option<&CarrierView>) -> String {
    let Some(p) = p else {
        return r#","pr":{"ping":false,"dead":false,"relay":false,"ch":-1,"pto":0,"lh":0,"smp":true,"sr":1,"nd":0}"#
            .into();
    };
    assert!(
        p.carrier.is_none_or(|c| c % 1000 == 0) && p.heard % 1000 == 0,
        "a carrier or peer time off the microsecond"
    );
    format!(
        r#","pr":{{"ping":{},"dead":{},"relay":{},"ch":{},"pto":{},"lh":{},"smp":{},"sr":{},"nd":{}}}"#,
        p.ping,
        p.dead,
        p.relay,
        ous(p.carrier),
        p.ptos,
        us(p.heard),
        p.sampled,
        us(p.srtt),
        us(p.node)
    )
}

/// What `dead_behind_live_carrier` decides, from the read times in nanoseconds, and the same from the rounded ones the
/// checkers take: both must agree at the call's time.
fn carrier_decision(p: &CarrierView, now: u64) -> bool {
    let rtt = if p.sampled { p.srtt } else { (333 * MS).max(p.node * 2) };
    let exact = p.relay
        && p.carrier.is_some_and(|h| now.saturating_sub(h) < 6 * SEC)
        && p.ptos >= 4
        && now.saturating_sub(p.heard) >= rtt * 4;
    let (nowu, rttu) = (
        now.div_ceil(1000),
        if p.sampled {
            p.srtt
        } else {
            (333 * MS).max(p.node.div_ceil(1000) * 2000)
        }
        .div_ceil(1000),
    );
    let rounded = p.relay
        && p.carrier.is_some_and(|h| nowu.saturating_sub(h / 1000) < 6_000_000)
        && p.ptos >= 4
        && nowu.saturating_sub(p.heard / 1000) >= rttu * 4;
    assert_eq!(
        exact, rounded,
        "rounding to microseconds changed the carrier rule at {now}: {p:?}"
    );
    exact
}

fn view_json(v: &TimerView) -> String {
    let ph = ["hs", "conn", "closing", "closed"][usize::from(v.phase)];
    format!(
        r#"{{"ph":"{ph}","close":{},"keys":{},"act":{},"sent":{},"ka":{},"pa":{},"la":{},"stx":{},"wd":{},"ld":{},"idle":{},"conf":{},"hs":{},"rekey":{},"rec":{},"ack":{},"amp":{},"paced":{},"path":{},"mtu":{}}}"#,
        v.close.map_or(-1, |c| i64::try_from(c).unwrap()),
        v.send_keys,
        us(v.last_activity),
        us(v.last_sent),
        ous(v.keepalive),
        ous(v.peer_asleep),
        v.local_asleep,
        v.sleep_tx,
        ous(v.wake_deadline),
        ous(v.link_down),
        us(v.idle),
        v.confirmed,
        cus(v.hs),
        cus(v.rekey),
        cus(v.rec),
        cus(v.ack),
        v.amp_ok,
        cus(v.paced),
        cus(v.path),
        cus(v.mtu)
    )
}

/// The ndjson being written and what the test counts by itself.
struct Log {
    out: String,
    run: u32,
    /// CLOSE packets that left each node of the run (a datagram written while closing).
    closes: [u32; 2],
    /// Events of each kind seen over all runs, to show the scenarios reach them.
    seen: std::collections::BTreeMap<&'static str, usize>,
}

impl Log {
    /// One event: the call `op` of node `n` at `now`, with `extra` (`,"k":v` pairs), the lifecycle events the
    /// connection reports after it and its timers.
    fn line(&mut self, n: usize, node: &mut Node<'_>, now: u64, op: &str, extra: &str) -> Vec<&'static str> {
        let v = node.conn.trace_timers();
        let mut ev = Vec::new();
        while let Some(e) = node.conn.poll_event() {
            ev.push(match e {
                Event::Closed(r) => match r {
                    CloseReason::Local { .. } => "local",
                    CloseReason::Peer { .. } => "peer",
                    CloseReason::Violation { .. } => "viol",
                    CloseReason::IdleTimeout => "idle",
                    CloseReason::PathDead => "dead",
                    CloseReason::HandshakeTimeout | CloseReason::Unanswered | CloseReason::Unconfirmed => "hs",
                    CloseReason::Handshake(f) => panic!("the handshake failed: {f:?}"),
                },
                Event::PeerAsleep => "asleep",
                Event::PeerAwake => "awake",
                Event::WakeUnanswered => "unanswered",
                Event::Connected { .. } => "connected",
                _ => continue,
            });
        }
        for e in &ev {
            *self.seen.entry(e).or_default() += 1;
        }
        *self.seen.entry(leak(op)).or_default() += 1;
        let evs: Vec<String> = ev.iter().map(|e| format!("\"{e}\"")).collect();
        let name = if n == 0 { "a" } else { "b" };
        let _ = writeln!(
            self.out,
            r#"{{"t":"tmr","run":{},"n":"{name}","op":"{op}","now":{}{extra},"ev":[{}],"v":{}}}"#,
            self.run,
            us(now),
            evs.join(","),
            view_json(&v)
        );
        ev
    }
}

fn leak(op: &str) -> &'static str {
    match op {
        "init" => "init",
        "poll" => "poll",
        "timeout" => "timeout",
        "tx" => "tx",
        "recv" => "recv",
        "inject" => "inject",
        "close" => "close",
        "sleep" => "sleep",
        "wake" => "wake",
        "link" => "link",
        "keepalive" => "keepalive",
        "pulse" => "pulse",
        _ => "app",
    }
}

/// How a pool datagram is handed over.
#[derive(Clone, Copy, PartialEq, Eq)]
enum How {
    Fresh,
    Again,
    Altered,
}

/// Two connected nodes, the datagrams they wrote, and the time.
struct Duo<'a, 'b> {
    nodes: [Node<'a>; 2],
    stores: &'b mut Stores,
    now: u64,
    /// `(from, bytes, delivered)`.
    pool: Vec<(usize, Vec<u8>, bool)>,
    buf: Vec<u8>,
}

/// One node's calls, written to the log.
fn init(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64) {
    log.line(n, node, now, "init", "");
}

fn poll(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64) -> Option<u64> {
    let t = node.conn.poll_timeout();
    let out = t.map_or(-1, |t| i64::try_from(t.div_ceil(1000)).unwrap());
    log.line(n, node, now, "poll", &format!(r#","out":{out}"#));
    if node.conn.is_closed() && !node.conn.is_connected() && t.is_some() {
        assert_eq!(t, Some(0), "a closing connection runs its timer at once");
    }
    t
}

fn timeout(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64) -> Vec<&'static str> {
    node.with_env(now, Conn::handle_timeout);
    let probe = node.conn.trace_carrier_take();
    let extra = probe_json(probe.as_ref());
    let ev = log.line(n, node, now, "timeout", &extra);
    if let Some(p) = probe.filter(|p| p.ping && !p.dead) {
        let (close, v) = (carrier_decision(&p, now), node.conn.trace_timers());
        let fresh = p.carrier.is_some_and(|h| now.saturating_sub(h) < 6 * SEC);
        let rtt = if p.sampled { p.srtt } else { (333 * MS).max(p.node * 2) };
        let silent = now.saturating_sub(p.heard) >= rtt * 4;
        let seen = &mut log.seen;
        let mut note = |k: &'static str| *seen.entry(k).or_default() += 1;
        if close {
            assert!(
                ev.contains(&"dead") && v.close == Some(0),
                "no close behind a live carrier: {p:?}"
            );
            note("carrier_close");
            note(if p.sampled {
                "carrier_close_sampled"
            } else {
                "carrier_close_unsampled"
            });
        } else if p.relay {
            assert!(
                !ev.contains(&"dead"),
                "a close behind a carrier outside the rule: {p:?}"
            );
            if fresh && silent && p.ptos < 4 {
                note("near_pto3");
            }
            if p.carrier.is_some() && !fresh && silent && p.ptos >= 4 {
                note("near_stale");
            }
            if p.carrier.is_none() && silent && p.ptos >= 4 {
                note("near_nocarrier");
            }
            if fresh && !silent && p.ptos >= 4 {
                note(if p.sampled {
                    "near_heard_sampled"
                } else {
                    "near_heard_unsampled"
                });
            }
        } else if fresh && silent && p.ptos >= 4 {
            note("near_direct");
        }
    }
    ev
}

fn close(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64, err: u64) {
    node.with_env(now, |c, env| c.close(env, err));
    log.line(n, node, now, "close", &format!(r#","err":{err}"#));
}

fn simple(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64, op: &str, arg: u64) {
    let extra = match op {
        "sleep" => {
            node.with_env(now, Conn::sleep);
            String::new()
        }
        "wake" => {
            node.with_env(now, Conn::wake);
            String::new()
        }
        "link" => {
            let down = arg != 0;
            node.with_env(now, |c, env| c.set_link_down(env, down));
            format!(r#","down":{down}"#)
        }
        "keepalive" => {
            let ka = (arg != 0).then_some(arg);
            node.conn.set_keepalive(ka);
            format!(r#","ka":{}"#, ous(ka))
        }
        "pulse" => {
            let sent = arg != 0;
            node.conn.pulse(now, sent);
            format!(r#","sent":{sent}"#)
        }
        _ => unreachable!(),
    };
    log.line(n, node, now, op, &extra);
}

/// The application opens a stream and writes `len` bytes on it.
fn app(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64, len: usize) {
    let r = node.conn.open_bi().and_then(|id| node.conn.write(id, &vec![0x5a; len]));
    let ok = r.is_ok();
    if node.conn.is_closed() {
        assert!(!ok, "a closed connection took application data");
    }
    log.line(n, node, now, "app", &format!(r#","ok":{ok}"#));
}

/// Frames injected as an authenticated packet: `bad` ones do not decode, the others acknowledge a packet that was
/// never sent.
fn inject(log: &mut Log, n: usize, node: &mut Node<'_>, now: u64, path: PathId, bad: bool) {
    assert!(!node.conn.is_closed());
    let mut buf = [0u8; 64];
    let len = if bad {
        buf[0] = 0x06;
        1
    } else {
        let mut w = Writer::new(&mut buf);
        vinc_transport::frame::write_ack(&mut w, core::iter::once(1_000_000u64..=1_000_000)).unwrap();
        w.written().len()
    };
    let _ = node.with_env(now, |c, env| c.inject_payload(env, path, now, 1 << 40, &buf[..len]));
    let (kind, err) = if bad {
        ("bad", code::FRAME_ENCODING)
    } else {
        ("viol", code::PROTOCOL_VIOLATION)
    };
    log.line(n, node, now, "inject", &format!(r#","kind":"{kind}","err":{err}"#));
}

impl Duo<'_, '_> {
    fn init(&mut self, log: &mut Log) {
        for n in 0..2 {
            init(log, n, &mut self.nodes[n], self.now);
        }
    }

    fn poll(&mut self, log: &mut Log, n: usize) -> Option<u64> {
        poll(log, n, &mut self.nodes[n], self.now)
    }

    fn timeout(&mut self, log: &mut Log, n: usize) -> Vec<&'static str> {
        timeout(log, n, &mut self.nodes[n], self.now)
    }

    /// `poll_transmit` until it has nothing; every call is an event. Returns the datagrams written.
    fn tx(&mut self, log: &mut Log, n: usize) -> usize {
        let mut made = 0;
        for _ in 0..64 {
            let now = self.now;
            let phase = self.nodes[n].conn.trace_timers().phase;
            let (closing, was_closed) = (phase == 2, phase == 3);
            let buf = &mut self.buf;
            let r = self.nodes[n].with_env(now, |c, env| c.poll_transmit(env, buf));
            let len = r.map_or(0, |t| t.len);
            log.line(n, &mut self.nodes[n], now, "tx", &format!(r#","len":{len}"#));
            let Some(t) = r else { break };
            assert!(!was_closed, "a closed connection wrote a datagram");
            if closing {
                log.closes[n] += 1;
                assert!(log.closes[n] <= 1, "a second CLOSE left");
            }
            for seg in self.buf[..t.len].chunks(t.segment_size) {
                self.pool.push((n, seg.to_vec(), false));
                made += 1;
            }
        }
        made
    }

    /// Hand pool datagram `i` to the other node.
    fn deliver(&mut self, log: &mut Log, i: usize, how: How) {
        let (from, mut bytes, _) = self.pool[i].clone();
        self.pool[i].2 = true;
        if how == How::Altered {
            let last = bytes.len() - 1;
            bytes[last] ^= 0x40;
        }
        let to = 1 - from;
        let now = self.now;
        let was_closed = self.nodes[to].conn.is_closed();
        let r = if to == 0 {
            self.nodes[0].with_env(now, |c, env| c.handle_datagram(env, PathId(1), &mut bytes))
        } else {
            let stores = &mut *self.stores;
            self.nodes[1].with_env(now, |c, env| c.handle_datagram_with(env, stores, PathId(2), &mut bytes))
        };
        let res = match r {
            Ok(()) => "ok",
            Err(Drop::Duplicate) => "dup",
            Err(Drop::Undecryptable) => "undecryptable",
            Err(Drop::Closed) => "closed",
            Err(Drop::Unroutable) => "unroutable",
            Err(e) => panic!("an unexpected refusal {e:?}"),
        };
        if was_closed {
            assert_eq!(res, "closed", "a closed connection took a datagram");
        }
        if how == How::Altered {
            assert!(res != "ok", "an altered datagram was taken");
        }
        log.line(to, &mut self.nodes[to], now, "recv", &format!(r#","res":"{res}""#));
    }

    /// Hand every waiting datagram over, in order.
    fn deliver_all(&mut self, log: &mut Log) {
        for i in 0..self.pool.len() {
            if !self.pool[i].2 {
                self.deliver(log, i, How::Fresh);
            }
        }
    }

    /// Lose every waiting datagram.
    fn lose_all(&mut self) {
        for d in &mut self.pool {
            d.2 = true;
        }
    }

    /// Both sides write, every datagram arrives, until quiet (a few rounds).
    fn exchange(&mut self, log: &mut Log) {
        for _ in 0..6 {
            let m = self.tx(log, 0) + self.tx(log, 1);
            self.deliver_all(log);
            if m == 0 {
                break;
            }
        }
    }

    /// The earliest timer of the open nodes.
    fn next_deadline(&self) -> Option<u64> {
        self.nodes.iter().filter_map(|x| x.conn.poll_timeout()).min()
    }

    /// Move to the next deadline (rounded up to a microsecond, never back), and run the timers that are due.
    fn advance_to_next(&mut self, log: &mut Log) -> bool {
        let Some(t) = self.next_deadline() else { return false };
        self.now = self.now.max(t.div_ceil(1000) * 1000);
        self.fire(log);
        true
    }

    /// Poll both nodes and run the timers that are due.
    fn fire(&mut self, log: &mut Log) {
        for n in 0..2 {
            if self.poll(log, n).is_some_and(|t| t <= self.now) {
                self.timeout(log, n);
            }
        }
    }
}

/// Connect two nodes over the in-memory link, then hand them to `f` as a scripted pair.
fn with_pair(seed: u64, thin: bool, f: impl FnOnce(&mut Duo<'_, '_>)) {
    with_pair_at(seed, thin, false, f);
}

/// As [`with_pair`]; with `resent` the first flight of the dial is lost and its resend answered, so the handshake
/// measures no round trip and the connection has no round-trip sample.
fn with_pair_at(seed: u64, thin: bool, resent: bool, f: impl FnOnce(&mut Duo<'_, '_>)) {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.thin = thin;
    w.seed = seed as u8;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    if resent {
        net.link.route(PathId(1)).up = false;
        net.run(net.now + SEC, |_| false);
        net.link.route(PathId(1)).up = true;
    }
    assert!(net.connect(net.now + 30 * SEC));
    if !resent {
        net.run(net.now + 100 * MS, |_| false);
    }
    let Net { a, b, stores, now, .. } = net;
    let mut d = Duo {
        nodes: [a, b],
        stores,
        now: now.div_ceil(MS) * MS,
        pool: Vec::new(),
        buf: vec![0u8; 65_536],
    };
    for x in &mut d.nodes {
        while x.conn.poll_event().is_some() {}
    }
    f(&mut d);
}

/// Random calls on a connected pair.
fn random_run(log: &mut Log, seed: u64, steps: usize) {
    with_pair(seed, seed.is_multiple_of(3), |d| {
        let mut rng = SplitMix64::new(seed ^ 0x7469_6d65);
        d.init(log);
        for _ in 0..steps {
            if d.nodes.iter().all(|x| x.conn.is_closed()) && rng.next_u64().is_multiple_of(8) {
                break;
            }
            let n = (rng.next_u64() % 2) as usize;
            match rng.next_u64() % 24 {
                0..=4 => {
                    // time moves on
                    let dt = [MS, 20 * MS, 300 * MS, SEC, 5 * SEC, 20 * SEC, 45 * SEC][(rng.next_u64() % 7) as usize];
                    match rng.next_u64() % 4 {
                        0 => {
                            d.advance_to_next(log);
                        }
                        1 => {
                            // just before the next deadline: nothing of the lifecycle may happen there
                            if let Some(t) = d.next_deadline() {
                                let t = t.div_ceil(1000) * 1000;
                                if t > d.now + 1000 {
                                    d.now = t - 1000;
                                    for m in 0..2 {
                                        d.poll(log, m);
                                        d.timeout(log, m);
                                    }
                                }
                            }
                        }
                        _ => {
                            d.now += dt;
                            d.fire(log);
                        }
                    }
                }
                5..=6 => {
                    d.poll(log, n);
                    d.timeout(log, n);
                }
                7..=9 => {
                    d.tx(log, n);
                }
                10..=13 => {
                    let waiting: Vec<usize> = (0..d.pool.len()).filter(|i| !d.pool[*i].2).collect();
                    if !waiting.is_empty() {
                        let i = waiting[(rng.next_u64() % waiting.len().min(3) as u64) as usize];
                        match rng.next_u64() % 10 {
                            0 => d.pool[i].2 = true,
                            1 => d.deliver(log, i, How::Altered),
                            _ => d.deliver(log, i, How::Fresh),
                        }
                    } else if !d.pool.is_empty() {
                        let i = (rng.next_u64() % d.pool.len() as u64) as usize;
                        d.deliver(log, i, How::Again);
                    }
                }
                14..=15 => {
                    let len = [10, 1000, 30_000][(rng.next_u64() % 3) as usize];
                    app(log, n, &mut d.nodes[n], d.now, len);
                }
                16 => {
                    let op = if d.nodes[n].conn.asleep() { "wake" } else { "sleep" };
                    simple(log, n, &mut d.nodes[n], d.now, op, 0);
                }
                17 => {
                    let down = u64::from(rng.next_u64().is_multiple_of(2));
                    simple(log, n, &mut d.nodes[n], d.now, "link", down);
                }
                18 => {
                    let ka = [0, 5 * SEC, 20 * SEC][(rng.next_u64() % 3) as usize];
                    simple(log, n, &mut d.nodes[n], d.now, "keepalive", ka);
                }
                19 => {
                    let sent = rng.next_u64() % 2;
                    simple(log, n, &mut d.nodes[n], d.now, "pulse", sent);
                }
                20 => {
                    if rng.next_u64().is_multiple_of(12) {
                        close(log, n, &mut d.nodes[n], d.now, rng.next_u64() % 0x50);
                    }
                }
                21 => {
                    if rng.next_u64().is_multiple_of(16) && !d.nodes[n].conn.is_closed() {
                        let path = PathId(if n == 0 { 1 } else { 2 });
                        inject(log, n, &mut d.nodes[n], d.now, path, rng.next_u64().is_multiple_of(2));
                    }
                }
                _ => {
                    d.exchange(log);
                }
            }
        }
    });
}

/// Nothing is heard: both sides close for idleness at the first timer call at or after 75 s of silence, and not a
/// microsecond earlier.
fn idle_run(log: &mut Log, seed: u64) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        d.lose_all();
        for n in 0..2 {
            let idle = d.nodes[n].conn.trace_timers().idle;
            assert_eq!(idle, d.nodes[n].conn.trace_timers().last_activity + IDLE_TIMEOUT);
        }
        let mut closed = [false; 2];
        for _ in 0..400 {
            // the recovery timers fire meanwhile; their probes are lost
            if !d.advance_to_next(log) {
                break;
            }
            for n in 0..2 {
                d.tx(log, n);
            }
            d.lose_all();
            for n in 0..2 {
                let v = d.nodes[n].conn.trace_timers();
                if v.phase == 1 && d.now.div_ceil(1000) * 1000 + 1000 <= v.idle && v.idle < d.now + SEC {
                    // just before the deadline: nothing
                    let at = v.idle.div_ceil(1000) * 1000 - 1000;
                    if at >= d.now {
                        d.now = at;
                        let ev = d.timeout(log, n);
                        assert!(!ev.contains(&"idle"), "closed for idleness before the deadline");
                    }
                }
            }
            for n in 0..2 {
                if !closed[n] && d.nodes[n].conn.is_closed() {
                    closed[n] = true;
                }
            }
            if closed.iter().all(|c| *c) {
                break;
            }
        }
        assert!(closed.iter().all(|c| *c), "an idle connection stayed open");
        // closed: no timer, nothing written, nothing taken
        for n in 0..2 {
            assert!(d.poll(log, n).is_none());
            assert_eq!(d.tx(log, n), 0);
            app(log, n, &mut d.nodes[n], d.now, 10);
        }
    });
}

/// A local close: one CLOSE, then nothing; the peer ends silently on it.
fn close_run(log: &mut Log, seed: u64, timer_first: bool, keep_talking: bool) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        if keep_talking {
            app(log, 1, &mut d.nodes[1], d.now, 5000);
            d.tx(log, 1);
        }
        d.now += 3 * MS;
        let err = seed % 0x40;
        close(log, 0, &mut d.nodes[0], d.now, err);
        assert!(d.nodes[0].conn.is_closed());
        assert_eq!(d.poll(log, 0), Some(0));
        if timer_first {
            // the timer comes before the CLOSE is written: the connection is over and nothing leaves
            d.timeout(log, 0);
            assert_eq!(d.tx(log, 0), 0);
            assert_eq!(log.closes[0], 0);
        } else {
            assert_eq!(d.tx(log, 0), 1, "one CLOSE");
            assert_eq!(log.closes[0], 1);
        }
        d.deliver_all(log);
        if !timer_first {
            assert!(d.nodes[1].conn.is_closed(), "the peer took the CLOSE");
            assert_eq!(d.tx(log, 1), 0, "the peer's end is silent");
        }
        for _ in 0..3 {
            d.now += SEC;
            d.fire(log);
            for n in 0..2 {
                d.tx(log, n);
                app(log, n, &mut d.nodes[n], d.now, 10);
            }
            d.deliver_all(log);
            // a datagram for a closed connection: refused
            if !d.pool.is_empty() {
                d.deliver(log, 0, How::Again);
            }
        }
        assert!(log.closes[0] <= 1 && log.closes[1] == 0);
    });
}

/// A violation: injected frames that do not decode, or that acknowledge a packet never sent; one CLOSE follows.
fn violation_run(log: &mut Log, seed: u64, bad: bool) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        d.now += 5 * MS;
        inject(log, 1, &mut d.nodes[1], d.now, PathId(2), bad);
        assert!(d.nodes[1].conn.is_closed());
        assert_eq!(d.tx(log, 1), 1);
        d.deliver_all(log);
        d.now += SEC;
        d.fire(log);
        d.tx(log, 0);
        d.tx(log, 1);
    });
}

/// A peer that announced its sleep is held 120 s: no idle close at 75 s, a close at the first timer call 120 s after
/// its last SLEEP.
fn sleep_hold_run(log: &mut Log, seed: u64) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        d.now += 10 * MS;
        simple(log, 0, &mut d.nodes[0], d.now, "sleep", 0);
        d.tx(log, 0);
        d.deliver_all(log);
        d.tx(log, 0);
        d.tx(log, 1);
        assert!(d.nodes[1].conn.peer_asleep());
        // nothing more is heard from the sleeper, and what the held side sends is lost
        d.lose_all();
        let pa = d.nodes[1].conn.trace_timers().peer_asleep.unwrap();
        for _ in 0..400 {
            if !d.advance_to_next(log) || d.nodes[1].conn.is_closed() {
                break;
            }
            d.tx(log, 1);
            d.lose_all();
            if d.now < pa + 120 * SEC {
                assert!(
                    !d.nodes[1].conn.is_closed(),
                    "the sleeping peer was let go before 120 s"
                );
            }
        }
        assert!(d.nodes[1].conn.is_closed());
        assert!(d.now >= pa + 120 * SEC);
    });
}

/// A WAKE nobody answers is reported 800 ms later; an answer in time clears the wait.
fn wake_run(log: &mut Log, seed: u64, answered: bool) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        d.now += 10 * MS;
        simple(log, 0, &mut d.nodes[0], d.now, "sleep", 0);
        d.tx(log, 0);
        d.lose_all();
        d.now += 2 * SEC;
        d.fire(log);
        let at = d.now;
        simple(log, 0, &mut d.nodes[0], d.now, "wake", 0);
        d.tx(log, 0);
        if answered {
            d.deliver_all(log);
            d.tx(log, 1);
            d.now += 50 * MS;
            d.deliver_all(log);
        } else {
            d.lose_all();
        }
        let mut cleared = d.nodes[0].conn.trace_timers().wake_deadline.is_none().then_some(d.now);
        if answered {
            assert!(cleared.is_some(), "the answer did not end the wait");
        }
        for _ in 0..100 {
            if d.now >= at + 2 * SEC {
                break;
            }
            if d.next_deadline().is_none_or(|t| t > at + 2 * SEC) {
                d.now = at + 2 * SEC;
                d.fire(log);
            } else {
                d.advance_to_next(log);
            }
            if cleared.is_none() && d.nodes[0].conn.trace_timers().wake_deadline.is_none() {
                cleared = Some(d.now);
            }
            d.tx(log, 0);
            d.tx(log, 1);
            if answered {
                d.deliver_all(log);
            } else {
                d.lose_all();
            }
        }
        if !answered {
            assert_eq!(
                cleared,
                Some(at + 800 * MS),
                "the unanswered WAKE is reported at 800 ms"
            );
        }
    });
}

/// Data in flight and nothing comes back: recovery gives up (or the idle timeout comes first), silently.
fn dead_run(log: &mut Log, seed: u64) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        app(log, 0, &mut d.nodes[0], d.now, 20_000);
        for _ in 0..2000 {
            d.tx(log, 0);
            d.tx(log, 1);
            d.lose_all();
            if d.nodes[0].conn.is_closed() || !d.advance_to_next(log) {
                break;
            }
        }
        assert!(d.nodes[0].conn.is_closed());
        assert_eq!(log.closes, [0, 0], "a silent end sent a CLOSE");
        assert_eq!(d.tx(log, 0), 0);
    });
}

/// How the carrier of the relay path answers in a `relay_run`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Carrier {
    /// Heard 1 ms ago at every timer call.
    Fresh,
    /// Heard exactly 6 s ago: not fresh.
    Stale,
    /// Heard 6 s less a microsecond ago: fresh.
    Edge,
    /// Not open.
    Never,
    /// Fresh, and the peer is heard (a keepalive answer of the carrier) just before every timer call.
    Heard,
    /// Fresh, and the peer last heard exactly 4 fallback round trips (4 x max(333 ms, 2 x the node's)) before every timer
    /// call: silent enough.
    SilentHit,
    /// Fresh, and the peer last heard a microsecond less than 4 fallback round trips before every timer call.
    SilentMiss,
}

/// A session on a path whose probes time out while nothing comes back, with the carrier of a relay path answering as
/// `carrier` says: the probe timeouts grow in a row, and the session is closed behind a live carrier at the 4th when
/// the rule holds. `relay` says whether the active path is a relay path.
fn relay_run(
    log: &mut Log,
    seed: u64,
    relay: bool,
    carrier: Carrier,
    node_rtt: Option<u64>,
    side: usize,
    resent: bool,
) {
    with_pair_at(seed, false, resent, |d| {
        d.init(log);
        d.exchange(log);
        let me = side;
        if let Some(r) = node_rtt {
            d.nodes[me].conn.set_node_rtt(r, 0, false);
        }
        let info = PathInfo {
            kind: if relay { PathKind::Relay } else { PathKind::Direct },
            ..PathInfo::default()
        };
        d.nodes[me].conn.set_path_info(PathId(1 + me as u64), info);
        assert_eq!(d.nodes[me].conn.active_is_relay(), relay);
        d.now += 10 * SEC;
        app(log, me, &mut d.nodes[me], d.now, 20_000);
        for _ in 0..40 {
            d.tx(log, me);
            d.tx(log, 1);
            d.lose_all();
            let Some(t) = d.next_deadline() else { break };
            d.now = d.now.max(t.div_ceil(1000) * 1000);
            let now = d.now;
            d.nodes[me].conn.set_carrier_heard(match carrier {
                Carrier::Fresh | Carrier::Heard | Carrier::SilentHit | Carrier::SilentMiss => Some(now - MS),
                Carrier::Stale => Some(now - 6 * SEC),
                Carrier::Edge => Some(now - 6 * SEC + 1000),
                Carrier::Never => None,
            });
            let four = 4 * (333 * MS).max(2 * node_rtt.unwrap_or(0));
            match carrier {
                Carrier::Heard => simple(log, me, &mut d.nodes[me], now, "pulse", 0),
                Carrier::SilentHit => simple(log, me, &mut d.nodes[me], now - four, "pulse", 0),
                Carrier::SilentMiss => simple(log, me, &mut d.nodes[me], now - four + 1000, "pulse", 0),
                _ => {}
            }
            d.fire(log);
            if d.nodes[me].conn.is_closed() || d.nodes[1 - me].conn.is_closed() {
                break;
            }
        }
        if carrier == Carrier::SilentMiss {
            assert!(
                !d.nodes[me].conn.is_closed(),
                "a session silent for less than 4 round trips was closed"
            );
        }
        if relay && matches!(carrier, Carrier::Fresh | Carrier::Edge | Carrier::SilentHit) {
            assert!(
                d.nodes[me].conn.is_closed(),
                "the session behind a live carrier was not closed"
            );
            assert_eq!(log.closes[me], 0);
            // its CLOSE leaves, once
            d.tx(log, me);
            assert_eq!(log.closes[me], 1, "the carrier close sends its CLOSE");
            d.deliver_all(log);
        }
    });
}

/// A link outage longer than 30 s: the freeze ends by itself at 30 s.
fn link_run(log: &mut Log, seed: u64) {
    with_pair(seed, false, |d| {
        d.init(log);
        d.exchange(log);
        app(log, 0, &mut d.nodes[0], d.now, 20_000);
        d.tx(log, 0);
        d.lose_all();
        d.now += 5 * MS;
        simple(log, 0, &mut d.nodes[0], d.now, "link", 1);
        let down = d.now;
        for _ in 0..200 {
            if !d.advance_to_next(log) || d.now > down + 40 * SEC {
                break;
            }
            d.tx(log, 0);
            d.tx(log, 1);
            d.lose_all();
        }
        assert!(
            d.nodes[0].conn.trace_timers().link_down.is_none(),
            "the outage outlived its bound"
        );
        simple(log, 0, &mut d.nodes[0], d.now, "link", 0);
        d.exchange(log);
    });
}

/// A dial nobody answers: its handshake retransmits, then gives up; or the application closes it first.
fn dial_run(log: &mut Log, seed: u64, close_at: Option<u64>) {
    let w = World::new(IdentityAlg::Ed25519);
    let mut sa = Store::new(true);
    let mut node = w.client(&mut sa, None, ClientTickets::new());
    let mut now = T0;
    init(log, 0, &mut node, now);
    let mut buf = vec![0u8; 65_536];
    let mut rng = SplitMix64::new(seed);
    for _ in 0..400 {
        if let Some(c) = close_at
            && now >= T0 + c
            && !node.conn.is_closed()
        {
            close(log, 0, &mut node, now, 9);
        }
        loop {
            let r = node.with_env(now, |c, env| c.poll_transmit(env, &mut buf));
            let len = r.map_or(0, |t| t.len);
            log.line(0, &mut node, now, "tx", &format!(r#","len":{len}"#));
            if r.is_none() {
                break;
            }
        }
        let Some(t) = poll(log, 0, &mut node, now) else { break };
        // sometimes a timer call before the deadline
        if rng.next_u64().is_multiple_of(4) && t.div_ceil(1000) * 1000 > now + 1000 {
            let at = t.div_ceil(1000) * 1000 - 1000;
            let ev = timeout(log, 0, &mut node, at);
            assert_eq!(ev, Vec::<&str>::new(), "a timer call before the deadline did something");
            now = at;
        }
        now = now.max(t.div_ceil(1000) * 1000);
        timeout(log, 0, &mut node, now);
    }
    assert!(node.conn.is_closed());
}

#[test]
fn timers_match_the_models() {
    big_stack(|| {
        let mut log = Log {
            out: String::new(),
            run: 0,
            closes: [0; 2],
            seen: std::collections::BTreeMap::new(),
        };
        let next = |log: &mut Log| {
            log.run += 1;
            log.closes = [0; 2];
        };
        for seed in 1..=4 {
            next(&mut log);
            idle_run(&mut log, 100 + seed);
        }
        for (i, (timer_first, talk)) in [(false, false), (true, false), (false, true), (true, true)]
            .into_iter()
            .enumerate()
        {
            next(&mut log);
            close_run(&mut log, 200 + i as u64, timer_first, talk);
        }
        for (i, bad) in [true, false].into_iter().enumerate() {
            next(&mut log);
            violation_run(&mut log, 300 + i as u64, bad);
        }
        next(&mut log);
        sleep_hold_run(&mut log, 400);
        for (i, answered) in [false, true].into_iter().enumerate() {
            next(&mut log);
            wake_run(&mut log, 500 + i as u64, answered);
        }
        next(&mut log);
        link_run(&mut log, 600);
        for seed in 0..2 {
            next(&mut log);
            dead_run(&mut log, 650 + seed);
        }
        for (i, c) in [None, Some(2 * SEC)].into_iter().enumerate() {
            next(&mut log);
            dial_run(&mut log, 700 + i as u64, c);
        }
        for (i, (relay, carrier, node)) in [
            (true, Carrier::Fresh, None),
            (true, Carrier::Edge, None),
            (true, Carrier::Stale, None),
            (true, Carrier::Never, None),
            (true, Carrier::Heard, None),
            (false, Carrier::Fresh, None),
            (true, Carrier::Fresh, Some(300 * MS)),
        ]
        .into_iter()
        .enumerate()
        {
            next(&mut log);
            relay_run(&mut log, 800 + i as u64, relay, carrier, node, i % 2, false);
        }
        // the same with no round-trip sample: the first flight of the dial was lost, the handshake measured none
        for (i, (carrier, node, side)) in [
            (Carrier::Fresh, None, 0),
            (Carrier::Fresh, Some(300 * MS), 0),
            (Carrier::Fresh, Some(900 * MS), 0),
            (Carrier::Heard, None, 0),
            (Carrier::Fresh, None, 1),
            (Carrier::SilentHit, None, 0),
            (Carrier::SilentMiss, None, 0),
            (Carrier::SilentHit, Some(900 * MS), 0),
            (Carrier::SilentMiss, Some(900 * MS), 0),
        ]
        .into_iter()
        .enumerate()
        {
            next(&mut log);
            relay_run(&mut log, 850 + i as u64, true, carrier, node, side, true);
        }
        for seed in 1..=24u64 {
            next(&mut log);
            random_run(&mut log, 1000 + seed, 400);
        }
        for k in [
            "idle",
            "local",
            "peer",
            "viol",
            "dead",
            "hs",
            "asleep",
            "awake",
            "unanswered",
            "inject",
            "link",
            "keepalive",
            "pulse",
            "sleep",
            "wake",
            "carrier_close",
            "carrier_close_sampled",
            "carrier_close_unsampled",
            "near_pto3",
            "near_stale",
            "near_nocarrier",
            "near_direct",
            "near_heard_sampled",
            "near_heard_unsampled",
        ] {
            assert!(
                log.seen.get(k).copied().unwrap_or(0) > 0,
                "the scenarios never reached {k}: {:?}",
                log.seen
            );
        }
        eprintln!("timers: {} events {:?}", log.out.lines().count(), log.seen);
        if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("timers.ndjson"), &log.out).unwrap();
        }
    });
}
