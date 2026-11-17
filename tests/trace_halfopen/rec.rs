//! The recorder of the half-open trace: a real endpoint whose every call is checked against the naive reading of the
//! rules and written as ndjson in milliseconds and in nanoseconds, with the counters of what the runs reached.

use std::fmt::Write as _;
use std::net::SocketAddr;

use vinc_core::{Answer, Command, CommandError, Event, HalfOpenSlot, Query, Reply, SessionId, TraceEvent};
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use vinc_security::message::{FULL_INITIAL_MIN, RESUME_HELLO_MIN, SHORT_INITIAL_MIN};
use vinc_security::{Env, KeyHandle, KeyResponse, SoftKeys, SoftPrekeys};
use vinc_tests::*;
use vinc_transport::stream::NoSource;

use crate::common::{Ep, HOLD, HOLDERS, LIFE, MAX, floor, kind_of, server};

/// What a set of runs exercised.
#[derive(Default, Debug)]
pub struct Seen {
    pub lines: u64,
    pub refused_floor: u32,
    pub admitted_at_floor: u32,
    pub refused_cap: u32,
    pub cap_reached: u32,
    pub resume_at_cap: u32,
    pub hello_refused_at_cap: u32,
    pub accept_failed: u32,
    pub stalled: u32,
    pub not_first: u32,
    pub expired: u32,
    pub expired_at_end: u32,
    pub spared_at_limit: u32,
    pub rejected: u32,
    pub dropped_first: u32,
    pub refused_half: u32,
    pub left_by_est: u32,
    pub left_uncounted_by_est: u32,
    pub left_by_free: u32,
    pub stalled_timer: u32,
    pub clock_back: u32,
    pub second_holder: u32,
}

/// The host's side of the endpoint: its signing key, and the outputs written so far.
pub struct Host {
    pub kp: Keypair,
    pub prov: Caps,
    pub drbg: Drbg,
}

impl Host {
    pub fn new() -> Self {
        Self {
            kp: Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap(),
            prov: Caps(Software, true),
            drbg: Drbg::new(&[9; 32]),
        }
    }
}

#[derive(Clone, Copy)]
pub enum Op {
    Dgram(u8, usize),
    Timer,
    Other,
}

/// A real endpoint and its recorder: every call goes through [`Rec::call`].
pub struct Rec<const K: usize, const D: usize> {
    pub ep: Box<Ep<K, D>>,
    pub addr: SocketAddr,
    pub run: u32,
    pub ms: String,
    pub ns: String,
    pub prev: Vec<Option<HalfOpenSlot>>,
    pub host: Host,
    pub seen: Seen,
    /// What the next first flight's ticket must give, when the test knows.
    pub expect_resume: Option<bool>,
    /// The next datagram is one a genuine dialer sent, as it left the dialer: while no session holds its ids the
    /// endpoint never rejects or drops it.
    pub genuine: bool,
    pub last_now: u64,
    /// Rejects the endpoint kept to send, and rejects it counted as sent: equal once everything is written.
    pub queued: u64,
    pub written: u64,
}

impl<const K: usize, const D: usize> Rec<K, D> {
    pub fn new(now: u64, run: u32) -> Self {
        let (ep, addr) = server::<K, D>(now);
        let mut r = Self {
            ep,
            addr,
            run,
            ms: String::new(),
            ns: String::new(),
            prev: vec![None; K],
            host: Host::new(),
            seen: Seen::default(),
            expect_resume: None,
            genuine: false,
            last_now: now,
            queued: 0,
            written: 0,
        };
        while r.ep.poll_trace().is_some() {}
        for (unit, out) in [(MS_NS, &mut r.ms), (1, &mut r.ns)] {
            let _ = writeln!(
                out,
                r#"{{"t":"coho","run":{run},"op":"init","k":{K},"max":{MAX},"life":{},"hold":{},"full":{FULL_INITIAL_MIN},"short":{SHORT_INITIAL_MIN},"hello":{RESUME_HELLO_MIN},"holders":{HOLDERS}}}"#,
                LIFE / unit,
                HOLD / unit
            );
        }
        r
    }

    pub fn view(&self) -> Vec<Option<HalfOpenSlot>> {
        (0..K).map(|i| self.ep.half_open_slot(i)).collect()
    }

    /// Run `f` on the endpoint at `now` and record it.
    pub fn call<R>(&mut self, now: u64, op: Op, f: impl FnOnce(&mut Ep<K, D>) -> R) -> R {
        assert_eq!(now % MS_NS, 0, "the host's clock ticks in milliseconds");
        assert_eq!(self.view(), self.prev, "the bookkeeping changed outside a call");
        self.seen.clock_back += u32::from(now < self.last_now);
        self.last_now = now;
        let stalled0 = self.ep.events_stalled();
        let ns0 = self.ep.node_stats();
        let r = f(&mut self.ep);
        assert_eq!(self.ep.trace_dropped(), 0, "the trace ring overflowed");
        let mut steps: Vec<[u64; 6]> = Vec::new();
        let mut n = None;
        while let Some(rec) = self.ep.poll_trace() {
            match rec.event {
                TraceEvent::Demux { candidates, .. } if n.is_none() => n = Some(candidates),
                TraceEvent::HalfOpen {
                    admitted,
                    half_open,
                    resume,
                    room,
                    owed,
                } => steps.push([0, admitted, half_open, resume, room, owed]),
                TraceEvent::Session { slot, step: 0, dialer } => steps.push([1, slot, dialer, 0, 0, 0]),
                TraceEvent::Session { slot, step: 1, .. } => steps.push([2, slot, 0, 0, 0, 0]),
                TraceEvent::Session { slot, .. } => steps.push([4, slot, 0, 0, 0, 0]),
                TraceEvent::HalfOpenExpired { slot } => steps.push([3, slot, 0, 0, 0, 0]),
                _ => {}
            }
        }
        let after = self.view();
        let ns1 = self.ep.node_stats();
        let stalled1 = self.ep.events_stalled();
        let timeout = self.ep.poll_timeout();
        let diff: Vec<usize> = (0..K).filter(|i| self.prev[*i] != after[*i]).collect();
        let dropped = ns1.dropped_in - ns0.dropped_in;
        // a reject that is queued is counted when it is sent, in a later call: only a refusal counts in this one
        let otherwise = (ns1.stateless_refused + ns1.backlog_refused) - (ns0.stateless_refused + ns0.backlog_refused);
        let stalled_in = ns1.stalled_in - ns0.stalled_in;
        self.check(
            now,
            &op,
            n,
            stalled0,
            &steps,
            &after,
            ns0.half_open,
            ns1.half_open,
            stalled1,
            timeout,
            dropped,
            otherwise,
            stalled_in,
        );
        let write =
            matches!(op, Op::Dgram(..) | Op::Timer) || !steps.is_empty() || !diff.is_empty() || stalled0 != stalled1;
        if write {
            self.seen.lines += 1;
            let (opn, kind, len) = match op {
                Op::Dgram(k, l) => ("dgram", k, l),
                Op::Timer => ("timer", 0, 0),
                Op::Other => ("other", 0, 0),
            };
            let steps_s: Vec<String> = steps
                .iter()
                .map(|s| format!("[{},{},{},{},{},{}]", s[0], s[1], s[2], s[3], s[4], s[5]))
                .collect();
            for (unit, out) in [(MS_NS, &mut self.ms), (1, &mut self.ns)] {
                let narrow = |x: u64| {
                    assert!(unit == 1 || x < 1 << 31, "a number past TLC's integers: {x}");
                    x
                };
                let exact = |t: u64| {
                    assert_eq!(t % unit, 0);
                    narrow(t / unit)
                };
                let up = |t: u64| narrow(t.div_ceil(unit));
                let diff_s: Vec<String> = diff
                    .iter()
                    .map(|&i| match after[i] {
                        None => format!("[{i},0,0,0,0,0,0,0]"),
                        Some(s) => format!(
                            "[{i},1,{},{},{},{},{},{}]",
                            exact(s.created),
                            u8::from(s.unauth),
                            u8::from(s.counted),
                            u8::from(s.deadline.is_some()),
                            s.deadline.map_or(0, up),
                            exact(s.life)
                        ),
                    })
                    .collect();
                let to = timeout.map_or(String::new(), |t| up(t).to_string());
                let _ = writeln!(
                    out,
                    r#"{{"t":"coho","run":{},"op":"{opn}","now":{},"kind":{kind},"len":{len},"n":{},"genuine":{},"stalled0":{},"steps":[{}],"diff":[{}],"count":{},"stalled":{},"timeout":[{to}],"dropped":{dropped},"otherwise":{otherwise},"stalledIn":{stalled_in}}}"#,
                    self.run,
                    exact(now),
                    n.unwrap_or(255).min(255),
                    u8::from(self.genuine),
                    u8::from(stalled0),
                    steps_s.join(","),
                    diff_s.join(","),
                    ns1.half_open,
                    u8::from(stalled1)
                );
            }
        }
        self.prev = after;
        r
    }

    /// The naive reading of the rules, on every call.
    pub fn check(
        &mut self,
        now: u64,
        op: &Op,
        n: Option<u64>,
        stalled0: bool,
        steps: &[[u64; 6]],
        after: &[Option<HalfOpenSlot>],
        count0: usize,
        count: usize,
        stalled: bool,
        timeout: Option<u64>,
        dropped: u64,
        otherwise: u64,
        stalled_in: u64,
    ) {
        let before = self.prev.clone();
        // the count and the slots
        let counted = after.iter().flatten().filter(|s| s.counted).count();
        assert_eq!(count, counted, "the count is not the number of counted sessions");
        assert!(count <= MAX, "the count passed the cap");
        self.seen.cap_reached += u32::from(count == MAX && count0 < MAX);
        for s in after.iter().flatten() {
            assert!(!s.counted || s.unauth, "a counted session is authenticated");
            if s.unauth {
                assert!(
                    s.deadline.is_some_and(|d| d <= s.created + s.life + 1) && (s.life == LIFE || s.life == HOLD),
                    "an unauthenticated session's deadline is past its end: {s:?}"
                );
            }
        }
        let earliest = after.iter().flatten().filter_map(|s| s.deadline).min();
        assert_eq!(
            timeout,
            if stalled { None } else { earliest },
            "poll_timeout is not the earliest deadline"
        );
        // a session that is new, left the count or was freed did so by a recorded step
        let has = |code: u64, i: usize| steps.iter().any(|s| s[0] == code && s[1] == i as u64);
        for i in 0..K {
            match (before[i], after[i]) {
                (None, Some(_)) => assert!(has(1, i), "slot {i} was taken without a session"),
                (Some(b), a) => {
                    let left = b.counted && !a.is_some_and(|a| a.counted && a.created == b.created);
                    if left {
                        assert!(has(2, i) || has(4, i), "slot {i} left the count without a step");
                        if has(2, i) {
                            self.seen.left_by_est += 1;
                        } else if !has(3, i) {
                            self.seen.left_by_free += 1;
                        }
                    }
                    if b.unauth && !b.counted && a.is_some_and(|a| !a.unauth && a.created == b.created) {
                        assert!(has(2, i));
                        self.seen.left_uncounted_by_est += 1;
                    }
                }
                (None, None) => {}
            }
        }
        for s in steps.iter().filter(|s| s[0] == 3) {
            let b = before[s[1] as usize].unwrap();
            assert!(matches!(op, Op::Timer), "an expiry outside a timer call");
            assert!(b.unauth && now > b.created + b.life, "a session expired before its end");
            self.seen.expired += 1;
            self.seen.expired_at_end += u32::from(now == b.created + b.life + MS_NS);
        }
        if let Op::Timer = op {
            if stalled0 {
                assert!(steps.is_empty(), "a timer ran while the queue was stalled");
                self.seen.stalled_timer += 1;
            }
            if !stalled {
                for s in after.iter().flatten() {
                    assert!(
                        !s.unauth || now <= s.created + s.life,
                        "a session outlived its end past a timer call"
                    );
                    self.seen.spared_at_limit += u32::from(s.unauth && now == s.created + s.life);
                }
            }
        }
        // an admission decision
        let Op::Dgram(kind, len) = *op else { return };
        let freed_first = steps.iter().position(|s| s[0] == 4);
        let decided_at = steps.iter().position(|s| s[0] == 0);
        // a reject is kept to be sent unless the ledger or a full queue turned it away in this call
        if steps.iter().any(|s| s[0] == 0 && s[1] == 2) {
            self.queued += u64::from(dropped + otherwise == 0);
        }
        if decided_at.is_some() {
            assert!(
                n.is_some_and(|n| n < HOLDERS),
                "a first flight went to the admission for an id that {n:?} sessions hold"
            );
        }
        if n == Some(1) && decided_at.is_some() {
            // a first message that differs from the one a half-open session holds under the same ids gets a session of
            // its own: the held one is not freed
            assert!(
                freed_first.is_none(),
                "a first message freed the session that holds its id"
            );
            self.seen.second_holder += u32::from(steps.iter().any(|s| s[0] == 1));
        }
        if n != Some(0) {
            return;
        }
        let changed = (0..K).any(|i| before[i] != after[i]);
        if stalled0 {
            assert!(steps.is_empty() && !changed, "a stalled endpoint started a session");
            assert_eq!((dropped, stalled_in), (0, 1));
            self.seen.stalled += 1;
            return;
        }
        let Some(f) = floor(kind) else {
            assert!(
                steps.is_empty() && !changed,
                "a datagram that is no first message started a session"
            );
            if kind != 0 {
                assert_eq!(dropped, 1);
            }
            self.seen.not_first += 1;
            return;
        };
        let [code, admitted, c, resume, room, owed] = steps[0];
        assert_eq!((code, c as usize), (0, count0), "the decision did not use the count");
        assert!(resume == 0 || kind == 6, "a resumption that is no Hello");
        if let Some(e) = self.expect_resume.take() {
            assert_eq!(resume == 1, e, "the ticket did not decide as expected");
        }
        // the cap is the code's, or half the room the host left, rounded up, when that is less; no flight is decided
        // on while the owed sessions fill the room
        let cap = MAX.min((room as usize).div_ceil(2));
        let open = owed < room;
        if admitted >= 2 {
            // answered with a reject or dropped, without a session: a short Initial or a Hello at its floor or more, no
            // resumption, and never a first packet a genuine dialer sent (this branch runs only while no session holds
            // the ids)
            assert!(
                matches!(kind, 2 | 6) && resume == 0 && len >= f && open,
                "a first packet was answered without a session that the responder would not only reject"
            );
            assert!(!self.genuine, "a genuine first packet was rejected or dropped");
            assert!(
                steps.len() == 1 && !changed,
                "an answered first packet changed the table"
            );
            if admitted == 3 {
                assert_eq!(dropped + otherwise, 1, "a dropped first packet was not counted once");
            } else {
                // a queued reject is counted when it is sent; only a refusal or a full queue counts in this call
                assert!(dropped + otherwise <= 1, "a rejected first packet was counted twice");
            }
            self.seen.rejected += u32::from(admitted == 2);
            self.seen.dropped_first += u32::from(admitted == 3);
            return;
        }
        let want = len >= f && open && (resume == 1 || count0 < cap);
        assert_eq!(admitted == 1, want, "the admission differs from the rule");
        if admitted == 0 {
            assert!(steps.len() == 1 && !changed, "a refused first flight changed the table");
            assert_eq!(dropped + otherwise, 1);
            self.seen.refused_floor += u32::from(len < f);
            self.seen.refused_cap += u32::from(len >= f && open && count0 == MAX);
            self.seen.refused_half += u32::from(len >= f && open && count0 >= cap && cap < MAX);
            self.seen.hello_refused_at_cap += u32::from(len >= f && open && count0 == MAX && kind == 6);
            return;
        }
        self.seen.admitted_at_floor += u32::from(len == f);
        self.seen.resume_at_cap += u32::from(resume == 1 && count0 == MAX);
        if let Some([1, i, 0, ..]) = steps.get(1) {
            let i = *i as usize;
            assert!(before[i].is_none());
            if let Some(s) = after[i].filter(|_| !has(4, i)) {
                // a resumption may be established by its Hello alone, in the same call
                assert_eq!(
                    (s.created, s.unauth, s.counted),
                    (now, !has(2, i), resume == 0 && !has(2, i))
                );
            }
            self.seen.left_uncounted_by_est += u32::from(resume == 1 && has(2, i));
        } else {
            assert!(!changed, "a first flight that made no session changed the table");
            assert_eq!(dropped, 1);
            self.seen.accept_failed += 1;
        }
    }

    /// A datagram of the genuine dialer, as it left it.
    pub fn peer_dgram(&mut self, now: u64, from: SocketAddr, d: Vec<u8>) {
        self.genuine = true;
        self.dgram(now, from, d, None);
        self.genuine = false;
    }

    pub fn dgram(&mut self, now: u64, from: SocketAddr, mut d: Vec<u8>, expect_resume: Option<bool>) {
        let (kind, len, addr) = (kind_of(&d), d.len(), self.addr);
        self.expect_resume = expect_resume;
        self.call(now, Op::Dgram(kind, len), |ep| {
            ep.handle_datagram(now, addr, from, &mut d);
        });
        self.expect_resume = None;
    }

    pub fn timer(&mut self, now: u64) {
        self.call(now, Op::Timer, |ep| ep.handle_timeout(now));
    }

    pub fn command(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        self.call(now, Op::Other, |ep| ep.command(now, c))
    }

    /// Read every event and answer key requests and access checks, as a host does.
    pub fn drain(&mut self, now: u64) {
        if !self.ep.events_waiting() {
            return;
        }
        let evs = self.call(now, Op::Other, |ep| {
            let mut v = Vec::new();
            while let Some(e) = ep.poll_event() {
                v.push(e);
            }
            v
        });
        for e in evs {
            self.react(now, e);
        }
    }

    pub fn react(&mut self, now: u64, ev: Event) {
        let rep = match ev {
            Event::AcpCheck { check, .. } => self.command(now, Command::AcpAnswer { check, allow: true }),
            Event::KeyRequest { session } => {
                let mut sig = [0u8; MAX_SIGNATURE_LEN];
                let soft = SoftKeys {
                    signer: Some((KeyHandle(1), &self.host.kp)),
                    prekeys: None::<&SoftPrekeys<Caps>>,
                };
                let mut env = Env {
                    provider: &self.host.prov,
                    now,
                    drbg: &mut self.host.drbg,
                };
                let response = match self.ep.query(Query::KeyRequest(session)) {
                    Answer::KeyRequest(req) => match soft.answer(&mut env, &req, &mut sig) {
                        KeyResponse::Signature(s) => KeyResponse::Signature(s),
                        KeyResponse::SharedSecret(s) => KeyResponse::SharedSecret(s),
                        KeyResponse::Failed => KeyResponse::Failed,
                    },
                    _ => return,
                };
                self.command(now, Command::KeyResponse { session, response })
            }
            _ => return,
        };
        for e in rep
            .into_iter()
            .flat_map(|r| r.events.iter().copied().collect::<Vec<_>>())
        {
            self.react(now, e);
        }
    }

    /// Everything the endpoint sends now.
    pub fn transmit(&mut self, now: u64) -> Vec<(SocketAddr, SocketAddr, Vec<u8>)> {
        let (v, sent) = self.call(now, Op::Other, |ep| {
            let (mut v, mut buf) = (Vec::new(), vec![0u8; 65_536]);
            let before = ep.node_stats().stateless_rejects;
            while let Some(t) = ep.poll_transmit(now, &mut buf) {
                for chunk in buf[..t.len].chunks(t.segment_size) {
                    v.push((t.local, t.remote, chunk.to_vec()));
                }
            }
            (v, ep.node_stats().stateless_rejects - before)
        });
        // the exact count, read after the write: every reject kept was counted once when it left, none twice
        self.written += sent;
        assert_eq!(self.written, self.queued, "a reject was not counted exactly once when sent");
        v
    }

    /// A host that ticks in milliseconds: run the timers when they are due.
    pub fn tick(&mut self, now: u64) {
        if self.ep.poll_timeout().is_some_and(|t| t <= now) {
            self.timer(now);
        }
        self.drain(now);
    }

    pub fn unauth(&self) -> Vec<(usize, HalfOpenSlot)> {
        self.prev
            .iter()
            .enumerate()
            .filter_map(|(i, s)| s.filter(|s| s.unauth).map(|s| (i, s)))
            .collect()
    }

    pub fn session_at(&self, i: usize) -> Option<SessionId> {
        self.ep.sessions().find(|s| s.slot() == i)
    }
}

pub fn add(a: &mut Seen, b: &Seen) {
    a.lines += b.lines;
    a.refused_floor += b.refused_floor;
    a.admitted_at_floor += b.admitted_at_floor;
    a.refused_cap += b.refused_cap;
    a.cap_reached += b.cap_reached;
    a.resume_at_cap += b.resume_at_cap;
    a.hello_refused_at_cap += b.hello_refused_at_cap;
    a.accept_failed += b.accept_failed;
    a.stalled += b.stalled;
    a.not_first += b.not_first;
    a.expired += b.expired;
    a.expired_at_end += b.expired_at_end;
    a.spared_at_limit += b.spared_at_limit;
    a.rejected += b.rejected;
    a.dropped_first += b.dropped_first;
    a.refused_half += b.refused_half;
    a.left_by_est += b.left_by_est;
    a.left_uncounted_by_est += b.left_uncounted_by_est;
    a.left_by_free += b.left_by_free;
    a.stalled_timer += b.stalled_timer;
    a.clock_back += b.clock_back;
    a.second_holder += b.second_holder;
}
