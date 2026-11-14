//! Trace generation for the endpoint's half-open cap and the lifetime of an unauthenticated session: seeded runs of a
//! real endpoint (`vinc-core`, built with the `trace` feature), recorded as ndjson (`halfopen.ndjson`) for the TLA+
//! trace check (`TraceHalfOpen.tla`) and the Lean replay (`Vinc/TraceHalfOpen.lean`).
//!
//! The runs feed the endpoint first flights of every message type at, below and above the size floors, garbage, later
//! parts and datagrams too long to be read; fill the half-open table to its cap with forgeries that arrive at staggered
//! times and keep offering more; dial it for real (a full handshake, then a resumption while the table is full, then
//! replays of the used Hello); close a half-open session; leave it with no protocol registered and with a full slot
//! table; stall it by leaving events unread; and step the clock to just before, onto and past the end of each
//! session's 30 s, and back. One line is written per call of the endpoint that decided something or changed the
//! bookkeeping, and for every datagram and timer call: the inputs the decision used (the message type and length the
//! test reads off the datagram, how many sessions held its id, whether the event queue was stalled), the decisions the
//! endpoint recorded in its own trace ring during the call (admissions, sessions made, established, expired and freed)
//! and the slots whose bookkeeping changed, read through the `trace` view `half_open_slot`, with the count, the stall
//! and `poll_timeout` after the call.
//!
//! The host's clock ticks in milliseconds, so every time of a call and every creation time is a whole millisecond:
//! `halfopen.ndjson` writes times in milliseconds (a deadline rounded up, which keeps every comparison of a deadline
//! with a creation time, an end of life or a call exact), so TLC reads every number; `halfopen_ns.ndjson`, read by the
//! Lean replay only, has the same lines in nanoseconds.
//!
//! The test compares every call with a naive reading of the rules: the count is the number of counted sessions and at
//! most 256, a counted session is unauthenticated, an unauthenticated session's deadline is at most 30 s after its
//! creation and `poll_timeout` is the earliest deadline (none while stalled), a timer call leaves no session past its
//! 30 s, an admission is `len >= floor && (resume || count < 256)`, a refused first flight changes no slot and counts
//! one dropped (or stalled) datagram, and a session leaves the count only by being established or freed.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::large_stack_arrays,
    clippy::too_many_arguments,
    clippy::struct_excessive_bools,
    clippy::panic,
    unreachable_pub
)]

use std::fmt::Write as _;
use std::net::SocketAddr;

use vinc_core::{
    Answer, Command, CommandError, Endpoint, EndpointConfig, Event, HALF_OPEN_LIFE, HalfOpenSlot, MAX_DATAGRAM,
    MAX_HALF_OPEN, Query, Reply, Role, SessionId, Slot, TraceEvent,
};
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use vinc_security::message::{FULL_INITIAL_MIN, SHORT_INITIAL_MIN};
use vinc_security::{ConnId, Env, KeyHandle, KeyResponse, LocalIdentity, SoftKeys, SoftPrekeys};
use vinc_tests::*;
use vinc_transport::conn::{Resources, Tables};
use vinc_transport::packet::{LongHeader, LongType};
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, Streams};
use vinc_wire::{Reader, Writer};

const LIFE: u64 = HALF_OPEN_LIFE;
const MAX: usize = MAX_HALF_OPEN;
/// The most sessions that may hold one id (`MAX_CANDIDATES` in `rx.rs`, private to the crate): a first flight for an id
/// that this many hold is dropped.
const HOLDERS: u64 = 4;
/// The table of the big endpoint: room past the cap, so the cap and not the table refuses.
const BK: usize = MAX_HALF_OPEN + 44;
/// The table of the small endpoint: full long before the cap.
const SK: usize = 8;

type Ep<const K: usize, const D: usize> = Endpoint<'static, 'static, Caps, NoSource, 1, 2, 16, 1, K, D, 4, 4, 2>;
type TSlot = Slot<'static, Caps, NoSource, 1, 2, 16, 1>;

fn small_memory() -> Resources<'static, NoSource, 1, 2, 16> {
    let pool = BufferPool::new_boxed(4);
    let streams: &'static mut Streams<NoSource, 1, 2> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    Resources {
        pool,
        streams: streams.into(),
        loss: (&*Box::leak(Box::new(LossEstimate::new()))).into(),
        tables: Tables::new(),
    }
}

fn server<const K: usize, const D: usize>(now: u64) -> (Box<Ep<K, D>>, SocketAddr) {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let v: Vec<TSlot> = (0..K).map(|_| Slot::new(small_memory())).collect();
    let slots: Box<[TSlot; K]> = v.into_boxed_slice().try_into().ok().unwrap();
    let mut ep = Box::new(Endpoint::new(
        now,
        Caps(Software, true),
        Drbg::new(&[3; 32]),
        id,
        EndpointConfig::new(5),
        Box::leak(slots),
    ));
    assert!(ep.register_alpn(ALPN_A));
    let addr: SocketAddr = "10.0.0.1:4433".parse().unwrap();
    ep.add_iface(addr).unwrap();
    (ep, addr)
}

/// A long handshake datagram of exactly `len` bytes for `odcid` whose message (of 4095 bytes) starts at `off` with
/// `kind`, then `salt`.
fn craft(odcid: u64, kind: u8, len: usize, off: u64, salt: u8) -> Vec<u8> {
    let mut d = vec![0u8; len];
    let mut h = LongHeader {
        ty: LongType::Handshake,
        dcid: ConnId::new(&odcid.to_be_bytes()).unwrap(),
        scid: ConnId::new(&[1, 2, 3, 4]).unwrap(),
        body_len: 0,
    };
    for _ in 0..3 {
        h.body_len = len - h.header_len();
    }
    let mut w = Writer::new(&mut d);
    h.write(&mut w, 0).unwrap();
    w.put_varint(4095).unwrap();
    w.put_varint(off).unwrap();
    w.put_u8(kind).unwrap();
    w.put_u8(salt).unwrap();
    d
}

/// The message type of a datagram whose first packet is a long Handshake packet that starts a message (offset 0, a
/// length above 0), 1 to 8; 0 for any other datagram (a later part, another packet, garbage, an unknown type byte).
fn kind_of(buf: &[u8]) -> u8 {
    let Ok((h, hlen)) = LongHeader::parse(buf) else {
        return 0;
    };
    if h.ty != LongType::Handshake {
        return 0;
    }
    let Some(body) = hlen.checked_add(h.body_len).and_then(|e| buf.get(hlen..e)) else {
        return 0;
    };
    let mut r = Reader::new(body);
    let (Ok(total), Ok(off)) = (r.read_varint(), r.read_varint()) else {
        return 0;
    };
    if off != 0 || total == 0 {
        return 0;
    }
    r.read_bytes(r.remaining())
        .ok()
        .and_then(|d| d.first().copied())
        .filter(|b| (1..=8).contains(b))
        .unwrap_or_default()
}

/// The size floor of a first message type, `None` for a type that starts no session.
const fn floor(kind: u8) -> Option<usize> {
    match kind {
        1 => Some(FULL_INITIAL_MIN),
        2 => Some(SHORT_INITIAL_MIN),
        6 => Some(0),
        _ => None,
    }
}

fn source(i: u64) -> SocketAddr {
    SocketAddr::from(([10, 1, (i >> 8) as u8, i as u8], 9))
}

/// What a set of runs exercised.
#[derive(Default, Debug)]
struct Seen {
    lines: u64,
    refused_floor: u32,
    admitted_at_floor: u32,
    refused_cap: u32,
    cap_reached: u32,
    resume_at_cap: u32,
    hello_refused_at_cap: u32,
    accept_failed: u32,
    stalled: u32,
    not_first: u32,
    expired: u32,
    expired_at_end: u32,
    spared_before_end: u32,
    left_by_est: u32,
    left_uncounted_by_est: u32,
    left_by_free: u32,
    stalled_timer: u32,
    clock_back: u32,
    second_holder: u32,
}

/// The host's side of the endpoint: its signing key, and the outputs written so far.
struct Host {
    kp: Keypair,
    prov: Caps,
    drbg: Drbg,
}

impl Host {
    fn new() -> Self {
        Self {
            kp: Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap(),
            prov: Caps(Software, true),
            drbg: Drbg::new(&[9; 32]),
        }
    }
}

#[derive(Clone, Copy)]
enum Op {
    Dgram(u8, usize),
    Timer,
    Other,
}

/// A real endpoint and its recorder: every call goes through [`Rec::call`].
struct Rec<const K: usize, const D: usize> {
    ep: Box<Ep<K, D>>,
    addr: SocketAddr,
    run: u32,
    ms: String,
    ns: String,
    prev: Vec<Option<HalfOpenSlot>>,
    host: Host,
    seen: Seen,
    /// What the next first flight's ticket must give, when the test knows.
    expect_resume: Option<bool>,
    last_now: u64,
}

impl<const K: usize, const D: usize> Rec<K, D> {
    fn new(now: u64, run: u32) -> Self {
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
            last_now: now,
        };
        while r.ep.poll_trace().is_some() {}
        for (unit, out) in [(MS_NS, &mut r.ms), (1, &mut r.ns)] {
            let _ = writeln!(
                out,
                r#"{{"t":"coho","run":{run},"op":"init","k":{K},"max":{MAX},"life":{},"full":{FULL_INITIAL_MIN},"short":{SHORT_INITIAL_MIN},"holders":{HOLDERS}}}"#,
                LIFE / unit
            );
        }
        r
    }

    fn view(&self) -> Vec<Option<HalfOpenSlot>> {
        (0..K).map(|i| self.ep.half_open_slot(i)).collect()
    }

    /// Run `f` on the endpoint at `now` and record it.
    fn call<R>(&mut self, now: u64, op: Op, f: impl FnOnce(&mut Ep<K, D>) -> R) -> R {
        assert_eq!(now % MS_NS, 0, "the host's clock ticks in milliseconds");
        assert_eq!(self.view(), self.prev, "the bookkeeping changed outside a call");
        self.seen.clock_back += u32::from(now < self.last_now);
        self.last_now = now;
        let stalled0 = self.ep.events_stalled();
        let ns0 = self.ep.node_stats();
        let r = f(&mut self.ep);
        assert_eq!(self.ep.trace_dropped(), 0, "the trace ring overflowed");
        let mut steps: Vec<[u64; 4]> = Vec::new();
        let mut n = None;
        while let Some(rec) = self.ep.poll_trace() {
            match rec.event {
                TraceEvent::Demux { candidates, .. } if n.is_none() => n = Some(candidates),
                TraceEvent::HalfOpen {
                    admitted,
                    half_open,
                    resume,
                } => steps.push([0, admitted, half_open, resume]),
                TraceEvent::Session { slot, step: 0, dialer } => steps.push([1, slot, dialer, 0]),
                TraceEvent::Session { slot, step: 1, .. } => steps.push([2, slot, 0, 0]),
                TraceEvent::Session { slot, .. } => steps.push([4, slot, 0, 0]),
                TraceEvent::HalfOpenExpired { slot } => steps.push([3, slot, 0, 0]),
                _ => {}
            }
        }
        let after = self.view();
        let ns1 = self.ep.node_stats();
        let stalled1 = self.ep.events_stalled();
        let timeout = self.ep.poll_timeout();
        let diff: Vec<usize> = (0..K).filter(|i| self.prev[*i] != after[*i]).collect();
        let dropped = ns1.dropped_in - ns0.dropped_in;
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
                .map(|s| format!("[{},{},{},{}]", s[0], s[1], s[2], s[3]))
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
                        None => format!("[{i},0,0,0,0,0,0]"),
                        Some(s) => format!(
                            "[{i},1,{},{},{},{},{}]",
                            exact(s.created),
                            u8::from(s.unauth),
                            u8::from(s.counted),
                            u8::from(s.deadline.is_some()),
                            s.deadline.map_or(0, up)
                        ),
                    })
                    .collect();
                let to = timeout.map_or(String::new(), |t| up(t).to_string());
                let _ = writeln!(
                    out,
                    r#"{{"t":"coho","run":{},"op":"{opn}","now":{},"kind":{kind},"len":{len},"n":{},"stalled0":{},"steps":[{}],"diff":[{}],"count":{},"stalled":{},"timeout":[{to}],"dropped":{dropped},"stalledIn":{stalled_in}}}"#,
                    self.run,
                    exact(now),
                    n.unwrap_or(255).min(255),
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
    fn check(
        &mut self,
        now: u64,
        op: &Op,
        n: Option<u64>,
        stalled0: bool,
        steps: &[[u64; 4]],
        after: &[Option<HalfOpenSlot>],
        count0: usize,
        count: usize,
        stalled: bool,
        timeout: Option<u64>,
        dropped: u64,
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
                    s.deadline.is_some_and(|d| d <= s.created + LIFE),
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
            assert!(b.unauth && now >= b.created + LIFE, "a session expired before its end");
            self.seen.expired += 1;
            self.seen.expired_at_end += u32::from(now == b.created + LIFE);
        }
        if let Op::Timer = op {
            if stalled0 {
                assert!(steps.is_empty(), "a timer ran while the queue was stalled");
                self.seen.stalled_timer += 1;
            }
            if !stalled {
                for s in after.iter().flatten() {
                    assert!(
                        !s.unauth || now < s.created + LIFE,
                        "a session outlived its end past a timer call"
                    );
                    self.seen.spared_before_end += u32::from(s.unauth && now + MS_NS == s.created + LIFE);
                }
            }
        }
        // an admission decision
        let Op::Dgram(kind, len) = *op else { return };
        let freed_first = steps.iter().position(|s| s[0] == 4);
        let decided_at = steps.iter().position(|s| s[0] == 0);
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
        let [code, admitted, c, resume] = steps[0];
        assert_eq!((code, c as usize), (0, count0), "the decision did not use the count");
        assert!(resume == 0 || kind == 6, "a resumption that is no Hello");
        if let Some(e) = self.expect_resume.take() {
            assert_eq!(resume == 1, e, "the ticket did not decide as expected");
        }
        let want = len >= f && (resume == 1 || count0 < MAX);
        assert_eq!(admitted == 1, want, "the admission differs from the rule");
        if admitted == 0 {
            assert!(steps.len() == 1 && !changed, "a refused first flight changed the table");
            assert_eq!(dropped, 1);
            self.seen.refused_floor += u32::from(len < f);
            self.seen.refused_cap += u32::from(len >= f && count0 == MAX);
            self.seen.hello_refused_at_cap += u32::from(len >= f && count0 == MAX && kind == 6);
            return;
        }
        self.seen.admitted_at_floor += u32::from(len == f);
        self.seen.resume_at_cap += u32::from(resume == 1 && count0 == MAX);
        if let Some([1, i, 0, _]) = steps.get(1) {
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

    fn dgram(&mut self, now: u64, from: SocketAddr, mut d: Vec<u8>, expect_resume: Option<bool>) {
        let (kind, len, addr) = (kind_of(&d), d.len(), self.addr);
        self.expect_resume = expect_resume;
        self.call(now, Op::Dgram(kind, len), |ep| {
            ep.handle_datagram(now, addr, from, &mut d);
        });
        self.expect_resume = None;
    }

    fn timer(&mut self, now: u64) {
        self.call(now, Op::Timer, |ep| ep.handle_timeout(now));
    }

    fn command(&mut self, now: u64, c: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        self.call(now, Op::Other, |ep| ep.command(now, c))
    }

    /// Read every event and answer key requests and access checks, as a host does.
    fn drain(&mut self, now: u64) {
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

    fn react(&mut self, now: u64, ev: Event) {
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
    fn transmit(&mut self, now: u64) -> Vec<(SocketAddr, SocketAddr, Vec<u8>)> {
        self.call(now, Op::Other, |ep| {
            let mut v = Vec::new();
            let mut buf = vec![0u8; 65_536];
            while let Some(t) = ep.poll_transmit(now, &mut buf) {
                for chunk in buf[..t.len].chunks(t.segment_size) {
                    v.push((t.local, t.remote, chunk.to_vec()));
                }
            }
            v
        })
    }

    /// A host that ticks in milliseconds: run the timers when they are due.
    fn tick(&mut self, now: u64) {
        if self.ep.poll_timeout().is_some_and(|t| t <= now) {
            self.timer(now);
        }
        self.drain(now);
    }

    fn unauth(&self) -> Vec<(usize, HalfOpenSlot)> {
        self.prev
            .iter()
            .enumerate()
            .filter_map(|(i, s)| s.filter(|s| s.unauth).map(|s| (i, s)))
            .collect()
    }

    fn session_at(&self, i: usize) -> Option<SessionId> {
        self.ep.sessions().find(|s| s.slot() == i)
    }
}

/// A time to run the timers at, as a host with a millisecond clock might: its next deadline, the moment before, at
/// or after the end of a random unauthenticated session, or a little later than now.
fn pick_time<const K: usize, const D: usize>(r: &Rec<K, D>, rng: &mut SplitMix64, now: u64) -> u64 {
    let open = r.unauth();
    match rng.next_u64() % 6 {
        0 | 1 if !open.is_empty() => {
            let (_, s) = open[(rng.next_u64() % open.len() as u64) as usize];
            let end = s.created + LIFE;
            match rng.next_u64() % 3 {
                0 => end - MS_NS,
                1 => end,
                _ => end + MS_NS * (rng.next_u64() % 50),
            }
        }
        2 | 3 => r.ep.poll_timeout().map_or(now + SEC_NS, |t| t.div_ceil(MS_NS) * MS_NS),
        _ => now + MS_NS * (rng.next_u64() % 4000),
    }
}

/// The big endpoint beside one dialer on a `CoreNet`, joined by hand: the dialer's datagrams to the endpoint's
/// address go in through the recorder, the endpoint's go back.
struct Duo {
    net: CoreNet,
    r: Rec<BK, { BK * 10 }>,
    taken: usize,
    /// Damage the next first message the dialer sends, as a path that flips a bit would.
    damage: bool,
    /// Deliver what the dialer sent in one tick in reverse.
    reverse: bool,
}

/// Flip a bit of the message a first flight starts, 20 bytes into it.
fn damage(d: &mut [u8]) {
    let (_, hlen) = LongHeader::parse(d).unwrap();
    let mut r = Reader::new(&d[hlen..]);
    r.read_varint().unwrap();
    r.read_varint().unwrap();
    let at = hlen + r.position() + 20;
    d[at] ^= 1;
}

impl Duo {
    fn new(run: u32) -> Self {
        let mut net = CoreNet::new(MS_NS);
        net.add(2);
        net.capture = true;
        let r = Rec::new(net.now, run);
        Self {
            net,
            r,
            taken: 0,
            damage: false,
            reverse: false,
        }
    }

    /// Move the clock to `t` (a whole millisecond) and hand over what the dialer sent meanwhile.
    fn step_to(&mut self, t: u64) {
        if t > self.net.now {
            self.net.run_for(t - self.net.now);
        }
        let now = self.net.now;
        let mut batch = Vec::new();
        while let Some((from, to, mut d)) = self.net.captured.get(self.taken).cloned() {
            self.taken += 1;
            if to == self.r.addr {
                if self.damage && matches!(kind_of(&d), 1 | 2) {
                    self.damage = false;
                    self.reverse = true;
                    damage(&mut d);
                }
                batch.push((from, d));
            }
        }
        if self.reverse && batch.len() > 1 {
            // after the damage, what arrives together arrives in reverse, so the start of a repeated first message
            // is what completes it
            batch.reverse();
        }
        for (from, d) in batch {
            self.r.dgram(now, from, d, None);
        }
        self.r.tick(now);
        for (local, remote, d) in self.r.transmit(now) {
            self.net.inject(local, remote, d, 0);
        }
    }

    fn drive(&mut self, span: u64) {
        for _ in 0..span / MS_NS {
            let t = self.net.now + MS_NS;
            self.step_to(t);
        }
    }

    fn dial(&mut self, span: u64) -> SessionId {
        let id = LocalIdentity::from_keypair(&self.r.host.kp, KeyHandle(1)).unwrap();
        let (now, to) = (self.net.now, self.r.addr);
        let n0 = self.net.nodes[0].count(|e| matches!(e, Event::Connected { .. }));
        let rep = self.net.nodes[0]
            .connect(now, id.node_id(), ALPN_A, to, Role::Other)
            .unwrap();
        self.drive(span);
        assert_eq!(
            self.net.nodes[0].count(|e| matches!(e, Event::Connected { .. })),
            n0 + 1,
            "no session"
        );
        self.net.nodes[0].session(&rep)
    }

    fn hang_up(&mut self, session: SessionId) {
        let now = self.net.now;
        self.net.nodes[0]
            .cmd(now, Command::Close { session, error: 0 })
            .unwrap();
        self.drive(2 * SEC_NS);
    }

    /// A crafted first flight from a fresh address at the current time.
    fn forge(&mut self, odcid: u64, kind: u8, len: usize) {
        let now = self.net.now;
        self.r.dgram(
            now,
            source(odcid),
            craft(odcid, kind, len, 0, odcid as u8),
            (kind == 6).then_some(false),
        );
    }
}

/// The big endpoint: floors, the cap, a resumption at the cap, replays, a close and the lifetime.
fn big_run(run: u32, seed: u64) -> (String, String, Seen) {
    let mut rng = SplitMix64::new(seed);
    let mut d = Duo::new(run);
    let mut id = u64::from(run) << 32;
    let mut next = || {
        id += 1;
        id
    };
    // floors and types around their edges
    for (kind, len) in [
        (1, FULL_INITIAL_MIN - 1),
        (1, FULL_INITIAL_MIN),
        (1, FULL_INITIAL_MIN + 1),
        (2, SHORT_INITIAL_MIN - 1),
        (2, SHORT_INITIAL_MIN),
        (2, SHORT_INITIAL_MIN + 1),
        (6, 40),
        (6, 300),
        (3, 1300),
        (4, 1300),
        (5, 1300),
        (7, 1300),
        (8, 1300),
        (9, 1300),
    ] {
        d.forge(next(), kind, len);
        d.drive(MS_NS);
    }
    let now = d.net.now;
    let i = next();
    d.r.dgram(now, source(i), craft(i, 1, 1300, 600, 1), None);
    d.r.dgram(now, source(1), vec![0x40; 50], None);
    d.r.dgram(now, source(2), Vec::new(), None);
    d.r.dgram(now, source(3), vec![0xC0; MAX_DATAGRAM + 1], None);
    // no protocol registered: the cap admits, no session is made
    d.r.ep.unregister_alpn(ALPN_A);
    d.forge(next(), 1, FULL_INITIAL_MIN);
    assert!(d.r.ep.register_alpn(ALPN_A));
    d.drive(MS_NS);
    // a full handshake whose first message is damaged on the way: the dialer's repeat gets a session beside the one it made;
    // the dialer then holds a ticket
    d.damage = true;
    let s = d.dial(3 * SEC_NS);
    d.reverse = false;
    d.hang_up(s);
    // a close of a half-open session: it counts until it is freed
    let open = d.r.unauth();
    let (i, _) = open[0];
    let sid = d.r.session_at(i).unwrap();
    let now = d.net.now;
    d.r.command(now, Command::Close { session: sid, error: 0 }).unwrap();
    // the flood, at staggered times, past the cap
    let mut extra = 0;
    while extra < 40 {
        let kind = [1u8, 2, 6][(rng.next_u64() % 3) as usize];
        let f = floor(kind).unwrap();
        let len = match rng.next_u64() % 8 {
            0 => f.max(40),
            1 => f.saturating_sub(1).max(40),
            2 => 1200 + (rng.next_u64() % 100) as usize,
            _ => f.max(40) + (rng.next_u64() % 300) as usize,
        };
        d.forge(next(), kind, len);
        extra += u32::from(d.r.ep.node_stats().half_open == MAX);
        let gap = rng.next_u64() % 25;
        d.drive(gap * MS_NS);
    }
    // a genuine resumption while the table is full, then replays of its Hello and a forged binder
    let mark = d.net.captured.len();
    let s = d.dial(300 * MS_NS);
    let hello = d.net.captured[mark..]
        .iter()
        .find(|c| c.1 == d.r.addr)
        .unwrap()
        .2
        .clone();
    assert_eq!(kind_of(&hello), 6, "the second dial is a resumption");
    d.hang_up(s);
    for k in 0..5u64 {
        let now = d.net.now;
        d.r.dgram(now, source(5000 + k), hello.clone(), Some(false));
        d.drive(MS_NS);
    }
    let mut forged = hello;
    *forged.last_mut().unwrap() ^= 1;
    let now = d.net.now;
    d.r.dgram(now, source(6000), forged, Some(false));
    // the lifetime: timers at the host's deadline, just before, at and after the ends, new first flights between
    let mut now = d.net.now;
    let mut rounds = 0;
    while (!d.r.unauth().is_empty() || rounds < 40) && rounds < 4000 {
        rounds += 1;
        let t = pick_time(&d.r, &mut rng, now).max(now);
        d.step_to(t);
        now = d.net.now;
        if rng.next_u64().is_multiple_of(5) {
            let kind = [1u8, 2, 6][(rng.next_u64() % 3) as usize];
            d.forge(next(), kind, floor(kind).unwrap().max(40));
        }
    }
    assert!(d.r.unauth().is_empty(), "sessions outlived the run");
    let Rec { ms, ns, seen, .. } = d.r;
    (ms, ns, seen)
}

/// Fill the event queue without reading it: each dial to this node itself fails at once with an event.
fn stall<const K: usize, const D: usize>(r: &mut Rec<K, D>, now: u64) {
    let me = r.ep.identity().node_id();
    for _ in 0..100_000 {
        let c = Command::Connect {
            node: me,
            alpn: ALPN_A,
            addrs: &[],
            role: Role::Other,
        };
        match r.command(now, c) {
            Err(CommandError::Refused) => {}
            Err(CommandError::EventsPending) => return,
            other => panic!("unexpected {other:?}"),
        }
    }
    panic!("the queue never stalled");
}

/// The small endpoint: a full slot table, no protocol, a stalled queue, and a clock that steps back.
fn small_run(run: u32, seed: u64) -> (String, String, Seen) {
    let mut rng = SplitMix64::new(seed);
    let mut now = 50 * SEC_NS + (rng.next_u64() % 1000) * MS_NS;
    let mut r: Rec<SK, { SK * 10 }> = Rec::new(now, run);
    let mut id = u64::from(run) << 32;
    let mut forge = |r: &mut Rec<SK, { SK * 10 }>, now: u64, kind: u8, len: usize| {
        id += 1;
        r.dgram(
            now,
            source(id),
            craft(id, kind, len, 0, id as u8),
            (kind == 6).then_some(false),
        );
    };
    for _ in 0..(SK + 3) {
        let kind = [1u8, 2, 6][(rng.next_u64() % 3) as usize];
        let f = floor(kind).unwrap();
        let len = if rng.next_u64().is_multiple_of(4) {
            f.saturating_sub(1).max(40)
        } else {
            f.max(40)
        };
        forge(&mut r, now, kind, len);
        now += MS_NS * (rng.next_u64() % 400);
        r.tick(now);
    }
    r.ep.unregister_alpn(ALPN_A);
    forge(&mut r, now, 2, SHORT_INITIAL_MIN);
    assert!(r.ep.register_alpn(ALPN_A));
    // a stalled queue: no session starts, no timer runs, no deadline is given
    if run.is_multiple_of(2) {
        stall(&mut r, now);
        forge(&mut r, now, 1, FULL_INITIAL_MIN);
        r.timer(now + LIFE + SEC_NS);
        r.drain(now);
    }
    // the lifetime, with a clock that sometimes steps back
    let mut rounds = 0;
    while !r.unauth().is_empty() && rounds < 400 {
        rounds += 1;
        let mut t = pick_time(&r, &mut rng, now).max(now);
        if rng.next_u64().is_multiple_of(7) {
            t = now.saturating_sub(MS_NS * (rng.next_u64() % 3000));
        }
        now = t;
        r.timer(now);
        if rng.next_u64().is_multiple_of(4) {
            let kind = [1u8, 2, 6][(rng.next_u64() % 3) as usize];
            forge(&mut r, now, kind, floor(kind).unwrap().max(40));
        }
    }
    let t = r
        .unauth()
        .iter()
        .map(|(_, s)| s.created + LIFE)
        .max()
        .unwrap_or(now)
        .max(now);
    r.timer(t);
    assert!(r.unauth().is_empty(), "sessions outlived the run");
    let Rec { ms, ns, seen, .. } = r;
    (ms, ns, seen)
}

fn add(a: &mut Seen, b: &Seen) {
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
    a.spared_before_end += b.spared_before_end;
    a.left_by_est += b.left_by_est;
    a.left_uncounted_by_est += b.left_uncounted_by_est;
    a.left_by_free += b.left_by_free;
    a.stalled_timer += b.stalled_timer;
    a.clock_back += b.clock_back;
    a.second_holder += b.second_holder;
}

#[test]
fn the_half_open_cap_matches_the_models() {
    let (ms, ns, seen) = big_stack(|| {
        let (mut ms, mut ns, mut seen) = (String::new(), String::new(), Seen::default());
        for (run, seed) in [(1u32, 0x686f_0001u64), (2, 0x686f_0002)] {
            let (a, b, s) = big_run(run, seed);
            ms.push_str(&a);
            ns.push_str(&b);
            add(&mut seen, &s);
        }
        for run in 10..50u32 {
            let (a, b, s) = small_run(run, 0x686f_0100 + u64::from(run));
            ms.push_str(&a);
            ns.push_str(&b);
            add(&mut seen, &s);
        }
        (ms, ns, seen)
    });
    eprintln!("{seen:?}");
    assert!(
        seen.refused_floor > 0 && seen.admitted_at_floor > 0,
        "the floors were not met at their edges"
    );
    assert!(
        seen.cap_reached > 0 && seen.refused_cap > 0,
        "the cap was not reached and pressed"
    );
    assert!(seen.resume_at_cap > 0, "no resumption was admitted at the cap");
    assert!(
        seen.hello_refused_at_cap > 0,
        "no forged or replayed Hello was refused at the cap"
    );
    assert!(
        seen.accept_failed > 0,
        "no admitted first flight failed to make a session"
    );
    assert!(seen.stalled > 0 && seen.stalled_timer > 0, "the queue never stalled");
    assert!(seen.not_first > 0);
    assert!(
        seen.expired > 0 && seen.expired_at_end > 0,
        "no session expired at its end"
    );
    assert!(seen.spared_before_end > 0, "no timer ran just before a session's end");
    assert!(
        seen.left_by_est > 0 && seen.left_uncounted_by_est > 0,
        "no session was established"
    );
    assert!(
        seen.left_by_free > 0,
        "no counted session was freed other than by its end"
    );
    assert!(seen.clock_back > 0, "the clock never stepped back");
    assert!(
        seen.second_holder > 0,
        "no first message got a session beside a damaged one"
    );
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("halfopen.ndjson"), &ms).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("halfopen_ns.ndjson"), &ns).unwrap();
    }
}
