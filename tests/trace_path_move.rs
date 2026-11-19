//! Trace generation for path validation and migration: seeded and fixed runs of the dialing side of real established
//! sessions (`pinc-transport`, built with the `trace` and `inject` features), recorded as ndjson (`path_move.ndjson`)
//! for the TLA+ trace check (`TracePathMove.tla`).
//!
//! The test drives the connection `a` through its host calls (`add_path`, `rebind_path`, `remove_path`, `path_lost`,
//! `set_active`, `set_path_info`, `probe`, `punch_known`, `path_returned`), through packets handed to it on any path
//! (`inject_payload`: answers to its real challenges, to replaced ones, forged ones, on the wrong path and after a
//! rebind, challenges, and data with and without WAKE, the highest numbered or older), through its built datagrams
//! (thrown away) and through its timers (the 15 s silence and one nanosecond past it, probes due, the third probe
//! timeout in a row and later ones, thin and not). Paths added as relayed run through a node that carries the relay
//! role. After the session is established the peer is never driven again. Every call is recorded with the path table
//! before and after it (`Connection::trace_paths`), challenge bytes numbered in the order they are first seen.
//!
//! The test asserts by itself that no path id is held twice, that the active slot holds a path, that a forged answer
//! validates nothing, and the checks of each fixed run; the model reads the rest. The trace is written to
//! `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::similar_names,
    unreachable_pub,
    clippy::redundant_closure_for_method_calls,
    clippy::unused_self
)]

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{Drop as RxDrop, PathError, PathId, PathInfo, PathsView, SlotView};
use pinc_transport::frame::Frame;
use pinc_transport::recovery::PathKind;
use pinc_wire::Writer;

/// The places of the path table of the connection under test.
const NP: usize = 4;
/// A silent direct path is left out after this long.
const IDLE: u64 = 15 * SEC;
/// A run injects something at least this often (the idle timeout is 75 s).
const INJECT_EVERY: u64 = 24 * SEC;
/// The first packet number the test injects above.
const PN0: u64 = 1_000_000;
const EMPTY_SLOT: &str = r#"{"id":0,"k":"d","six":false,"v":false,"ch":0,"sent":[0,0,0,0],"nx":1,"sc":false,"pr":false,"rj":false,"gone":false,"hd":"never","r":[0,0,0,0]}"#;

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn encoded(frames: &[Frame<'_>]) -> Vec<u8> {
    let mut buf = vec![0u8; 1400];
    let mut w = Writer::new(&mut buf);
    for f in frames {
        f.write(&mut w).unwrap();
    }
    let n = w.written().len();
    buf.truncate(n);
    buf
}

fn kind_of(relay: bool) -> PathKind {
    if relay { PathKind::Relay } else { PathKind::Direct }
}

fn kind_str(relay: bool) -> &'static str {
    if relay { "r" } else { "d" }
}

fn path_res(r: Result<(), PathError>) -> &'static str {
    match r {
        Ok(()) => "ok",
        Err(PathError::TooMany) => "toomany",
        Err(PathError::Unknown) => "unknown",
        Err(PathError::NotValidated) => "notvalidated",
        Err(PathError::Active) => "active",
        Err(PathError::Exists) => "exists",
    }
}

fn heard(last_rx: u64, at: u64) -> &'static str {
    if last_rx == 0 {
        "never"
    } else if at.saturating_sub(last_rx) > IDLE {
        "stale"
    } else {
        "fresh"
    }
}

fn held_ids(net: &Net<'_, '_>) -> Vec<u64> {
    net.a.conn.path_list().map(|(p, _, _)| p.0).collect()
}

fn validated_count(net: &Net<'_, '_>) -> usize {
    net.a.conn.path_list().filter(|(_, _, v)| *v).count()
}

/// What the whole trace saw, and its text.
#[derive(Default)]
struct PmTrace {
    out: String,
    seen: BTreeSet<String>,
}

/// A packet number taken for an injected packet: the highest so far (`hi`), or an odd one below it.
#[derive(Clone, Copy)]
struct Pn {
    n: u64,
    hi: bool,
}

/// One run: the clock, the numbering of challenge bytes and of packets, and what the rules of the run keep.
struct PmRun<'t> {
    tr: &'t mut PmTrace,
    run: u32,
    rng: SplitMix64,
    toks: BTreeMap<[u8; 8], u32>,
    now: u64,
    top: u64,
    used: BTreeSet<u64>,
    last_inj: u64,
    lost: BTreeSet<u64>,
    live: bool,
}

impl<'t> PmRun<'t> {
    fn new(tr: &'t mut PmTrace, run: u32, net: &mut Net<'_, '_>, seed: u64) -> Self {
        let mut r = Self {
            tr,
            run,
            rng: SplitMix64::new(seed),
            toks: BTreeMap::new(),
            now: net.now,
            top: PN0,
            used: BTreeSet::new(),
            last_inj: net.now,
            lost: BTreeSet::new(),
            live: true,
        };
        let view = net.a.conn.trace_paths();
        r.number(&view, &view, "init");
        let v = r.view(&view, view.clock);
        let _ = writeln!(
            r.tr.out,
            r#"{{"t":"pm","run":{run},"op":"init","pre":{v},"post":{v},"np":{NP}}}"#
        );
        r.tr.seen.insert("init".into());
        r
    }

    fn tok(&self, b: Option<[u8; 8]>) -> u32 {
        b.map_or(0, |b| *self.toks.get(&b).expect("challenge bytes are numbered"))
    }

    fn slot(&self, s: Option<&SlotView>, at: u64) -> String {
        let Some(s) = s else { return EMPTY_SLOT.to_owned() };
        format!(
            r#"{{"id":{},"k":"{}","six":{},"v":{},"ch":{},"sent":[{},{},{},{}],"nx":{},"sc":{},"pr":{},"rj":{},"gone":{},"hd":"{}","r":{}}}"#,
            s.id,
            kind_str(s.relay),
            s.v6,
            s.validated,
            self.tok(s.challenge),
            self.tok(s.sent[0]),
            self.tok(s.sent[1]),
            self.tok(s.sent[2]),
            self.tok(s.sent[3]),
            s.sent_next + 1,
            s.send_challenge,
            s.probes_left > 0,
            s.rejoin,
            s.gone,
            heard(s.last_rx, at),
            limbs(s.rtt)
        )
    }

    fn view(&self, v: &PathsView, at: u64) -> String {
        let slots: Vec<String> = v.slots.iter().map(|s| self.slot(s.as_ref(), at)).collect();
        format!(
            r#"{{"act":{},"smp":{},"srtt":{},"thin":{},"decl":{},"pto":{},"paths":[{}]}}"#,
            v.active + 1,
            v.srtt.is_some(),
            limbs(v.srtt.unwrap_or(0)),
            v.thin,
            v.decl,
            v.pto,
            slots.join(",")
        )
    }

    /// Number the challenge bytes the `post` view shows for the first time, in the order the code draws them; the
    /// `pre` view holds none the map lacks.
    fn number(&mut self, pre: &PathsView, post: &PathsView, op: &str) {
        if op != "init" {
            for s in pre.slots.iter().flatten() {
                for b in s.challenge.iter().chain(s.sent.iter().flatten()) {
                    assert!(
                        self.toks.contains_key(b),
                        "run {}: the view before {op} holds unnumbered bytes",
                        self.run
                    );
                }
            }
        }
        let order: Vec<usize> = if op == "timer" && post.pto >= 3 {
            std::iter::once(pre.active).chain(0..post.slots.len()).collect()
        } else {
            (0..post.slots.len()).collect()
        };
        for i in order {
            let Some(Some(s)) = post.slots.get(i) else { continue };
            for b in s.challenge.iter().chain(s.sent.iter().flatten()) {
                let n = self.toks.len() as u32 + 1;
                self.toks.entry(*b).or_insert(n);
            }
        }
    }

    /// The invariants of the table, after every call.
    fn check(&self, net: &Net<'_, '_>, post: &PathsView) {
        let ids = held_ids(net);
        let unique: BTreeSet<u64> = ids.iter().copied().collect();
        assert_eq!(ids.len(), unique.len(), "run {}: a path id is held twice", self.run);
        assert_eq!(post.slots.len(), NP);
        assert!(
            post.slots[post.active].is_some(),
            "run {}: the active slot is empty",
            self.run
        );
    }

    /// One call and its line. `call` returns the op fields (starting with a comma), or `None` for a call not recorded.
    /// Returns whether a line was written; a run whose connection ended stops without recording the call.
    fn ev(
        &mut self,
        net: &mut Net<'_, '_>,
        op: &'static str,
        at_now: bool,
        call: impl FnOnce(&mut Net<'_, '_>, u64) -> Option<String>,
    ) -> bool {
        if !self.live {
            return false;
        }
        let pre = net.a.conn.trace_paths();
        let now = self.now;
        let fields = call(net, now);
        if !net.a.conn.is_connected() {
            self.live = false;
            return false;
        }
        let post = net.a.conn.trace_paths();
        self.check(net, &post);
        let Some(fields) = fields else { return false };
        self.number(&pre, &post, op);
        let at_pre = if at_now { now } else { pre.clock };
        let line = format!(
            r#"{{"t":"pm","run":{},"op":"{op}","pre":{},"post":{}{fields}}}"#,
            self.run,
            self.view(&pre, at_pre),
            self.view(&post, post.clock)
        );
        self.tr.out.push_str(&line);
        self.tr.out.push('\n');
        self.tr.seen.insert(op.to_owned());
        if let Some(i) = fields.find(r#""r":"#) {
            let rest = &fields[i + 4..];
            let end = rest.find(',').unwrap_or(rest.len());
            self.tr.seen.insert(format!("r:{}", rest[..end].trim_matches('"')));
        }
        if op == "timer" {
            self.tr.seen.insert(if pre.thin { "thin" } else { "nonthin" }.into());
            if post.pto == 3 {
                self.tr.seen.insert("pto3".into());
            }
            if post.pto >= 4 {
                self.tr.seen.insert("pto4".into());
            }
        }
        true
    }

    fn adv(&mut self, ns: u64) {
        self.now += ns;
    }

    /// The `PathInfo` of a call that names kind and v6: a held path keeps its interface MTU.
    fn info_for(net: &Net<'_, '_>, id: u64, relay: bool, v6: bool) -> PathInfo {
        let held = net.a.conn.path_list().find(|(p, _, _)| p.0 == id).map(|(_, i, _)| i);
        PathInfo {
            kind: kind_of(relay),
            v6,
            ..held.unwrap_or_default()
        }
    }

    // ---- host calls ----

    fn add(&mut self, net: &mut Net<'_, '_>, id: u64, relay: bool, v6: bool) {
        let info = Self::info_for(net, id, relay, v6);
        self.ev(net, "add", false, |n, now| {
            let r = n.a.with_env(now, |c, env| c.add_path(env, PathId(id), info));
            Some(format!(
                r#","id":{id},"k":"{}","six":{v6},"r":"{}""#,
                kind_str(relay),
                path_res(r)
            ))
        });
    }

    fn rebind(&mut self, net: &mut Net<'_, '_>, id: u64, nid: u64) {
        self.ev(net, "rebind", false, |n, _| {
            let r = n.a.conn.rebind_path(PathId(id), PathId(nid));
            Some(format!(r#","id":{id},"nid":{nid},"r":"{}""#, path_res(r)))
        });
    }

    fn remove(&mut self, net: &mut Net<'_, '_>, id: u64) {
        self.ev(net, "remove", false, |n, _| {
            let r = n.a.conn.remove_path(PathId(id));
            Some(format!(r#","id":{id},"r":"{}""#, path_res(r)))
        });
    }

    fn lost(&mut self, net: &mut Net<'_, '_>, id: u64) {
        self.lost.insert(id);
        self.ev(net, "lost", false, |n, _| {
            let r = n.a.conn.path_lost(PathId(id));
            Some(format!(r#","id":{id},"r":"{}""#, path_res(r)))
        });
    }

    fn set(&mut self, net: &mut Net<'_, '_>, id: u64) {
        self.ev(net, "set", false, |n, _| {
            let r = n.a.conn.set_active(PathId(id));
            Some(format!(r#","id":{id},"r":"{}""#, path_res(r)))
        });
    }

    fn info(&mut self, net: &mut Net<'_, '_>, id: u64, relay: bool, v6: bool) {
        let info = Self::info_for(net, id, relay, v6);
        self.ev(net, "info", false, |n, _| {
            n.a.conn.set_path_info(PathId(id), info);
            Some(format!(r#","id":{id},"k":"{}","six":{v6}"#, kind_str(relay)))
        });
    }

    fn probe(&mut self, net: &mut Net<'_, '_>, id: u64) {
        self.ev(net, "probe", false, |n, now| {
            let r = n.a.with_env(now, |c, env| c.probe(env, PathId(id)));
            Some(format!(r#","id":{id},"r":"{}""#, path_res(r)))
        });
    }

    fn punch(&mut self, net: &mut Net<'_, '_>) {
        self.ev(net, "punch", false, |n, now| {
            n.a.with_env(now, |c, env| c.punch_known(env));
            Some(String::new())
        });
    }

    fn returned(&mut self, net: &mut Net<'_, '_>, id: u64, rtt: u64) -> bool {
        let mut got = false;
        self.ev(net, "returned", false, |n, now| {
            got = n.a.conn.path_returned(PathId(id), rtt, now);
            Some(format!(r#","id":{id},"rtt":{},"r":{got}"#, limbs(rtt)))
        });
        got
    }

    fn rejoin_floor(net: &mut Net<'_, '_>, id: u64, at: u64) {
        net.a.conn.set_rejoin_floor(PathId(id), at);
    }

    // ---- packets handed to the connection ----

    /// The largest unused odd packet number below the highest one handed in, above the first.
    fn lo_candidate(&self) -> Option<u64> {
        let mut n = self.top.checked_sub(1)?;
        while n > PN0 {
            if !self.used.contains(&n) {
                return Some(n);
            }
            n -= 2;
        }
        None
    }

    fn take_pn(&mut self, hi: bool) -> Option<Pn> {
        if hi {
            self.top += 2;
            Some(Pn { n: self.top, hi })
        } else {
            let n = self.lo_candidate()?;
            self.used.insert(n);
            Some(Pn { n, hi })
        }
    }

    /// A packet refused for want of a place was never recorded as received: its number is free again.
    fn settle(&mut self, p: Pn, ok: bool) {
        if !ok {
            if p.hi {
                self.top -= 2;
            } else {
                self.used.remove(&p.n);
            }
        }
    }

    /// Hand `payload` to the connection on path `on`; `fields` builds the op fields from the result text.
    fn inject(
        &mut self,
        net: &mut Net<'_, '_>,
        op: &'static str,
        on: u64,
        payload: &[u8],
        hi: bool,
        fields: impl FnOnce(&str) -> String,
    ) -> Option<&'static str> {
        let pn = self.take_pn(hi)?;
        let mut r: &'static str = "ok";
        let recorded = self.ev(net, op, false, |n, now| {
            let res =
                n.a.with_env(now, |c, env| c.inject_payload(env, PathId(on), now, pn.n, payload));
            n.a.service(now);
            r = match res {
                Ok(()) => "ok",
                Err(RxDrop::NoPath) => "nopath",
                Err(e) => panic!("{op} on {on}: {e:?}"),
            };
            Some(fields(r))
        });
        self.settle(pn, r == "ok");
        if recorded && r == "ok" {
            self.last_inj = self.now;
        }
        Some(r)
    }

    fn rtt_of(&self, net: &Net<'_, '_>, on: u64) -> u64 {
        net.a
            .conn
            .trace_paths()
            .slots
            .iter()
            .flatten()
            .find(|s| s.id == on)
            .map_or(0, |s| {
                if s.last_tx == 0 {
                    0
                } else {
                    self.now.saturating_sub(s.last_tx)
                }
            })
    }

    /// Whether an answer on `on` keeps every round trip below 2^30 ns.
    fn resp_ok(&self, net: &Net<'_, '_>, on: u64) -> bool {
        self.rtt_of(net, on) < 500 * MS
    }

    /// An answer carrying `bytes` on path `on`; forged bytes are no challenge of the run.
    fn resp(&mut self, net: &mut Net<'_, '_>, on: u64, bytes: [u8; 8], forged: bool) {
        assert!(
            self.resp_ok(net, on),
            "run {}: an answer on {on} would break the round trip bound",
            self.run
        );
        let tok = if forged {
            assert!(
                !self.toks.contains_key(&bytes),
                "forged bytes are a challenge of the run"
            );
            0
        } else {
            *self.toks.get(&bytes).expect("an answer carries a numbered challenge")
        };
        let rtt = self.rtt_of(net, on);
        let before = validated_count(net);
        let payload = encoded(&[Frame::PathResponse(bytes)]);
        self.inject(net, "resp", on, &payload, true, |r| {
            format!(r#","id":{on},"tok":{tok},"rtt":{},"r":"{r}""#, limbs(rtt))
        });
        if forged {
            assert!(
                validated_count(net) <= before,
                "run {}: a forged answer validated a path",
                self.run
            );
        }
    }

    /// An answer carrying the challenge `bytes` of the run on path `on`.
    fn resp_real(&mut self, net: &mut Net<'_, '_>, on: u64, bytes: [u8; 8]) {
        self.resp(net, on, bytes, false);
    }

    fn forged(&mut self) -> [u8; 8] {
        loop {
            let mut b = [0u8; 8];
            self.rng.fill(&mut b);
            if !self.toks.contains_key(&b) {
                return b;
            }
        }
    }

    fn resp_forged(&mut self, net: &mut Net<'_, '_>, on: u64) {
        let b = self.forged();
        self.resp(net, on, b, true);
    }

    /// The challenges a path keeps, oldest drawn first.
    fn kept(&self, net: &Net<'_, '_>, id: u64) -> Vec<[u8; 8]> {
        let v = net.a.conn.trace_paths();
        let Some(s) = v.slots.iter().flatten().find(|s| s.id == id) else {
            return Vec::new();
        };
        let mut all: Vec<[u8; 8]> = s
            .challenge
            .into_iter()
            .chain(s.sent.iter().flatten().copied())
            .collect();
        all.sort_by_key(|b| self.toks[b]);
        all.dedup();
        all
    }

    fn outstanding(&self, net: &Net<'_, '_>, id: u64) -> Option<[u8; 8]> {
        net.a
            .conn
            .trace_paths()
            .slots
            .iter()
            .flatten()
            .find(|s| s.id == id)
            .and_then(|s| s.challenge)
    }

    /// Answer the challenge outstanding on `id`, if there is one.
    fn answer(&mut self, net: &mut Net<'_, '_>, id: u64) {
        if let Some(b) = self.outstanding(net, id) {
            self.resp_real(net, id, b);
        }
    }

    fn chal(&mut self, net: &mut Net<'_, '_>, id: u64) {
        let mut b = [0u8; 8];
        self.rng.fill(&mut b);
        let payload = encoded(&[Frame::PathChallenge(b)]);
        self.inject(net, "chal", id, &payload, true, |r| format!(r#","id":{id},"r":"{r}""#));
    }

    /// Data on `id`: the highest numbered packet or an older one, with WAKE or without. `None` when no older number
    /// is free.
    fn data(&mut self, net: &mut Net<'_, '_>, id: u64, hi: bool, wake: bool) -> Option<&'static str> {
        let mut frames = vec![Frame::Datagram {
            data: b"d",
            implicit_len: false,
        }];
        if wake {
            frames.push(Frame::Wake);
        }
        let payload = encoded(&frames);
        self.inject(net, "data", id, &payload, hi, |r| {
            format!(r#","id":{id},"hi":{hi},"wake":{wake},"r":"{r}""#)
        })
    }

    // ---- built datagrams and timers ----

    fn send(&mut self, net: &mut Net<'_, '_>) -> bool {
        self.ev(net, "send", true, |n, now| {
            let mut buf = vec![0u8; 65_536];
            n.a.with_env(now, |c, env| c.poll_transmit(env, &mut buf))
                .map(|_| String::new())
        })
    }

    /// Build datagrams until there is none to build.
    fn send_all(&mut self, net: &mut Net<'_, '_>) {
        for _ in 0..64 {
            if !self.send(net) {
                return;
            }
        }
        panic!("run {}: the connection keeps building datagrams", self.run);
    }

    fn timer_at(&mut self, net: &mut Net<'_, '_>, t: u64) {
        assert!(t >= self.now, "a timer before the last instant");
        self.now = t;
        self.ev(net, "timer", true, |n, now| {
            n.a.with_env(now, |c, env| c.handle_timeout(env));
            Some(String::new())
        });
    }

    fn timer_next(&mut self, net: &mut Net<'_, '_>) {
        let t = net.a.conn.poll_timeout().unwrap_or(self.now + MS).max(self.now);
        self.timer_at(net, t);
    }

    /// Timers at the next deadline, with the datagrams they leave built, until `n` probe timeouts are in a row.
    fn until_pto(&mut self, net: &mut Net<'_, '_>, n: u32) {
        for _ in 0..200 {
            if !self.live || net.a.conn.trace_paths().pto >= n {
                return;
            }
            self.timer_next(net);
            self.send_all(net);
        }
        panic!("run {}: {n} probe timeouts in a row were not reached", self.run);
    }

    // ---- the random steps ----

    fn pick(&mut self, v: &[u64]) -> Option<u64> {
        (!v.is_empty()).then(|| v[(self.rng.next_u64() % v.len() as u64) as usize])
    }

    fn coin(&mut self, n: u64) -> bool {
        self.rng.next_u64().is_multiple_of(n)
    }

    /// One random step; `true` when it was a timer (which moves the clock itself).
    fn random_step(&mut self, net: &mut Net<'_, '_>, start: u64) -> bool {
        let held = held_ids(net);
        match self.rng.next_u64() % 14 {
            0 => {
                let (id, relay, v6) = (2 + self.rng.next_u64() % 5, self.coin(2), self.coin(2));
                self.add(net, id, relay, v6);
            }
            1 => {
                if let Some(id) = self.pick(&held) {
                    let nid = 2 + self.rng.next_u64() % 6;
                    self.rebind(net, id, nid);
                }
            }
            2 => {
                if let Some(id) = self.pick(&held) {
                    self.remove(net, id);
                }
            }
            3 => {
                if let Some(id) = self.pick(&held) {
                    self.lost(net, id);
                }
            }
            4 => {
                if let Some(id) = self.pick(&held) {
                    self.set(net, id);
                }
            }
            5 => {
                if let Some(id) = self.pick(&held) {
                    let (relay, v6) = (self.coin(2), self.coin(2));
                    self.info(net, id, relay, v6);
                }
            }
            6 => {
                if let Some(id) = self.pick(&held) {
                    self.probe(net, id);
                }
            }
            7 => self.punch(net),
            8 => {
                if let Some(id) = self.pick(&held) {
                    let rtt = [0, 7 * MS, 40 * MS][(self.rng.next_u64() % 3) as usize];
                    self.returned(net, id, rtt);
                }
            }
            9 => self.random_resp(net),
            10 => {
                let id = 1 + self.rng.next_u64() % 7;
                self.chal(net, id);
            }
            11 => {
                let id = 1 + self.rng.next_u64() % 7;
                let wake = self.coin(4);
                let hi = !self.coin(4);
                if self.data(net, id, hi, wake).is_none() {
                    self.data(net, id, true, wake);
                }
            }
            12 => self.send_all(net),
            _ => {
                self.random_timer(net, start);
                return true;
            }
        }
        false
    }

    /// An answer: a known number of the run, the outstanding challenge of a random slot, or forged bytes; on a random id.
    fn random_resp(&mut self, net: &mut Net<'_, '_>) {
        let on = 1 + self.rng.next_u64() % 7;
        if self.lost.contains(&on) || !self.resp_ok(net, on) {
            return;
        }
        let known = match self.rng.next_u64() % 3 {
            0 if !self.toks.is_empty() => {
                let n = 1 + (self.rng.next_u64() % self.toks.len() as u64) as u32;
                self.toks.iter().find(|(_, t)| **t == n).map(|(b, _)| *b)
            }
            1 => {
                let view = net.a.conn.trace_paths();
                let chals: Vec<[u8; 8]> = view.slots.iter().flatten().filter_map(|s| s.challenge).collect();
                (!chals.is_empty()).then(|| chals[(self.rng.next_u64() % chals.len() as u64) as usize])
            }
            _ => None,
        };
        match known {
            Some(b) => self.resp_real(net, on, b),
            None => self.resp_forged(net, on),
        }
    }

    /// A timer at the next deadline or at a chosen instant, never past the 24 s a run goes without injecting
    /// something, and not at the tenth probe timeout in a row: at the ninth a data packet comes first.
    fn random_timer(&mut self, net: &mut Net<'_, '_>, start: u64) {
        let t = if self.coin(2) {
            net.a.conn.poll_timeout().unwrap_or(self.now + MS)
        } else {
            self.now + (1 + self.rng.next_u64() % 20_000) * MS
        };
        if net.a.conn.trace_paths().pto >= 9 {
            let active = net.a.conn.active_path().map_or(1, |p| p.0);
            self.data(net, active, true, false);
            if !self.live {
                return;
            }
        }
        let t = t.min(start + 60 * SEC).min(self.last_inj + INJECT_EVERY).max(self.now);
        self.timer_at(net, t);
    }
}

/// An established pair on a fresh world, handed to `f`.
fn with_net(thin: bool, seed: u64, f: impl FnOnce(&mut Net<'_, '_>)) {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.thin = thin;
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, Params::new(10 * MS)));
    assert!(net.connect(net.now + 10 * SEC));
    f(&mut net);
}

/// One fixed run: a fresh pair, `init`, then `body`.
fn fixed(tr: &mut PmTrace, run: u32, thin: bool, body: impl FnOnce(&mut Net<'_, '_>, &mut PmRun<'_>)) {
    with_net(thin, 5000 + u64::from(run), |net| {
        let mut r = PmRun::new(tr, run, net, 0x504D_1000 + u64::from(run));
        body(net, &mut r);
    });
}

/// Data in flight, so that probe timeouts happen.
fn flight(net: &mut Net<'_, '_>, len: usize) {
    let id = net.a.conn.open_bi().unwrap();
    net.a.conn.write(id, &vec![0x5a; len]).unwrap();
}

fn active(net: &Net<'_, '_>) -> u64 {
    net.a.conn.active_path().unwrap().0
}

fn validated(net: &Net<'_, '_>, id: u64) -> bool {
    net.a.conn.path_validated(PathId(id))
}

fn fixed_runs(tr: &mut PmTrace) {
    // 0: validation
    fixed(tr, 0, false, |net, r| {
        r.add(net, 2, false, false);
        r.send_all(net);
        r.adv(3 * MS);
        let c = r.outstanding(net, 2).unwrap();
        assert!(!validated(net, 2));
        r.resp_real(net, 2, c);
        assert!(validated(net, 2), "an answer on its path validates it");
    });
    // 1: a wrong path and forged bytes
    fixed(tr, 1, false, |net, r| {
        r.add(net, 2, false, false);
        r.send_all(net);
        r.adv(3 * MS);
        let c = r.outstanding(net, 2).unwrap();
        r.resp_real(net, 1, c);
        r.resp_real(net, 7, c);
        r.resp_forged(net, 2);
        assert!(!validated(net, 2));
        r.resp_real(net, 2, c);
    });
    // 2: a replaced challenge is still kept
    fixed(tr, 2, false, |net, r| {
        r.add(net, 2, false, false);
        for _ in 0..2 {
            r.probe(net, 2);
            r.send_all(net);
            r.adv(3 * MS);
        }
        let first = r.kept(net, 2)[0];
        r.resp_real(net, 2, first);
        assert!(validated(net, 2), "an answer to a replaced challenge validates");
    });
    // 3: the table wraps
    fixed(tr, 3, false, |net, r| {
        r.add(net, 2, false, false);
        r.probe(net, 2);
        r.send_all(net);
        r.adv(3 * MS);
        let first = r.kept(net, 2)[0];
        for _ in 0..4 {
            r.probe(net, 2);
            r.send_all(net);
            r.adv(3 * MS);
        }
        r.resp_real(net, 2, first);
        assert!(!validated(net, 2), "an overwritten challenge validated a path");
        let newest = *r.kept(net, 2).last().unwrap();
        r.resp_real(net, 2, newest);
    });
    // 4: a rebind during validation
    fixed(tr, 4, false, |net, r| {
        r.add(net, 2, false, false);
        r.send_all(net);
        r.adv(3 * MS);
        r.rebind(net, 2, 3);
        let c = r.outstanding(net, 3).unwrap();
        r.resp_real(net, 3, c);
        assert!(validated(net, 3), "the answer after a rebind validates the path");
        r.resp_real(net, 2, c);
        r.rebind(net, 3, 1);
        r.rebind(net, 9, 5);
    });
    // 5: host calls refused
    fixed(tr, 5, false, |net, r| {
        r.add(net, 2, false, false);
        r.remove(net, 1);
        r.remove(net, 9);
        r.lost(net, 9);
        r.set(net, 9);
        r.probe(net, 9);
        r.set(net, 2);
        assert!(!r.returned(net, 1, 7 * MS));
    });
    // 6: a full table
    fixed(tr, 6, false, |net, r| {
        for id in [2, 3, 4] {
            r.add(net, id, true, false);
        }
        r.add(net, 5, false, false);
        r.chal(net, 6);
        r.data(net, 6, true, false);
        r.remove(net, 4);
        r.add(net, 5, false, false);
        r.add(net, 6, false, false);
    });
    // 7: following the peer
    fixed(tr, 7, false, |net, r| {
        r.add(net, 2, true, false);
        r.adv(5 * MS);
        r.data(net, 2, true, false);
        r.adv(5 * MS);
        r.data(net, 2, true, true);
        r.adv(5 * MS);
        r.data(net, 1, false, false).expect("an older packet number is free");
        r.adv(5 * MS);
        r.data(net, 1, true, false);
        r.adv(5 * MS);
        r.data(net, 3, true, false);
    });
    // 8: the idle boundary
    fixed(tr, 8, false, |net, r| {
        r.add(net, 2, true, false);
        r.data(net, 1, true, false);
        let t = r.now;
        r.timer_at(net, t + IDLE);
        assert!(validated(net, 1), "a path silent for exactly 15 s is still validated");
        r.timer_at(net, t + IDLE + 1);
        assert!(!validated(net, 1), "a path silent for more than 15 s is validated");
        assert_eq!(active(net), 2);
        r.data(net, 1, true, false);
        r.send_all(net);
        r.answer(net, 1);
    });
    // 9: three probe timeouts with a relayed path
    fixed(tr, 9, false, |net, r| {
        r.add(net, 2, true, false);
        flight(net, 1000);
        r.send_all(net);
        r.until_pto(net, 3);
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(2)),
            "three probe timeouts fail over to the relayed path"
        );
        for _ in 0..2 {
            r.timer_next(net);
            r.send_all(net);
        }
        r.data(net, 1, true, false);
        r.send_all(net);
        r.answer(net, 1);
    });
    // 10: three probe timeouts with no relayed path
    fixed(tr, 10, false, |net, r| {
        flight(net, 1000);
        r.send_all(net);
        r.until_pto(net, 3);
        for _ in 0..2 {
            r.timer_next(net);
            r.send_all(net);
        }
        r.data(net, 1, true, false);
        r.send_all(net);
        r.answer(net, 1);
    });
    // 11: followed onto an unvalidated path, and no fall back
    fixed(tr, 11, false, |net, r| {
        r.add(net, 2, true, false);
        r.data(net, 3, true, false);
        flight(net, 1000);
        r.send_all(net);
        r.until_pto(net, 4);
    });
    // 12: lost
    fixed(tr, 12, false, |net, r| {
        r.lost(net, 1);
        r.add(net, 2, true, false);
        r.timer_next(net);
        r.add(net, 3, false, false);
        r.send_all(net);
        r.answer(net, 3);
    });
    // 13: gone
    fixed(tr, 13, false, |net, r| {
        r.add(net, 2, true, false);
        r.set(net, 2);
        let t = r.now;
        r.timer_at(net, t + 16 * SEC);
        r.lost(net, 2);
        r.set(net, 1);
        r.punch(net);
        flight(net, 1000);
        r.send_all(net);
        r.answer(net, 1);
        r.until_pto(net, 3);
    });
    // 14: path info
    fixed(tr, 14, false, |net, r| {
        r.add(net, 2, false, false);
        r.info(net, 2, true, false);
        r.info(net, 2, false, true);
        r.info(net, 1, true, false);
        r.info(net, 1, true, false);
    });
    // 15: punch
    fixed(tr, 15, false, |net, r| {
        r.add(net, 2, false, false);
        r.add(net, 3, false, false);
        r.lost(net, 3);
        r.punch(net);
    });
    // 16: a thin session re-joins a path that idled out
    fixed(tr, 16, true, |net, r| {
        r.add(net, 2, true, false);
        r.data(net, 1, true, false);
        let t = r.now;
        r.timer_at(net, t + IDLE + 1);
        let floor = r.now + 10 * SEC;
        PmRun::rejoin_floor(net, 1, floor);
        r.timer_next(net);
        PmRun::rejoin_floor(net, 1, 0);
        r.timer_next(net);
        r.send_all(net);
        assert!(r.returned(net, 1, 7 * MS), "a re-joined path that answers is validated");
        assert!(
            !r.returned(net, 1, 7 * MS),
            "a path already validated is not returned twice"
        );
    });
    // 17: a thin node declared thin does not challenge back
    fixed(tr, 17, true, |net, r| {
        r.add(net, 2, true, false);
        r.set(net, 2);
        r.chal(net, 3);
        r.add(net, 4, false, false);
        r.send_all(net);
        r.adv(5 * MS);
        r.data(net, 4, true, false);
    });
    // 18: a session that moved application data challenges back, once
    fixed(tr, 18, false, |net, r| {
        r.add(net, 2, true, false);
        r.set(net, 2);
        flight(net, 100);
        r.send_all(net);
        r.chal(net, 3);
        r.chal(net, 3);
    });
}

fn random_runs(tr: &mut PmTrace) {
    for k in 0..40u32 {
        with_net(k % 4 == 3, 6000 + u64::from(k), |net| {
            let mut r = PmRun::new(tr, 100 + k, net, 0x504D_0001 + u64::from(k));
            flight(net, 500);
            let start = r.now;
            for _ in 0..60 {
                if !r.live || r.now - start >= 60 * SEC {
                    break;
                }
                if !r.random_step(net, start) {
                    let gap = 1 + r.rng.next_u64() % 40;
                    r.adv(gap * MS);
                }
            }
        });
    }
}

#[test]
fn path_moves_match_the_model() {
    big_stack(|| {
        let mut tr = PmTrace::default();
        fixed_runs(&mut tr);
        random_runs(&mut tr);
        for op in [
            "init", "add", "rebind", "remove", "lost", "set", "info", "probe", "punch", "returned", "resp", "chal",
            "data", "send", "timer",
        ] {
            assert!(tr.seen.contains(op), "no `{op}` event was recorded");
        }
        for r in [
            "ok",
            "toomany",
            "unknown",
            "exists",
            "active",
            "notvalidated",
            "nopath",
            "true",
            "false",
        ] {
            assert!(tr.seen.contains(&format!("r:{r}")), "no event had the result `{r}`");
        }
        for s in ["pto3", "pto4", "thin", "nonthin"] {
            assert!(tr.seen.contains(s), "no timer event of kind `{s}`");
        }
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("path_move.ndjson"), &tr.out).unwrap();
        }
    });
}
