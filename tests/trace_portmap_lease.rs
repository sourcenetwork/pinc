//! Trace generation for the lease of one port mapping: a real `PortMap` (`pinc-portmap`, built with the `trace`
//! feature) over PCP, driven by a test that is the gateway and the network of `proofs/tla/PortMapLease.tla`. The test
//! keeps the gateway's state (its boot, whether it holds the mapping and until when, the datagrams in flight) and
//! drives the client one model action at a time: a request given out, the gateway's grant or refusal, an announce or
//! a spoofed one, a restart, a lost datagram, a tick of the clock, a timer call, stop. Every event is a line of
//! `portmap/lease.ndjson` for the TLA+ trace check (`TracePortMapLease.tla`): the gateway's and the network's state
//! from the test's own bookkeeping, the client's from the `trace` probe, every time in ticks of 5 s.
//!
//! The rules that keep every time on a tick (the header of `TracePortMapLease.tla`) are the test's: the gateway answers
//! only the first try of a round, at once; a refusal comes only when no restart has been missed and, in a renewal, only
//! when the lease has an even number of ticks left; answers are taken only while the client asks. Ten scripted runs
//! make each case the model names, 64 seeded runs of up to 150 events choose among the actions the rules allow.
//!
//! The test asserts the facts it relies on itself: every time is on a tick, a held lease ends one lifetime after it
//! started and is renewed half way unless an announce or a refusal moved it, a spoofed announce never takes the mapping
//! out of the record, a grant starts the lease at the tick of its request, and stop drops the mapping and gives out
//! the release. The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is
//! written.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::many_single_char_names,
    clippy::match_same_arms,
    clippy::struct_excessive_bools,
    clippy::unused_self
)]

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_portmap::lease::SEC;
use pinc_portmap::{Config, MAX_DATAGRAM, PortMap, pcp};
use pinc_tests::SplitMix64;

const TICK: u64 = 5 * SEC;
/// The lease in ticks: `cfg.lifetime` of 40 s.
const L: i64 = 8;
const GATEWAY: SocketAddr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)), 5351);
const NONCE: [u8; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

/// A time in ticks; a time off the tick is a break of the driving rules.
fn tk(ns: u64) -> i64 {
    assert_eq!(ns % TICK, 0, "a time off the tick: {ns} ns");
    i64::try_from(ns / TICK).unwrap()
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Act {
    Tick,
    /// The gateway takes the first try and grants; whether the answer is lost.
    Grant {
        lose_resp: bool,
    },
    Refuse,
    LoseReq,
    GwAnnounce,
    Spoof,
    Deliver,
    LoseResp,
    Restart,
    Stop,
    GwRelease,
    /// Ticks on until something other than the tick happens.
    Wait,
}

/// An answer in flight: kind, epoch in seconds, boot tick.
type Msg = (&'static str, u64, u64);

struct Run<'a> {
    pm: PortMap,
    tick: u64,
    t: u64,
    boot: u64,
    restarts: u32,
    gmap: bool,
    gexp: u64,
    req: BTreeSet<&'static str>,
    resp: BTreeSet<Msg>,
    /// The first try of a round is out and the gateway has not answered it.
    pending: bool,
    stopped: bool,
    expect_release: bool,
    /// A gateway restart the client has not noted an epoch since.
    unheard: bool,
    moved: bool,
    /// A request the test saw go out has no answer yet: a round is in flight.
    round: bool,
    /// An announce (the nonce is not checked, so a spoofed one counts) reached the client while a round (an ask or a renewal) was in flight: it is kept for after
    /// the round.
    kept_announce: bool,
    last_renew: i64,
    last_exp: i64,
    events: u32,
    post_stop: u32,
    rng: Option<SplitMix64>,
    out: &'a mut String,
}

impl<'a> Run<'a> {
    fn new(out: &'a mut String, rng: Option<SplitMix64>) -> Self {
        let mut cfg = Config::new(
            Some(GATEWAY.ip()),
            SocketAddr::from((Ipv4Addr::new(203, 0, 113, 5), 65534)),
            NONCE,
        );
        cfg.lifetime = 40;
        let mut r = Run {
            pm: PortMap::new(cfg, 0),
            tick: 0,
            t: 0,
            boot: 0,
            restarts: 0,
            gmap: false,
            gexp: 0,
            req: BTreeSet::new(),
            resp: BTreeSet::new(),
            pending: false,
            stopped: false,
            expect_release: false,
            unheard: false,
            moved: false,
            round: false,
            kept_announce: false,
            last_renew: 0,
            last_exp: 0,
            events: 0,
            post_stop: 0,
            rng,
            out,
        };
        r.rec("new");
        r.settle();
        r
    }

    fn rec(&mut self, ev: &str) {
        let p = self.pm.probe();
        if let Some((_, r, e)) = p.held {
            (self.last_renew, self.last_exp) = (tk(r), tk(e));
            assert!(self.last_renew <= self.last_exp, "a lease is renewed after it ends");
            if p.step == "held" && !self.moved {
                let s = tk(p.started);
                assert_eq!(
                    self.last_exp - s,
                    L,
                    "a lease does not end one lifetime after it started"
                );
                assert_eq!(self.last_renew - s, L / 2, "a lease is not renewed half way");
            }
        }
        let cstep = match p.step {
            "pcp" => "ask",
            "held" => "held",
            "stopped" => "stopped",
            _ => "idle",
        };
        let tries = if p.step == "pcp" { p.tries - u8::from(p.send) } else { 0 };
        let (prev_at, prev_srv) = p.epoch.map_or((-1, 0), |(at, s)| (tk(at), i64::from(s)));
        let req: Vec<String> = self.req.iter().map(|r| format!("\"{r}\"")).collect();
        let resp: Vec<String> = self
            .resp
            .iter()
            .map(|(k, e, b)| format!(r#"{{"k":"{k}","e":{e},"b":{b}}}"#))
            .collect();
        let _ = writeln!(
            self.out,
            r#"{{"ev":"{ev}","now":{},"boot":{},"restarts":{},"gmap":{},"gexp":{},"req":[{}],"resp":[{}],"cstep":"{cstep}","tries":{tries},"renewing":{},"pub":{},"started":{},"renewAt":{},"cexp":{},"prevAt":{prev_at},"prevSrv":{prev_srv},"floorEnd":{},"annNext":{}}}"#,
            self.tick,
            self.boot,
            self.restarts,
            self.gmap,
            self.gexp,
            req.join(","),
            resp.join(","),
            p.renewing,
            p.held.is_some(),
            tk(p.started),
            self.last_renew,
            self.last_exp,
            tk(p.floor_end),
            p.announce_next.map_or(-1, tk),
        );
        self.events += 1;
    }

    /// The gateway's epoch now, in seconds.
    fn epoch_now(&self) -> u64 {
        (self.tick - self.boot) * 5
    }

    fn bytes(&self, m: Msg) -> Vec<u8> {
        let (k, e, _) = m;
        let epoch = u32::try_from(e).unwrap();
        let map = |result: u8, lifetime: u32| pcp::Response::Map {
            result,
            lifetime,
            epoch,
            nonce: NONCE,
            protocol: pcp::UDP,
            internal_port: 65534,
            external_port: 40000,
            external_ip: Ipv4Addr::new(198, 51, 100, 7).into(),
        };
        let r = match k {
            "grant" => map(0, 40),
            "refuse" => map(8, 0),
            "announce" => pcp::Response::Header {
                opcode: pcp::OP_ANNOUNCE,
                result: 0,
                lifetime: 0,
                epoch,
            },
            _ => panic!("an answer the test does not know: {k}"),
        };
        let mut buf = [0u8; MAX_DATAGRAM];
        let n = pcp::encode_response(&r, &mut buf).unwrap();
        buf[..n].to_vec()
    }

    /// Whether to lose (not leave in flight) a later try's request.
    fn lose_later(&mut self) -> bool {
        self.rng.as_mut().is_none_or(|r| r.next_u64() % 2 == 0)
    }

    /// Run what the host does by itself: give out what is due and call `handle_timeout` when it is due in this tick,
    /// until a choice is left (the gateway's answer to a first try, or free time).
    fn settle(&mut self) {
        for _ in 0..1000 {
            if self.pending && !self.req.contains("map") {
                self.pending = false;
            }
            if self.pending {
                return;
            }
            let p = self.pm.probe();
            if p.send || p.releases.iter().any(Option::is_some) {
                let mut buf = [0u8; MAX_DATAGRAM];
                if let Some((to, n)) = self.pm.poll_datagram(&mut buf) {
                    assert_eq!(to, GATEWAY, "a datagram to somewhere else than the gateway");
                    let request = (buf[0] == 2).then(|| pcp::decode_request(&buf[..n]).unwrap());
                    match request {
                        Some(r) if r.lifetime == 0 => {
                            assert!(self.expect_release, "a release for a mapping that was not held");
                            self.rec("out");
                        }
                        Some(_) => {
                            self.round = true;
                            self.req.insert("map");
                            self.rec("send");
                            if self.pm.probe().tries == 1 {
                                self.pending = true;
                            } else if self.lose_later() {
                                self.req.remove("map");
                                self.rec("lose_req");
                            }
                        }
                        None => self.rec("out"),
                    }
                    continue;
                }
            }
            let idle = p.step == "idle";
            if let Some(d) = self.pm.poll_timeout() {
                let end = (self.tick + 1) * TICK;
                if (idle && d <= self.tick * TICK) || (!idle && d < end) {
                    self.t = if idle {
                        (self.tick * TICK).max(self.t)
                    } else {
                        d.max(self.t)
                    };
                    self.pm.handle_timeout(self.t);
                    self.rec("timer");
                    continue;
                }
            }
            return;
        }
        panic!("the host's work does not end");
    }

    fn announce_in_flight(&self) -> bool {
        self.resp.iter().any(|m| m.0 == "announce")
    }

    /// The actions the rules allow now.
    fn options(&self) -> Vec<Act> {
        let p = self.pm.probe();
        let mut o = Vec::new();
        if self.stopped {
            o.push(Act::Tick);
            if self.req.contains("release") {
                o.push(Act::GwRelease);
            }
            if !self.req.is_empty() {
                o.push(Act::LoseReq);
            }
            return o;
        }
        if self.pending {
            o.push(Act::Grant { lose_resp: false });
            let renewing = p.renewing;
            if !renewing {
                o.push(Act::Grant { lose_resp: true });
                o.push(Act::LoseReq);
            }
            let even_left = p.held.is_none_or(|(_, _, e)| {
                let left = tk(e) - i64::try_from(self.tick).unwrap();
                left >= 2 && left % 2 == 0
            });
            if !self.unheard && (!renewing || even_left) {
                o.push(Act::Refuse);
            }
            if !renewing && self.tick > self.boot {
                o.push(Act::Restart);
            }
        } else {
            if p.step != "pcp" {
                o.push(Act::Tick);
            }
            if self.tick > self.boot {
                o.push(Act::Restart);
            }
            if self.req.contains("release") {
                o.push(Act::GwRelease);
            }
            if !self.req.is_empty() {
                o.push(Act::LoseReq);
            }
        }
        o.push(Act::Stop);
        if self.announce_in_flight() {
            if self.t % TICK == 0 {
                o.push(Act::Deliver);
            }
            o.push(Act::LoseResp);
        } else {
            o.push(Act::GwAnnounce);
            o.push(Act::Spoof);
        }
        o
    }

    fn weight(a: Act) -> u64 {
        match a {
            Act::Tick => 4,
            Act::Grant { lose_resp: false } => 6,
            Act::Refuse | Act::Deliver => 3,
            Act::Grant { .. } | Act::LoseReq | Act::GwAnnounce | Act::Spoof | Act::LoseResp | Act::Restart => 1,
            Act::GwRelease => 3,
            Act::Stop => 1,
            Act::Wait => 0,
        }
    }

    fn deliver_map(&mut self, m: Msg) {
        let before = self.pm.probe();
        let bytes = self.bytes(m);
        self.pm.handle_datagram(self.t, GATEWAY, &bytes);
        self.resp.remove(&m);
        let after = self.pm.probe();
        if after.epoch != before.epoch {
            self.unheard = false;
        }
        match m.0 {
            "grant" => {
                assert!(after.held.is_some(), "a grant leaves no mapping held");
                assert_eq!(
                    tk(after.started),
                    i64::try_from(self.tick).unwrap(),
                    "a lease did not start at its request"
                );
                self.round = false;
                self.moved = std::mem::take(&mut self.kept_announce);
            }
            "refuse" => {
                self.moved = true;
                self.round = false;
                self.kept_announce = false;
            }
            _ => {
                if m.1 == 0 && before.held.is_some() {
                    assert!(
                        after.held.is_some(),
                        "a spoofed announce took the mapping out of the record"
                    );
                }
                self.moved |= before.held.is_some();
                self.kept_announce |= self.round && before.step == "pcp";
            }
        }
        self.rec("deliver");
    }

    fn apply(&mut self, a: Act) {
        assert!(
            self.options().contains(&a) || a == Act::Wait,
            "the script asks for {a:?}, which the rules do not allow now"
        );
        let (tick, boot) = (self.tick, self.boot);
        match a {
            Act::Tick => {
                self.tick += 1;
                self.t = self.tick * TICK;
                self.req.clear();
                self.resp.clear();
                self.rec("tick");
            }
            Act::Grant { lose_resp } => {
                self.req.remove("map");
                self.pending = false;
                self.gmap = true;
                self.gexp = tick + u64::try_from(L).unwrap();
                let m = ("grant", self.epoch_now(), boot);
                self.resp.insert(m);
                self.rec("gw_grant");
                if lose_resp {
                    self.resp.remove(&m);
                    self.rec("lose_resp");
                } else {
                    self.deliver_map(m);
                }
            }
            Act::Refuse => {
                self.req.remove("map");
                self.pending = false;
                let m = ("refuse", self.epoch_now(), boot);
                self.resp.insert(m);
                self.rec("gw_refuse");
                self.deliver_map(m);
            }
            Act::LoseReq => {
                let r = self.req.iter().next().copied().unwrap();
                self.req.remove(r);
                self.rec("lose_req");
            }
            Act::GwAnnounce => {
                self.resp.insert(("announce", self.epoch_now(), boot));
                self.rec("gw_announce");
            }
            Act::Spoof => {
                self.resp.insert(("announce", 0, boot));
                self.rec("spoof");
            }
            Act::Deliver => {
                let m = *self.resp.iter().find(|m| m.0 == "announce").unwrap();
                self.deliver_map(m);
            }
            Act::LoseResp => {
                let m = *self.resp.iter().find(|m| m.0 == "announce").unwrap();
                self.resp.remove(&m);
                self.rec("lose_resp");
            }
            Act::Restart => {
                self.boot = tick;
                self.restarts += 1;
                self.gmap = false;
                self.req.clear();
                self.resp.clear();
                self.unheard = true;
                self.rec("gw_restart");
            }
            Act::Stop => {
                // A release goes out for a held mapping and for a round in flight, which may have made one.
                let pre = self.pm.probe();
                let held = pre.held.is_some() || pre.step == "pcp";
                self.pm.stop(self.t);
                if held {
                    self.req.insert("release");
                }
                self.stopped = true;
                self.pending = false;
                self.expect_release = held;
                let p = self.pm.probe();
                assert!(
                    p.held.is_none() && p.step == "stopped",
                    "stop leaves a mapping held or the client running"
                );
                self.rec("stop");
            }
            Act::GwRelease => {
                self.req.remove("release");
                self.gmap = false;
                self.rec("gw_release");
            }
            Act::Wait => {
                for _ in 0..200 {
                    if !self.options().contains(&Act::Tick) {
                        break;
                    }
                    let before = self.events;
                    self.apply(Act::Tick);
                    self.settle();
                    if self.events - before > 1 {
                        break;
                    }
                }
                return;
            }
        }
        self.settle();
        if self.stopped {
            self.post_stop += 1;
        }
    }

    fn script(&mut self, acts: &[Act]) {
        for a in acts {
            self.apply(*a);
        }
        if self.stopped {
            assert!(
                self.pm.poll_datagram(&mut [0u8; MAX_DATAGRAM]).is_none(),
                "the release was not all given out"
            );
        }
    }

    fn random(&mut self) {
        while self.events < 150 && self.post_stop < 6 {
            let o = self.options();
            let total: u64 = o.iter().map(|a| Self::weight(*a)).sum();
            let mut r = self.rng.as_mut().unwrap().next_u64() % total;
            let a = *o
                .iter()
                .find(|a| {
                    let w = Self::weight(**a);
                    if r < w {
                        true
                    } else {
                        r -= w;
                        false
                    }
                })
                .unwrap();
            self.apply(a);
        }
    }
}

const G: Act = Act::Grant { lose_resp: false };

fn scripted() -> Vec<Vec<Act>> {
    use Act::{Deliver, GwAnnounce, GwRelease, LoseReq, Refuse, Restart, Spoof, Stop, Tick, Wait};
    vec![
        // a grant, then two renewals
        vec![G, Wait, G, Wait, G, Tick, Tick],
        // an announce while held brings the renewal forward
        vec![G, Tick, GwAnnounce, Deliver, G, Wait, G],
        // two announces inside the floor
        vec![
            G, Tick, GwAnnounce, Deliver, G, GwAnnounce, Deliver, Tick, Tick, G, Wait, G,
        ],
        // an announce while a renewal is in flight, kept for after it
        vec![G, Tick, Tick, Tick, Tick, GwAnnounce, Deliver, G, Wait, G],
        // a spoofed announce while held
        vec![G, Tick, Spoof, Deliver, G, Wait, G],
        // a gateway restart, then a renewal granted with the new epoch
        vec![G, Tick, Tick, Restart, Tick, Tick, G, Wait, G],
        // a refused renewal, renewed half way
        vec![G, Wait, Refuse, Wait, G, Wait, G],
        // a PCP round lost whole, NAT-PMP silent, the RETRY wait and PCP again
        vec![LoseReq, Wait, G, Wait, G],
        // stop while held
        vec![G, Tick, Stop, GwRelease, Tick],
        // stop while asking
        vec![Stop, Tick],
    ]
}

#[test]
fn lease_trace() {
    let mut out = String::new();
    for acts in scripted() {
        Run::new(&mut out, None).script(&acts);
    }
    for seed in 0..64u64 {
        let mut run = Run::new(&mut out, Some(SplitMix64::traced(0x5750_0100 + seed)));
        run.random();
    }
    assert!(out.lines().count() > 1000);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("portmap");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("lease.ndjson"), &out).unwrap();
    }
}
