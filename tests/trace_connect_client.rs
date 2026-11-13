//! Trace generation for the client rules of connectivity: seeded random calls of the real punch timer and probe gaps,
//! the hub tunnel decisions and splice tables, the first-flight selection and pending dials, the lookup table and the
//! verification of an answer, address classification and the probe state, recorded as ndjson (`connect_client.ndjson`)
//! for the TLA+ trace check (`TraceConnectClient.tla`) and the Lean replay (`Vinc/TraceConnectClient.lean`).
//!
//! Every event is one call with its arguments and its answer; a stateful structure is read back after each call
//! through its public accessors (the deadline, the round trips, the ages, the peers waiting), so the model must agree
//! on the state as well as on the answer. Instants are whole milliseconds, recorded in microseconds; nodes and
//! addresses are small numbers (the node `k` is `[k; 32]`, the address `k` is `10.0.0.k:k`).
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    unreachable_pub
)]

#[allow(dead_code)]
mod connect_codec_out;
mod connect_common;

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use connect_common::nid;
use vinc_connect::carrier::frame::DnsAnswer;
use vinc_connect::client::dial::{self, Cand, Pending, RelayView, Try};
use vinc_connect::client::lookup::{Ask, LookupError, Lookups, verify};
use vinc_connect::client::netcheck::{HomeStep, Netcheck, Observed, classify};
use vinc_connect::client::punch::{self, Puncher, Step, View};
use vinc_connect::client::tunnel::{self, Rides, Splices, ThinSplice, Via};
use vinc_connect::record::{Reach, Record, RecordFields};
use vinc_crypto::NodeId;
use vinc_tests::SplitMix64;

const MS: u64 = 1_000_000;
const S: u64 = 1_000_000_000;

fn us(ns: u64) -> u64 {
    assert_eq!(ns % 1000, 0, "{ns} ns is not whole microseconds");
    ns / 1000
}

fn addr(k: u16) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 0, 0, k as u8)), k)
}

fn opt_us(o: Option<u64>) -> i64 {
    o.map_or(-1, |v| us(v) as i64)
}

/// A deadline one nanosecond past a whole microsecond (`at + 1`) is recorded rounded up: every reading of the clock is
/// a whole number of microseconds, so the two are the same instant for the machine.
fn opt_ceil(o: Option<u64>) -> i64 {
    o.map_or(-1, |v| v.div_ceil(1000) as i64)
}

fn pick<T: Copy>(rng: &mut SplitMix64, v: &[T]) -> T {
    v[(rng.next_u64() % v.len() as u64) as usize]
}

fn bytes(v: &[u8]) -> String {
    format!("[{}]", v.iter().map(ToString::to_string).collect::<Vec<_>>().join(","))
}

fn jlist<T: ToString>(v: impl Iterator<Item = T>) -> String {
    format!("[{}]", v.map(|x| x.to_string()).collect::<Vec<_>>().join(","))
}

fn times(rng: &mut SplitMix64, now: u64) -> u64 {
    let deltas: [u64; 14] = [
        0,
        MS,
        100 * MS,
        600 * MS,
        S,
        2 * S,
        4 * S,
        5 * S,
        10 * S,
        15 * S,
        20 * S,
        30 * S,
        60 * S,
        61 * S,
    ];
    if rng.next_u64().is_multiple_of(9) && now > 100 * S {
        now - pick(rng, &deltas)
    } else {
        now + pick(rng, &deltas)
    }
}

fn punch_events(out: &mut Vec<String>) {
    for srtt in [0, MS, 8 * MS, 100 * MS, 264 * MS, 800 * MS, 2 * S, 16 * S] {
        out.push(format!(
            r#"{{"t":"cl","m":"gaps","srtt":{},"out":{}}}"#,
            us(srtt),
            jlist(punch::probe_gaps(srtt).iter().map(|g| us(*g)))
        ));
    }
    let mut rng = SplitMix64::new(0x9C);
    for _ in 0..40 {
        let mut p = Puncher::off();
        let mut now = pick(&mut rng, &[0, 5 * S]);
        out.push(r#"{"t":"cl","m":"pnew"}"#.to_string());
        for _ in 0..60 {
            now = times(&mut rng, now);
            let r = rng.next_u64() % 10;
            let line = match r {
                0..=1 => {
                    p.established(now);
                    format!(
                        r#"{{"t":"cl","m":"puncher","c":"est","now":{},"res":"none","at":{}}}"#,
                        us(now),
                        opt_ceil(p.deadline())
                    )
                }
                2 => {
                    let at = pick(&mut rng, &[0, now, now + 100 * MS, now + 60 * S]);
                    p.arm(at);
                    format!(
                        r#"{{"t":"cl","m":"puncher","c":"arm","now":{},"arg":{},"res":"none","at":{}}}"#,
                        us(now),
                        us(at),
                        opt_ceil(p.deadline())
                    )
                }
                _ => {
                    let v = View {
                        app_idle: pick(&mut rng, &[0, 19 * S, 20 * S, 21 * S, 100 * S]),
                        direct: rng.next_u64().is_multiple_of(2),
                        rtt: pick(&mut rng, &[0, MS, 10 * MS, 10 * MS + 1000, 50 * MS]),
                        quiet_until: pick(&mut rng, &[0, now, now + 5 * S, now.saturating_sub(S)]),
                    };
                    let step = p.due(now, &v);
                    let res = match step {
                        Step::Punch => "punch",
                        Step::Wait => "wait",
                    };
                    format!(
                        r#"{{"t":"cl","m":"puncher","c":"due","now":{},"view":{{"idle":{},"direct":{},"rtt":{},"quiet":{}}},"res":"{res}","at":{}}}"#,
                        us(now),
                        us(v.app_idle),
                        v.direct,
                        us(v.rtt),
                        us(v.quiet_until),
                        opt_ceil(p.deadline())
                    )
                }
            };
            out.push(line);
        }
    }
}

fn tunnel_events(out: &mut Vec<String>) {
    let mut rng = SplitMix64::new(0x7A);
    let silents = [0, 14 * S, 15 * S, 15 * S + MS, 40 * S];
    for _ in 0..3000 {
        let carrier_open = rng.next_u64().is_multiple_of(2);
        let silent_for = pick(&mut rng, &silents);
        let tunnel = !rng.next_u64().is_multiple_of(4);
        let session = (!rng.next_u64().is_multiple_of(3)).then(|| Rides {
            pto_count: (rng.next_u64() % 4) as u32,
            handshaking: rng.next_u64().is_multiple_of(2),
            hs_tries: (rng.next_u64() % 4) as u32,
            thin: rng.next_u64().is_multiple_of(2),
        });
        let via = tunnel::decide(carrier_open, silent_for, session, tunnel);
        let res = match via {
            Via::Carrier => "carrier",
            Via::Tunnel => "tunnel",
            Via::Both => "both",
        };
        let sess = session.map_or(
            r#"{"has":false,"pto":0,"hs":false,"tries":0,"thin":false}"#.to_string(),
            |s| {
                format!(
                    r#"{{"has":true,"pto":{},"hs":{},"tries":{},"thin":{}}}"#,
                    s.pto_count, s.handshaking, s.hs_tries, s.thin
                )
            },
        );
        out.push(format!(
            r#"{{"t":"cl","m":"decide","open":{carrier_open},"silent":{},"session":{sess},"tunnel":{tunnel},"res":"{res}"}}"#,
            us(silent_for)
        ));
        let t = ThinSplice {
            thin: !rng.next_u64().is_multiple_of(4),
            established: !rng.next_u64().is_multiple_of(4),
            splice_age: (!rng.next_u64().is_multiple_of(4))
                .then(|| pick(&mut rng, &[0, 3999 * MS, 4 * S, 5 * S, 9 * S])),
            rtt: pick(&mut rng, &[0, S, 2 * S, 3 * S]),
            carrier_fresh: rng.next_u64().is_multiple_of(2),
            tunnel_took: !rng.next_u64().is_multiple_of(4),
            pto_count: (rng.next_u64() % 4) as u32,
        };
        out.push(format!(
            r#"{{"t":"cl","m":"thin","thin":{},"est":{},"age":{},"rtt":{},"fresh":{},"took":{},"pto":{},"res":{}}}"#,
            t.thin,
            t.established,
            opt_us(t.splice_age),
            us(t.rtt),
            t.carrier_fresh,
            t.tunnel_took,
            t.pto_count,
            tunnel::thin_splice(&t)
        ));
        let heard = pick(&mut rng, &[0, 5 * S, 20 * S]);
        let now = pick(&mut rng, &[0, 10 * S, 25 * S, 40 * S]);
        let hub = tunnel::HubSession {
            validated_direct: rng.next_u64().is_multiple_of(2),
            heard,
            remote: addr(1),
        };
        out.push(format!(
            r#"{{"t":"cl","m":"hubok","valid":{},"heard":{},"now":{},"res":{}}}"#,
            hub.validated_direct,
            us(heard),
            us(now),
            tunnel::hub_ok(&hub, now)
        ));
    }
    for _ in 0..60 {
        let mut sp: Splices<3, 2> = Splices::new();
        let mut now = 0u64;
        out.push(r#"{"t":"cl","m":"snew","p":3,"r":2}"#.to_string());
        for _ in 0..50 {
            now = times(&mut rng, now);
            let relay = (rng.next_u64() % 3) as u8;
            let peer = (rng.next_u64() % 5) as u8 + 1;
            let port = (rng.next_u64() % 4) as u16 + 1;
            if rng.next_u64().is_multiple_of(2) {
                sp.seen(now, relay, nid(peer), addr(port));
                out.push(format!(
                    r#"{{"t":"cl","m":"seen","now":{},"relay":{relay},"peer":{peer},"from":{port}}}"#,
                    us(now)
                ));
            }
            let rtt = pick(&mut rng, &[0, S, 20 * S]);
            let ages: Vec<i64> = (1..=5u8)
                .flat_map(|p| (0..2u8).map(move |r| (p, r)))
                .map(|(p, r)| opt_us(sp.age(now, r, &nid(p))))
                .collect();
            let lives: Vec<i64> = (0..2u8)
                .map(|r| sp.live(now, r, rtt).map_or(-1, |a| i64::from(a.port())))
                .collect();
            out.push(format!(
                r#"{{"t":"cl","m":"sview","now":{},"rtt":{},"ages":{},"lives":{}}}"#,
                us(now),
                us(rtt),
                jlist(ages.iter()),
                jlist(lives.iter())
            ));
        }
    }
}

fn dial_events(out: &mut Vec<String>) {
    let mut rng = SplitMix64::new(0xD1);
    for _ in 0..2000 {
        let first_try = rng.next_u64().is_multiple_of(2);
        let is_hub = rng.next_u64().is_multiple_of(2);
        let fd = pick(&mut rng, &[0, 5 * S, 10 * S, 11 * S, 100 * S]);
        let started = pick(&mut rng, &[0, 5 * S]);
        out.push(format!(
            r#"{{"t":"cl","m":"direct","first":{first_try},"hub":{is_hub},"fd":{},"started":{},"res":{}}}"#,
            us(fd),
            us(started),
            dial::direct_first(first_try, is_hub, fd, started)
        ));
    }
    for _ in 0..4000 {
        let n = (rng.next_u64() % 7) as usize;
        let cands: Vec<Cand> = (0..n)
            .map(|_| {
                if rng.next_u64().is_multiple_of(2) {
                    Cand::Udp(addr((rng.next_u64() % 5) as u16 + 1))
                } else {
                    Cand::Relay((rng.next_u64() % 3) as u8)
                }
            })
            .collect();
        let views: Vec<Option<RelayView>> = (0..3)
            .map(|_| {
                (!rng.next_u64().is_multiple_of(4)).then(|| RelayView {
                    live: !rng.next_u64().is_multiple_of(3),
                    generation: rng.next_u64() % 3,
                })
            })
            .collect();
        let now = pick(&mut rng, &[0, 10 * S, 40 * S, 100 * S]);
        let link_rtt = pick(&mut rng, &[0, 100 * MS, 249 * MS, 250 * MS, S, 5 * S, 20 * S]);
        let t = Try {
            now,
            dialer: !rng.next_u64().is_multiple_of(4),
            tries: (rng.next_u64() % 6) as u32,
            link_rtt,
            no_rtt: rng.next_u64().is_multiple_of(2),
            hs0: rng.next_u64().is_multiple_of(3),
            last_relay: (rng.next_u64().is_multiple_of(2)).then(|| {
                (
                    (rng.next_u64() % 3) as u8,
                    rng.next_u64() % 3,
                    pick(&mut rng, &[0, 5 * S, 9 * S, 10 * S, 30 * S, 39 * S, 100 * S]),
                )
            }),
        };
        let cap = 1 + (rng.next_u64() % 4) as usize;
        let mut buf = vec![Cand::Relay(0); cap];
        let (m, carried) = dial::select(&cands, &t, |r| views.get(usize::from(r)).copied().flatten(), &mut buf);
        let cj = |c: &Cand| match c {
            Cand::Udp(a) => format!(r#"["u",{}]"#, a.port()),
            Cand::Relay(r) => format!(r#"["r",{r}]"#),
        };
        let vj = |v: &Option<RelayView>| {
            v.map_or(r#"{"some":false,"live":false,"gen":0}"#.to_string(), |v| {
                format!(r#"{{"some":true,"live":{},"gen":{}}}"#, v.live, v.generation)
            })
        };
        out.push(format!(
            r#"{{"t":"cl","m":"select","cands":[{}],"views":[{}],"try":{{"now":{},"dialer":{},"tries":{},"rtt":{},"nortt":{},"hs0":{},"haslast":{},"last":{}}},"cap":{cap},"out":[{}],"carried":{}}}"#,
            cands.iter().map(cj).collect::<Vec<_>>().join(","),
            views.iter().map(vj).collect::<Vec<_>>().join(","),
            us(t.now),
            t.dialer,
            t.tries,
            us(t.link_rtt),
            t.no_rtt,
            t.hs0,
            t.last_relay.is_some(),
            t.last_relay.map_or("[0,0,0]".to_string(), |(r, g, a)| format!("[{r},{g},{}]", us(a))),
            buf[..m].iter().map(cj).collect::<Vec<_>>().join(","),
            carried.map_or("[]".to_string(), |(r, g)| format!("[{r},{g}]"))
        ));
    }
    for _ in 0..80 {
        let mut p: Pending<u32, 3, 2> = Pending::new();
        out.push(r#"{"t":"cl","m":"pnew3","n":3,"h":2}"#.to_string());
        for _ in 0..60 {
            let peer = (rng.next_u64() % 5) as u8 + 1;
            let line = match rng.next_u64() % 10 {
                0..=4 => {
                    let s = (rng.next_u64() % 5) as u32;
                    let ok = p.add(nid(peer), s);
                    format!(r#"{{"t":"cl","m":"padd","peer":{peer},"s":{s},"res":{ok}"#)
                }
                5..=6 => {
                    let w = p.take(&nid(peer));
                    format!(
                        r#"{{"t":"cl","m":"ptake","peer":{peer},"res":[{}]"#,
                        w.iter()
                            .map(|x| x.map_or("-1".to_string(), |v| v.to_string()))
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                }
                _ => {
                    let keep = rng.next_u64() % 4;
                    let mut dropped = Vec::new();
                    p.prune(|s| u64::from(s) % 4 != keep, |n| dropped.push(n.bytes[0]));
                    format!(
                        r#"{{"t":"cl","m":"pprune","keep":{keep},"res":{}"#,
                        jlist(dropped.iter())
                    )
                }
            };
            let peers: Vec<u8> = p.peers().map(|n| n.bytes[0]).collect();
            let has: Vec<bool> = (1..=5).map(|k| p.contains(&nid(k))).collect();
            out.push(format!(
                r#"{line},"peers":{},"has":{}}}"#,
                jlist(peers.iter()),
                jlist(has.iter())
            ));
        }
    }
}

fn lookup_events(out: &mut Vec<String>) {
    let mut rng = SplitMix64::new(0x100C);
    for _ in 0..80 {
        let mut l: Lookups<3> = Lookups::new();
        let mut now = 0u64;
        out.push(r#"{"t":"cl","m":"lnew","n":3}"#.to_string());
        for _ in 0..60 {
            now = times(&mut rng, now);
            let peer = (rng.next_u64() % 5) as u8 + 1;
            let line = match rng.next_u64() % 12 {
                0..=6 => {
                    let udp = rng.next_u64().is_multiple_of(2);
                    let car = rng.next_u64().is_multiple_of(2);
                    // A thin node (a round trip of 250 ms or more, in whole microseconds) now and then.
                    let th = if rng.next_u64().is_multiple_of(3) {
                        250_000 + rng.next_u64() % 4_750_000
                    } else {
                        0
                    };
                    let a = l.ask(now, &nid(peer), udp, car, (th != 0).then_some(th * 1000));
                    let res = match a {
                        Ask::Skip => "skip",
                        Ask::Udp { others: false } => "udp",
                        Ask::Udp { others: true } => "udpall",
                        Ask::Carrier => "carrier",
                        Ask::Later => "later",
                    };
                    format!(
                        r#"{{"t":"cl","m":"ask","now":{},"peer":{peer},"udp":{udp},"car":{car},"thin":{th},"res":"{res}""#,
                        us(now)
                    )
                }
                7..=8 => {
                    l.answered(&nid(peer));
                    format!(
                        r#"{{"t":"cl","m":"answered","now":{},"peer":{peer},"res":"none""#,
                        us(now)
                    )
                }
                9 => {
                    l.too_large(&nid(peer));
                    format!(
                        r#"{{"t":"cl","m":"toolarge","now":{},"peer":{peer},"res":"none""#,
                        us(now)
                    )
                }
                10 => {
                    l.clear();
                    format!(r#"{{"t":"cl","m":"lclear","now":{},"res":"none""#, us(now))
                }
                _ => format!(r#"{{"t":"cl","m":"lview","now":{},"res":"none""#, us(now)),
            };
            let due: Vec<u8> = l.due(now).map(|n| n.bytes[0]).collect();
            let has: Vec<bool> = (1..=5).map(|k| l.contains(&nid(k))).collect();
            out.push(format!(
                r#"{line},"len":{},"due":{},"next":{},"has":{}}}"#,
                l.len(),
                jlist(due.iter()),
                opt_ceil(l.next_deadline()),
                jlist(has.iter())
            ));
        }
    }
    // verify: a signed record for node k, tampered or not, asked about the right and the wrong peer
    let kp = connect_common::ed(7);
    let me = kp.node_id();
    let addrs = [addr(1), addr(2)];
    let f = RecordFields {
        home: nid(9),
        seq: 42,
        reach: Reach::Nat,
        addrs: &addrs,
        hints: &[],
    };
    let mut rec = vec![0u8; 400];
    let n = vinc_connect::record::sign(&kp, &f, &mut rec).unwrap();
    rec.truncate(n);
    let mut cases: Vec<Vec<u8>> = vec![rec.clone()];
    for i in [0usize, 9, 40, 80, 83, 84, 100, n - 1] {
        let mut m = rec.clone();
        m[i] ^= 1;
        cases.push(m);
    }
    cases.push(rec[..n - 3].to_vec());
    let mut longer = rec.clone();
    longer.push(0);
    cases.push(longer);
    for case in &cases {
        for peer in [me, nid(7)] {
            let ans = DnsAnswer::Record(case);
            let sig = Record::parse(case).is_ok_and(|r| r.verify().is_ok());
            let res = match verify(&peer, &ans) {
                Ok(None) => unreachable!(),
                Ok(Some(found)) => format!(
                    r#"{{"found":{{"home":{},"reach":{},"seq":{},"addrs":[{}]}}}}"#,
                    bytes(&connect_common::node_bytes(&found.home)),
                    found.reach as u8,
                    found.seq,
                    found
                        .addrs()
                        .map(|a| format!(
                            "[{},{}]",
                            bytes(&match a.ip() {
                                IpAddr::V4(v) => v.octets().to_vec(),
                                IpAddr::V6(v) => v.octets().to_vec(),
                            }),
                            a.port()
                        ))
                        .collect::<Vec<_>>()
                        .join(",")
                ),
                Err(LookupError::TooLarge) => r#""toolarge""#.to_string(),
                Err(LookupError::WrongNode) => r#""wrongnode""#.to_string(),
                Err(LookupError::Record(e)) => format!(r#""rec:{}""#, connect_codec_out::rtag(e)),
            };
            out.push(format!(
                r#"{{"t":"cl","m":"verify","b":{},"peer":{},"sig":{sig},"k":"rec","res":{res}}}"#,
                bytes(case),
                bytes(&connect_common::node_bytes(&peer))
            ));
        }
    }
    let peer_b = bytes(&connect_common::node_bytes(&me));
    assert_eq!(verify(&me, &DnsAnswer::Absent), Ok(None));
    out.push(format!(
        r#"{{"t":"cl","m":"verify","b":[],"peer":{peer_b},"sig":false,"k":"abs","res":"none"}}"#
    ));
    assert_eq!(verify(&me, &DnsAnswer::TooLarge), Err(LookupError::TooLarge));
    out.push(format!(
        r#"{{"t":"cl","m":"verify","b":[],"peer":{peer_b},"sig":false,"k":"big","res":"toolarge"}}"#
    ));
}

fn netcheck_events(out: &mut Vec<String>) {
    let mut rng = SplitMix64::new(0x4E7);
    // classification
    let ips: [[u8; 4]; 5] = [
        [10, 0, 0, 1],
        [100, 64, 0, 1],
        [100, 128, 0, 1],
        [100, 127, 255, 1],
        [8, 8, 8, 8],
    ];
    let a = |i: usize, p: u16| SocketAddr::new(IpAddr::V4(Ipv4Addr::from(ips[i])), p);
    let pool: Vec<SocketAddr> = (0..5)
        .flat_map(|i| (1..3u16).map(move |p| (i, p)))
        .map(|(i, p)| a(i, p))
        .collect();
    let aj = |s: &SocketAddr| match s.ip() {
        IpAddr::V4(v) => format!("[{},{}]", bytes(&v.octets()), s.port()),
        IpAddr::V6(_) => unreachable!(),
    };
    for _ in 0..3000 {
        let mut pickn = |max: u64| -> Vec<SocketAddr> {
            (0..(rng.next_u64() % (max + 1)))
                .map(|_| pool[(rng.next_u64() % pool.len() as u64) as usize])
                .collect()
        };
        let local = pickn(2);
        let reflexive = pickn(3);
        let mapped = pickn(2);
        let udp_heard = rng.next_u64().is_multiple_of(2);
        let since = pick(&mut rng, &[0, 4 * S, 5 * S, 9 * S]);
        let wd = 5 * S;
        let res = classify(&Observed {
            local: &local,
            reflexive: &reflexive,
            mapped: &mapped,
            udp_heard,
            since_probe: since,
            watchdog: wd,
        });
        out.push(format!(
            r#"{{"t":"cl","m":"classify","local":[{}],"refl":[{}],"mapped":[{}],"heard":{udp_heard},"since":{},"wd":{},"res":{}}}"#,
            local.iter().map(aj).collect::<Vec<_>>().join(","),
            reflexive.iter().map(aj).collect::<Vec<_>>().join(","),
            mapped.iter().map(aj).collect::<Vec<_>>().join(","),
            us(since),
            us(wd),
            res.map_or(0, |r: Reach| r as u8)
        ));
    }
    for _ in 0..120 {
        let mut n: Netcheck<3> = Netcheck::new();
        let mut now = 0u64;
        out.push(r#"{"t":"cl","m":"nnew","r":3}"#.to_string());
        let mut nonces = [[0u8; 8]; 3];
        for _ in 0..70 {
            now = times(&mut rng, now);
            let relay = (rng.next_u64() % 4) as usize;
            let line = match rng.next_u64() % 14 {
                0..=3 => {
                    let nonce = [(rng.next_u64() % 3) as u8; 8];
                    let works = rng.next_u64().is_multiple_of(2);
                    n.probe_sent(now, relay, nonce, works);
                    if relay < 3 {
                        nonces[relay] = nonce;
                    }
                    format!(
                        r#"{{"t":"cl","m":"psent","now":{},"relay":{relay},"nonce":{},"works":{works},"res":"none""#,
                        us(now),
                        bytes(&nonce)
                    )
                }
                4..=7 => {
                    let nonce = if relay < 3 && !rng.next_u64().is_multiple_of(4) {
                        nonces[relay]
                    } else {
                        [(rng.next_u64() % 3) as u8; 8]
                    };
                    let port = (rng.next_u64() % 4) as u16 + 1;
                    let r = n.answered(now, relay, nonce, addr(port));
                    format!(
                        r#"{{"t":"cl","m":"answered","now":{},"relay":{relay},"nonce":{},"addr":{port},"res":{}"#,
                        us(now),
                        bytes(&nonce),
                        opt_us(r)
                    )
                }
                8 => {
                    n.failed(relay);
                    format!(
                        r#"{{"t":"cl","m":"failed","now":{},"relay":{relay},"res":"none""#,
                        us(now)
                    )
                }
                9 => {
                    n.healthy(relay);
                    format!(
                        r#"{{"t":"cl","m":"healthy","now":{},"relay":{relay},"res":"none""#,
                        us(now)
                    )
                }
                10 | 11 => {
                    let usable = [
                        !rng.next_u64().is_multiple_of(4),
                        !rng.next_u64().is_multiple_of(4),
                        !rng.next_u64().is_multiple_of(4),
                    ];
                    let open = [
                        rng.next_u64().is_multiple_of(2),
                        rng.next_u64().is_multiple_of(2),
                        rng.next_u64().is_multiple_of(2),
                    ];
                    let r = n.failover(|i| usable[i], |i| open[i]);
                    format!(
                        r#"{{"t":"cl","m":"failover","now":{},"usable":{},"open":{},"res":{}"#,
                        us(now),
                        jlist(usable.iter()),
                        jlist(open.iter()),
                        r.map_or(-1, |x| x as i64)
                    )
                }
                12 => {
                    n.restart();
                    format!(r#"{{"t":"cl","m":"restart","now":{},"res":"none""#, us(now))
                }
                _ => {
                    let first = (!rng.next_u64().is_multiple_of(3)).then(|| (rng.next_u64() % 3) as usize);
                    let r = n.home_missing(first);
                    let s = match r {
                        HomeStep::Done => "done".to_string(),
                        HomeStep::Again => "again".to_string(),
                        HomeStep::Fallback(f) => format!("fb{f}"),
                    };
                    format!(
                        r#"{{"t":"cl","m":"missing","now":{},"fr":{},"res":"{s}""#,
                        us(now),
                        first.map_or(-1, |x| x as i64)
                    )
                }
            };
            let rtts: Vec<i64> = (0..3).map(|i| n.rtt(i).map_or(-1, |v| us(v) as i64)).collect();
            let refl: Vec<i64> = (0..3)
                .map(|i| n.reflexive_of(i).map_or(-1, |a| i64::from(a.port())))
                .collect();
            let unh: Vec<bool> = (0..3).map(|i| n.unhealthy(i)).collect();
            out.push(format!(
                r#"{line},"home":{},"rtts":{},"refl":{},"unh":{},"best":{},"first":{}}}"#,
                n.home().map_or(-1, |h| h as i64),
                jlist(rtts.iter()),
                jlist(refl.iter()),
                jlist(unh.iter()),
                us(n.best_rtt()),
                opt_us(n.first_probe())
            ));
        }
    }
}

#[test]
fn connect_client_trace() {
    let mut out = Vec::new();
    let _: NodeId = nid(1);
    punch_events(&mut out);
    tunnel_events(&mut out);
    dial_events(&mut out);
    lookup_events(&mut out);
    netcheck_events(&mut out);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::write(format!("{dir}/connect_client.ndjson"), out.join("\n") + "\n").unwrap();
    }
    assert!(out.len() > 20_000);
}
