//! Trace generation for the port mappings a node holds (`pinc_connect::client::Connectivity::set_mapped`,
//! `candidates`, `link_changed` and `class`): seeded and fixed runs of the real layer with one relay, recorded as
//! ndjson (`connect_mapped.ndjson`) for the TLA+ trace check (`TraceConnectMapped.tla`).
//!
//! A run starts with a fresh rig (`new`) and then sets the mappings (`set`), has the relay report the address it saw
//! the node at (`report`) or changes the link (`link`). After every call the event shows the addresses the node
//! offers and its class. The fixed runs are the three of `connect_mapped.rs` and the cases of a mapping withdrawn, a
//! relay that sees another IP, two mappings, a public address, the shared range and a mapping set before any report;
//! then 60 random runs.
//!
//! The test checks by itself: a mapped address is offered only while the last report since the last link named its
//! IP (or it is that address or the local one), the mappings so vouched for lead the offer in the order of the
//! mapping, the port-mapped class holds only while such a report stands, a node that has a class keeps one, and the
//! offer has at most eight addresses and no repeat. The model is told the UDP watchdog never fires (the calls are a
//! millisecond apart), which the test asserts by the class never being `UdpBlocked`.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cognitive_complexity,
    unreachable_pub
)]

mod connect_common;
mod connect_rig;

use std::fmt::Write as _;
use std::net::SocketAddr;

use connect_common::{Rec, SEC, big_stack};
use connect_rig::Rig;
use pinc_connect::record::{MAX_ADDRS, Reach};
use pinc_crypto::Software;
use pinc_security::Env;
use pinc_tests::{Host, SplitMix64, soaking};

const NOW: u64 = 1000 * SEC;

fn a(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

fn rig() -> Rig {
    let host = Box::new(Host::new(0x31, a("192.168.1.2:4433"), NOW));
    let (identity, prekey) = (host.identity, host.prekey_info.clone());
    Rig::new(&identity, prekey)
}

/// One round of address discovery: the relay saw the node at `src` and says so.
fn report(rig: &mut Rig, now: u64, src: &str) {
    let Rig {
        conn,
        relay,
        sink,
        drbg,
        udp,
        ..
    } = rig;
    let mut env = Env {
        provider: &Software,
        now,
        drbg,
    };
    conn.probe_all(now, &mut env);
    let mut buf = vec![0u8; 2048];
    let (to, n) = conn.poll_udp(&mut buf).expect("a probe");
    assert_eq!(to, *udp);
    relay.datagram(now, a(src), None, &buf[..n], sink).unwrap();
    let reply = sink
        .effects()
        .into_iter()
        .find_map(|r| if let Rec::Udp(_, b) = r { Some(b) } else { None })
        .expect("the relay answers");
    assert!(conn.handle_udp(now, *udp, &reply));
}

fn offered(rig: &Rig) -> Vec<SocketAddr> {
    let mut out = [a("0.0.0.0:0"); MAX_ADDRS];
    let n = rig.conn.candidates(&mut out);
    out[..n].to_vec()
}

const MP: &str = "198.51.100.5:7777";
const MQ: &str = "203.0.113.9:7777";
const ML: &str = "192.168.1.2:4433";
const SOURCES: [&str; 6] = [
    "198.51.100.5:20000",
    "198.51.100.5:20001",
    "198.51.100.5:7777",
    "203.0.113.9:20000",
    "100.64.0.1:20000",
    "192.168.1.2:4433",
];

fn aj(a: SocketAddr) -> String {
    match a {
        SocketAddr::V4(v) => {
            let [p, q, r, s] = v.ip().octets();
            format!(r#"{{"ip":[{p},{q},{r},{s}],"port":{}}}"#, v.port())
        }
        SocketAddr::V6(_) => panic!("the mapped trace uses no IPv6 address"),
    }
}

fn alist(v: &[SocketAddr]) -> String {
    let items: Vec<String> = v.iter().map(|x| aj(*x)).collect();
    format!("[{}]", items.join(","))
}

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    fell_by_set: u32,
    fell_by_link: u32,
    public_with_map: u32,
    same_pair: u32,
}

struct T {
    out: String,
    seen: Seen,
}

#[derive(Clone, Copy, PartialEq)]
enum Op {
    New,
    Set,
    Report,
    Link,
}

/// One run: a rig and what the test knows of it.
struct M {
    rig: Rig,
    k: u64,
    last: Option<SocketAddr>,
    mapping: [Option<SocketAddr>; 2],
    cls: u8,
}

impl M {
    fn start(t: &mut T) -> Self {
        let mut m = Self {
            rig: rig(),
            k: 0,
            last: None,
            mapping: [None; 2],
            cls: 0,
        };
        let (cands, cls) = m.check(t, Op::New);
        let _ = writeln!(
            t.out,
            r#"{{"t":"map","op":"new","local":[{}],"relays":1,"cands":{},"cls":{cls}}}"#,
            aj(a(ML)),
            alist(&cands)
        );
        m
    }

    fn now(&mut self) -> u64 {
        let now = NOW + self.k * 1_000_000;
        self.k += 1;
        assert!(self.k <= 2000, "a run has more than 2000 calls");
        now
    }

    /// The offer and the class after a call, with every check of the test.
    fn check(&mut self, t: &mut T, op: Op) -> (Vec<SocketAddr>, u8) {
        let cands = offered(&self.rig);
        let class = self.rig.conn.class();
        assert_ne!(class, Some(Reach::UdpBlocked), "the UDP watchdog fired");
        let cls = class.map_or(0, |c| c as u8);
        let local = a(ML);
        let maps: Vec<SocketAddr> = self.mapping.iter().flatten().copied().collect();
        assert!(cands.len() <= MAX_ADDRS);
        assert!(
            cands.iter().enumerate().all(|(i, c)| !cands[..i].contains(c)),
            "a repeat in the offer: {cands:?}"
        );
        for c in cands.iter().filter(|c| maps.contains(c)) {
            assert!(
                self.last.is_some_and(|l| l.ip() == c.ip()) || *c == local,
                "the mapped address {c} is offered with no report naming its IP"
            );
        }
        let vouched = self.last.is_some_and(|l| maps.iter().any(|m| m.ip() == l.ip()));
        if let Some(l) = self.last {
            let mut lead: Vec<SocketAddr> = Vec::new();
            for m in maps.iter().filter(|m| m.ip() == l.ip()) {
                if !lead.contains(m) {
                    lead.push(*m);
                }
            }
            assert!(
                cands.starts_with(&lead),
                "the vouched mappings {lead:?} do not lead {cands:?}"
            );
        }
        assert!(cls != 2 || vouched, "port-mapped with no report naming a mapping's IP");
        assert!(self.cls == 0 || cls != 0, "a node that had a class lost it");
        if self.cls == 2 && (cls == 3 || cls == 4) {
            t.seen.fell_by_set += u32::from(op == Op::Set);
            t.seen.fell_by_link += u32::from(op == Op::Link);
        }
        t.seen.public_with_map += u32::from(cls == 1 && !maps.is_empty());
        self.cls = cls;
        (cands, cls)
    }

    fn set(&mut self, t: &mut T, addrs: &[&str]) {
        let list: Vec<SocketAddr> = addrs.iter().map(|s| a(s)).collect();
        let now = self.now();
        let before = self.mapping;
        self.mapping = [list.first().copied(), list.get(1).copied()];
        t.seen.same_pair += u32::from(before == self.mapping && before[0].is_some());
        self.rig.conn.set_mapped(now, &list);
        let (cands, cls) = self.check(t, Op::Set);
        let _ = writeln!(
            t.out,
            r#"{{"t":"map","op":"set","addrs":{},"cands":{},"cls":{cls}}}"#,
            alist(&list),
            alist(&cands)
        );
    }

    fn report(&mut self, t: &mut T, src: &str) {
        let now = self.now();
        report(&mut self.rig, now, src);
        self.last = Some(a(src));
        let (cands, cls) = self.check(t, Op::Report);
        let _ = writeln!(
            t.out,
            r#"{{"t":"map","op":"report","relay":0,"a":{},"cands":{},"cls":{cls}}}"#,
            aj(a(src)),
            alist(&cands)
        );
    }

    fn link(&mut self, t: &mut T) {
        let now = self.now();
        self.rig.conn.link_changed(now);
        self.last = None;
        let (cands, cls) = self.check(t, Op::Link);
        let _ = writeln!(
            t.out,
            r#"{{"t":"map","op":"link","cands":{},"cls":{cls}}}"#,
            alist(&cands)
        );
    }
}

fn fixed_runs(t: &mut T) {
    // 1. the three tests of connect_mapped.rs
    let mut m = M::start(t);
    m.report(t, "198.51.100.5:20000");
    m.set(t, &[]);
    let mut m = M::start(t);
    m.set(t, &["1.2.3.4:4433"]);
    m.report(t, "198.51.100.5:20000");
    let mut m = M::start(t);
    m.set(t, &[MP]);
    m.report(t, "198.51.100.5:20000");
    m.link(t);
    m.report(t, "198.51.100.5:20001");
    // 2. port-mapped, then the mapping withdrawn
    let mut m = M::start(t);
    m.set(t, &[MP]);
    m.report(t, "198.51.100.5:20000");
    m.set(t, &[]);
    // 3. port-mapped, then the relay sees another IP
    let mut m = M::start(t);
    m.set(t, &[MP]);
    m.report(t, "198.51.100.5:20000");
    m.report(t, "203.0.113.9:20000");
    // 4. two mappings, one seen
    let mut m = M::start(t);
    m.set(t, &[MP, MQ]);
    m.report(t, "203.0.113.9:20000");
    m.set(t, &[MQ, MP]);
    m.set(t, &[MQ, MP]);
    m.set(t, &[MP, MP]);
    m.set(t, &[MP, MQ, ML]);
    // 5. public wins over a mapping
    let mut m = M::start(t);
    m.set(t, &[MP]);
    m.report(t, "192.168.1.2:4433");
    m.report(t, "198.51.100.5:20000");
    // 6. the shared range
    let mut m = M::start(t);
    m.report(t, "100.64.0.1:20000");
    m.set(t, &[MP]);
    m.link(t);
    m.report(t, "198.51.100.5:7777");
    // 7. a mapping set before any report, then a link change, then reports
    let mut m = M::start(t);
    m.set(t, &[MP]);
    m.link(t);
    m.report(t, "198.51.100.5:20000");
    m.set(t, &[MQ]);
    m.report(t, "203.0.113.9:20000");
}

fn random_runs(t: &mut T, rng: &mut SplitMix64) {
    const MAPS: [&str; 3] = [MP, MQ, ML];
    for _ in 0..60 {
        let mut m = M::start(t);
        for _ in 0..30 {
            match rng.next_u64() % 100 {
                0..=39 => {
                    let n = (rng.next_u64() % 4) as usize;
                    let addrs: Vec<&str> = (0..n).map(|_| MAPS[(rng.next_u64() % 3) as usize]).collect();
                    m.set(t, &addrs);
                }
                40..=84 => m.report(t, SOURCES[(rng.next_u64() % 6) as usize]),
                _ => m.link(t),
            }
        }
    }
}

#[test]
fn mapped_addresses_match_the_model() {
    big_stack(|| {
        let mut rng = SplitMix64::traced(0x4D41_5050);
        let mut t = T {
            out: String::new(),
            seen: Seen::default(),
        };
        fixed_runs(&mut t);
        random_runs(&mut t, &mut rng);
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("connect_mapped.ndjson"), &t.out).unwrap();
        }
        if !soaking() {
            let s = &t.seen;
            assert!(s.fell_by_set > 0, "port-mapped never fell back by a set");
            assert!(s.fell_by_link > 0, "port-mapped never fell back by a link change");
            assert!(s.public_with_map > 0, "the class was never public with a mapping set");
            assert!(s.same_pair > 0, "no set repeated the pair before it");
        }
    });
}
