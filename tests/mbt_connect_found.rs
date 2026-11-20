//! Model-based test of the connect client's cache of lookup answers: a real `Connectivity` driven through its public
//! calls along every edge of the state graph of `proofs/tla/MbtConnectFound.tla`.
//!
//! The model is `ConnectFoundOps.tla` with the code's ring of 8 slots (`FOUND`) and three peers whose answers, forgets
//! and clock ticks the graph takes. The ring cannot be shrunk, so every case starts by answering six filler peers
//! (4 to 9, sequence 1) that then sit in the ring and are never answered or forgotten again, only evicted: the steps
//! act on peers 1 to 3. `MbtConnectFound.cfg` bounds them (sequences 1 and 2, one home, a lifetime of one tick, the
//! clock to 1); TLC writes the graph, `scripts/mbt.py` turns it into paths from the state after the fillers that take
//! every edge, and `scripts/proofs.sh` writes them to the directory `PINC_MBT_DIR` as `connect_found.ndjson`.
//!
//! Every call of the model is one public call: an answer is a signed `DnsReply` handed to `handle_udp`, a forget is
//! `forget_found`, a tick moves the test's own clock. After every step `found` and `found_fresh` (at each model time)
//! of all nine peers must be what the model's `seen` and `fresh` say; the ring's slot indices are not visible through
//! the API, so `c` is not compared, it decides which entries `found` still gives. It stops at the first difference and
//! names the file, the case, the step, the peer, the field and the calls that led there. Without `PINC_MBT_DIR` it
//! checks nothing; with it, a missing file or a file with no case fails. The fixed cases of `connect_found_slot.rs`
//! always run.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub
)]

mod connect_common;

use std::collections::HashMap;
use std::fmt::Write as _;
use std::net::SocketAddr;

use connect_common::{SEC, big_stack, ed, id, record_bytes};
use pinc_connect::carrier::DnsAnswer;
use pinc_connect::client::conn::{FOUND, FOUND_TTL};
use pinc_connect::client::{Config, Connectivity, RelayCfg};
use pinc_connect::relay::datagram::Datagram;
use pinc_crypto::{NodeId, Software};
use pinc_tests::{Host, Json, MbtCase, mbt_cases};

type Conn = Connectivity<Software, 1, 4>;

const FILE: &str = "connect_found.ndjson";
const RELAY_UDP: &str = "203.0.113.10:4433";
const PEERS: u64 = 9;
const TTL: u64 = 1;
const TMAX: u64 = 1;

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

fn nums(v: &Json) -> Vec<u64> {
    v.arr().unwrap().iter().map(num).collect()
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

/// Everything one walk shares: the node's setup, the peers, the encoded replies.
struct Rig {
    cfg: Config<1>,
    prekeys: pinc_security::PrekeyInfo,
    peers: Vec<NodeId>,
    replies: HashMap<(u64, u64, u64), Vec<u8>>,
}

fn home(h: u64) -> NodeId {
    id(&ed(0x80 + h as u8))
}

/// The model time `n` as the code's clock.
fn t(n: u64) -> u64 {
    1001 * SEC + n * (FOUND_TTL / TTL)
}

impl Rig {
    fn new(seqs: &[u64], homes: &[u64]) -> Self {
        let host = Box::new(Host::new(0x41, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let mut relays = [None; 1];
        relays[0] = Some(RelayCfg {
            id: id(&ed(0x77)),
            udp: Some(RELAY_UDP.parse().unwrap()),
            tcp: None,
            ws: None,
        });
        let cfg = Config {
            me: host.identity.node_id(),
            identity: host.identity,
            relays,
            phone: false,
            restarted: false,
            start: 1000 * SEC,
            v6: false,
            keep_learn: false,
        };
        let kps: Vec<_> = (1..=PEERS).map(|p| ed(0x90 + p as u8)).collect();
        let mut replies = HashMap::new();
        let mut encode = |p: u64, q: u64, h: u64| {
            let kp = &kps[p as usize - 1];
            let rec = record_bytes(kp, home(h), q);
            let mut out = vec![0u8; 1500];
            let n = Datagram::DnsReply {
                peer: id(kp),
                answer: DnsAnswer::Record(&rec),
            }
            .encode(&mut out)
            .unwrap();
            out.truncate(n);
            replies.insert((p, q, h), out);
        };
        for p in 1..=3 {
            for &q in seqs {
                for &h in homes {
                    encode(p, q, h);
                }
            }
        }
        for p in 4..=PEERS {
            encode(p, 1, 1);
        }
        Self {
            cfg,
            prekeys: host.prekey_info.clone(),
            peers: kps.iter().map(id).collect(),
            replies,
        }
    }

    fn node(&self) -> Box<Conn> {
        Box::new(Connectivity::new(self.cfg, self.prekeys.clone(), Software, 7))
    }

    fn answer(&self, c: &mut Conn, now: u64, p: u64, q: u64, h: u64, at: &dyn Fn() -> String) {
        let bytes = self
            .replies
            .get(&(p, q, h))
            .unwrap_or_else(|| panic!("{}: an answer ({p}, {q}, {h}) the test has no record for", at()));
        assert!(
            c.handle_udp(now, RELAY_UDP.parse::<SocketAddr>().unwrap(), bytes),
            "{}: handle_udp did not take the answer",
            at()
        );
    }

    /// The node's `found` and `found_fresh` of every peer against the model's `seen` and `fresh`.
    fn same(&self, c: &Conn, st: &Json, now_n: u64, at: &dyn Fn() -> String) {
        assert_eq!(num(st.get("clock").unwrap()), now_n, "{}: the clock", at());
        let seen = st.get("seen").unwrap().arr().unwrap();
        let fresh = st.get("fresh").unwrap().arr().unwrap();
        for p in 1..=PEERS {
            let (peer, s, fr) = (
                &self.peers[p as usize - 1],
                &seen[p as usize - 1],
                &fresh[p as usize - 1],
            );
            let held = s.get("e").unwrap().bool().unwrap();
            let got = c.found(peer);
            assert_eq!(
                got.is_some(),
                held,
                "{}: peer {p}, found is {:?}, the model's entry is {s}",
                at(),
                got.map(|f| (f.seq, f.home))
            );
            if let Some(f) = got {
                assert_eq!(f.seq, num(s.get("seq").unwrap()), "{}: peer {p}, found.seq", at());
                assert_eq!(f.home, home(num(s.get("h").unwrap())), "{}: peer {p}, found.home", at());
            }
            let fr = fr.arr().unwrap();
            assert_eq!(fr.len() as u64, TMAX + TTL + 1, "{}: the width of fresh", at());
            for (n, want) in fr.iter().enumerate() {
                let fresh_at = c.found_fresh(t(n as u64), peer);
                assert_eq!(
                    fresh_at.is_some(),
                    want.bool().unwrap(),
                    "{}: peer {p}, found_fresh at {n}",
                    at()
                );
                if let (Some(a), Some(b)) = (fresh_at, got) {
                    assert_eq!(
                        (a.seq, a.home),
                        (b.seq, b.home),
                        "{}: peer {p}, found_fresh at {n}",
                        at()
                    );
                }
            }
        }
    }

    /// Runs one case on a fresh node; returns the number of calls.
    fn run(&self, case: &MbtCase, init: &Json) -> usize {
        let who = format!("{FILE} case {}", case.id);
        let mut c = self.node();
        let mut now_n = 0;
        for p in 4..=PEERS {
            self.answer(&mut c, t(0), p, 1, 1, &|| format!("{who}: after the fillers"));
        }
        self.same(&c, init, 0, &|| format!("{who}: after the fillers"));
        for (i, st) in case.steps.iter().enumerate() {
            let at = || format!("{who} step {i}; calls:{}", calls(case, i));
            match (st.call.as_str(), st.args.as_slice()) {
                ("CallAnswer", [p, q, h]) => self.answer(&mut c, t(now_n), num(p), num(q), num(h), &at),
                ("CallForget", [p]) => c.forget_found(&self.peers[num(p) as usize - 1]),
                ("CallTick", []) => now_n += 1,
                _ => panic!("{who}: a call the test does not know: {st}"),
            }
            self.same(&c, &st.state, now_n, &at);
        }
        case.steps.len()
    }
}

/// Walks every case; false when `PINC_MBT_DIR` is unset.
fn walk() -> bool {
    let Some(cases) = mbt_cases(FILE) else {
        return false;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let c = head.get("constants").unwrap();
    let k = |n: &str| c.get(n).unwrap_or_else(|| panic!("{FILE}: the constants have no {n}"));
    assert_eq!(num(k("N")), FOUND as u64, "{FILE}: N is not the code's ring size");
    assert_eq!(num(k("NP")), 3, "{FILE}: NP");
    assert_eq!(num(k("FILL")), 6, "{FILE}: FILL");
    assert_eq!(nums(k("SEQS")), [1, 2], "{FILE}: SEQS");
    assert_eq!(nums(k("HOMES")), [1], "{FILE}: HOMES");
    assert_eq!(num(k("TTL")), TTL, "{FILE}: TTL");
    assert_eq!(num(k("TMAX")), TMAX, "{FILE}: TMAX");
    assert_eq!(FOUND_TTL % num(k("TTL")), 0, "FOUND_TTL is not a whole number of ticks");
    let rig = Rig::new(&nums(k("SEQS")), &nums(k("HOMES")));
    let init = head.get("init").unwrap();
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        steps += rig.run(&case.unwrap(), init);
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert!(n > 0, "{FILE}: the file holds no case");
    assert_eq!(
        (n, steps as u64),
        (count("cases"), count("steps")),
        "{FILE}: the file ends early"
    );
    eprintln!(
        "mbt_connect_found: {FILE}: {n} cases, {steps} calls, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
    true
}

#[test]
fn walk_graph() {
    // MbtConnectFound.cfg
    let ran = big_stack(walk);
    if !ran {
        eprintln!(
            "mbt_connect_found: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)"
        );
    }
}
