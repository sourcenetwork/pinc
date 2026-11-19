//! Model-based tests of the endpoint's half-open cap: a real endpoint (`pinc-core`, built with the `trace` feature, the
//! cap of 256 the code has) driven along every edge of the state graph of `proofs/tla/MbtHalfOpen.tla`.
//!
//! TLC enumerates every state the admission and expiry operators of `HalfOpenOps.tla` reach at the real cap within
//! the bounds of a config and writes the graph; `scripts/mbt.py` turns it into paths from the empty endpoint that take
//! every edge, which `scripts/proofs.sh` writes to the directory `PINC_MBT_DIR`: `halfopen.ndjson` from
//! `MbtHalfOpen.cfg` and `halfopen_back.ndjson` from `MbtHalfOpen_back.cfg`. This test runs each path on a fresh
//! endpoint: a `CallFlood` hands it a forged first flight (a message id and a source it has not seen) of the type and
//! length the call names, a `CallTimer` runs its timers. After every call the endpoint's own record of the decision
//! (the admission its trace ring holds: made, refused or dropped by the screening, told apart by the floor of the type,
//! and the count it used) must be the model's, the count of
//! half-open sessions must be the model's, and the sessions it holds, read through the `trace` view `half_open_slot`
//! and grouped by their creation time, must be the model's: every one unauthenticated and counted, as many made at
//! each time as the model says. It stops at the first difference and names the file, the case, the step and the calls
//! that led there. Without `PINC_MBT_DIR` it checks nothing.
//!
//! The model's numbers stand for the code's as `MbtHalfOpen.tla` says: model time `t` is `origin + t * step` with
//! `step = HALF_OPEN_LIFE / LIFE`, and a model length is the real floor of the type (`FULL_INITIAL_MIN`,
//! `SHORT_INITIAL_MIN`, `RESUME_HELLO_MIN`, 40 for a type with no floor) plus the model's length minus the model's floor. The cap, the
//! lifetime and the size of the slot table (300, so the cap and not the table refuses) are the code's. The origin is
//! `2 * HALF_OPEN_LIFE` or an odd millisecond past `5 * HALF_OPEN_LIFE`, by case.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub
)]

use std::fmt::Write as _;
use std::net::SocketAddr;
use std::rc::Rc;

use pinc_core::{Endpoint, EndpointConfig, HALF_OPEN_LIFE, MAX_HALF_OPEN, Slot, TraceEvent};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::message::{FULL_INITIAL_MIN, RESUME_HELLO_MIN, SHORT_INITIAL_MIN};
use pinc_security::{ConnId, KeyHandle, LocalIdentity};
use pinc_tests::{ALPN_A, Caps, Json, MS_NS, MbtCase, big_stack, mbt_cases};
use pinc_transport::conn::{Held, Resources, Shared, Tables};
use pinc_transport::packet::{LongHeader, LongType};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{self, NoSource, Streams};
use pinc_wire::Writer;

/// The table of the endpoint: room past the cap, so the cap and not the table refuses.
const K: usize = MAX_HALF_OPEN + 44;

type Ep<'s> = Endpoint<'s, 'static, Caps, NoSource, 1, 2, 16, 1, K, { K * 10 }, 4, 4, 2>;
type TSlot = Slot<'static, Caps, NoSource, 1, 2, 16, 1>;

// A slot's memory, owned by the slot: every case builds a table of `K` slots, so none of it may outlive its case.
fn small_memory() -> Resources<'static, NoSource, 1, 2, 16> {
    let pool = BufferPool::new_boxed(4);
    let streams = Box::new(Streams::new(&stream::Config::new(false), &pool));
    Resources {
        pool,
        streams: Held::Owned(streams),
        loss: Shared::Counted(Rc::new(LossEstimate::new())),
        tables: Tables::new(),
    }
}

fn slots() -> Box<[TSlot; K]> {
    let v: Vec<TSlot> = (0..K).map(|_| Slot::new(small_memory())).collect();
    v.into_boxed_slice().try_into().ok().unwrap()
}

// The endpoint of `trace_halfopen.rs` over `slots`: a software provider, one registered protocol, one interface.
fn server(now: u64, slots: &mut [TSlot; K]) -> (Box<Ep<'_>>, SocketAddr) {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let mut ep = Box::new(Endpoint::new(
        now,
        Caps(Software, true),
        Drbg::new(&[3; 32]),
        id,
        EndpointConfig::new(5),
        slots,
    ));
    assert!(ep.register_alpn(ALPN_A));
    let addr: SocketAddr = "10.0.0.1:4433".parse().unwrap();
    ep.add_iface(addr).unwrap();
    (ep, addr)
}

/// A long handshake datagram of exactly `len` bytes for `odcid` whose message (of 4095 bytes) starts with `kind`.
fn craft(odcid: u64, kind: u8, len: usize) -> Vec<u8> {
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
    w.put_varint(0).unwrap();
    w.put_u8(kind).unwrap();
    w.put_u8(odcid as u8).unwrap();
    d
}

fn source(i: u64) -> SocketAddr {
    SocketAddr::from(([10, 1, (i >> 8) as u8, i as u8], 9))
}

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

/// How the model's numbers map onto the code's.
struct Map {
    step: u64,
    origin: u64,
    full: u64,
    short: u64,
    hello: u64,
}

impl Map {
    fn time(&self, t: u64) -> u64 {
        self.origin + t * self.step
    }

    /// The datagram of a flood: the real floor of the type plus the model's length over the model's floor.
    fn len(&self, kind: u64, len: u64) -> usize {
        let (real, model) = match kind {
            1 => (FULL_INITIAL_MIN, self.full),
            2 => (SHORT_INITIAL_MIN, self.short),
            6 => (RESUME_HELLO_MIN, self.hello),
            _ => (40, 0),
        };
        real + len as usize - model as usize
    }
}

/// The endpoint's sessions against the model's `g` (the number made at each time) and `count`.
fn same_state(ep: &Ep<'_>, st: &Json, map: &Map, at: &dyn Fn() -> String) {
    let g: Vec<u64> = st.get("g").and_then(Json::arr).unwrap().iter().map(num).collect();
    let mut seen = vec![0u64; g.len()];
    for i in 0..K {
        let Some(s) = ep.half_open_slot(i) else { continue };
        assert!(
            s.unauth && s.counted,
            "{}: slot {i} holds a session that is not an unauthenticated counted one: {s:?}",
            at()
        );
        let t = (s.created - map.origin) / map.step;
        assert!(
            s.created == map.time(t) && (t as usize) < g.len(),
            "{}: slot {i} was made at a time that is no time of the model: {s:?}",
            at()
        );
        seen[t as usize] += 1;
    }
    assert_eq!(
        seen,
        g,
        "{}: the sessions held, by the time they were made, differ from the model's",
        at()
    );
    let count = num(st.get("count").unwrap());
    assert_eq!(
        ep.node_stats().half_open as u64,
        count,
        "{}: the count of half-open sessions differs from the model's",
        at()
    );
}

fn drain(ep: &mut Ep<'_>) {
    while ep.poll_event().is_some() {}
}

/// Runs one case of `file` on a fresh endpoint; returns the number of calls.
fn run(file: &str, case: &MbtCase, init: &Json, (full, short, hello): (u64, u64, u64), step: u64) -> usize {
    let map = Map {
        step,
        origin: [2 * HALF_OPEN_LIFE, 5 * HALF_OPEN_LIFE + 123 * MS_NS][(case.id % 2) as usize],
        full,
        short,
        hello,
    };
    let mut table = slots();
    let (mut ep, addr) = server(map.origin, &mut table);
    while ep.poll_trace().is_some() {}
    let who = format!("{file} case {}", case.id);
    same_state(&ep, init, &map, &|| format!("{who}: the empty endpoint"));
    let mut next = case.id << 32;
    let mut count = 0;
    for (i, st) in case.steps.iter().enumerate() {
        let a = &st.args;
        match (st.call.as_str(), a.as_slice()) {
            ("CallFlood", [t, kind, len, dec]) => {
                let now = map.time(num(t));
                let (kind, dec) = (num(kind), num(dec));
                let ok = dec == 1;
                next += 1;
                let mut d = craft(next, u8::try_from(kind).unwrap(), map.len(kind, num(len)));
                let dropped0 = ep.node_stats().dropped_in;
                ep.handle_datagram(now, addr, source(next), &mut d);
                let dropped = ep.node_stats().dropped_in - dropped0;
                let mut decisions = Vec::new();
                while let Some(rec) = ep.poll_trace() {
                    if let TraceEvent::HalfOpen {
                        admitted,
                        half_open,
                        resume,
                        ..
                    } = rec.event
                    {
                        decisions.push((admitted, half_open, resume));
                    }
                }
                if matches!(kind, 1 | 2 | 6) {
                    assert_eq!(
                        decisions,
                        [(dec, count, 0)],
                        "{who} step {i}: the endpoint's decisions (admitted, count, resume) differ from the model's: admitted \
                         {dec} at the count {count}, no resumption; calls:{}",
                        calls(case, i)
                    );
                } else {
                    assert!(
                        decisions.is_empty() && dec == 0,
                        "{who} step {i}: a flight of a type that starts nothing was decided on; calls:{}",
                        calls(case, i)
                    );
                }
                assert_eq!(
                    dropped,
                    u64::from(!ok),
                    "{who} step {i}: the flight was dropped or kept against the model's {ok}; calls:{}",
                    calls(case, i)
                );
            }
            ("CallTimer", [t]) => ep.handle_timeout(map.time(num(t))),
            _ => panic!("{who}: a call the test does not know: {st}"),
        }
        drain(&mut ep);
        let after = &st.state;
        count = num(after.get("count").unwrap());
        same_state(&ep, after, &map, &|| {
            format!("{who} after step {i}; calls:{}", calls(case, i))
        });
        while ep.poll_trace().is_some() {}
    }
    case.steps.len()
}

/// Walks every case of `file`; false when `PINC_MBT_DIR` is unset.
fn walk(file: &str) -> bool {
    let Some(cases) = mbt_cases(file) else {
        return false;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let c = head.get("constants").unwrap();
    let k = |n: &str| num(c.get(n).unwrap());
    assert_eq!(
        k("MAX"),
        MAX_HALF_OPEN as u64,
        "{file}: the model's cap is not the code's"
    );
    let life = k("LIFE");
    assert!(
        life > 0 && HALF_OPEN_LIFE.is_multiple_of(life * MS_NS),
        "{file}: the model's lifetime does not divide the code's"
    );
    let init = head.get("init").unwrap();
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        steps += run(
            file,
            &case.unwrap(),
            init,
            (k("FULL"), k("SHORT"), k("HELLO")),
            HALF_OPEN_LIFE / life,
        );
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert_eq!(
        (n, steps as u64),
        (count("cases"), count("steps")),
        "{file}: the file ends early"
    );
    eprintln!(
        "mbt_halfopen: {file}: {n} cases, {steps} calls, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
    true
}

#[test]
fn the_half_open_cap_follows_every_edge_of_the_model() {
    // MbtHalfOpen.cfg and MbtHalfOpen_back.cfg
    let walked = big_stack(|| ["halfopen.ndjson", "halfopen_back.ndjson"].map(walk));
    if walked == [false; 2] {
        eprintln!("mbt_halfopen: PINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
    }
}
