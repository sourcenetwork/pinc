//! Trace generation for the node's round trips: seeded runs of a real `NodeRtt` (`vinc-core`), recorded as ndjson
//! (`rtt.ndjson`) for the TLA+ trace check (`TraceRtt.tla`) and the Lean replay (`Vinc/TraceRtt.lean`).
//!
//! A run starts from an empty `NodeRtt` and calls `note_handshake`, `restore_peer`, `note_peak` and `note_timeout`
//! with a few peers and with values that land on the edges: zero, one, 250 ms and one nanosecond either side, 500 ms,
//! 8 s, and values up to `u64::MAX` so that the average, the first resend and the hub resend saturate. Long runs
//! use 300 peers, so the table of 256 fills and refuses. A `u64` is written as four 16-bit limbs (TLC cannot read a
//! number above 2^31). After every call the file shows the table (its peers in order; the values too while it holds
//! at most 8 entries), the average, the peak, the floor, and every reader for four peers (the one the call named,
//! 1, 2 and one never seen): the peer's `krtt`, `first_resend`, `remembered_for` and `hub_resend`, `thin_node`, and
//! `thin` for a random session.
//!
//! The test compares every call and every reader with a naive node written from the module documentation in `u128`
//! (a list of peers, formulas without saturating calls), and asserts the documented promises itself: the table never
//! holds more than `PEER_RTTS` peers and never replaces or moves one; the floor falls only on a handshake sample.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::indexing_slicing,
    clippy::cognitive_complexity,
    clippy::items_after_statements,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_core::{FIRST_RESEND, FLOOR_MAX, HUB_RESEND, NodeRtt, PEER_RTTS, SLOW_RTT};
use vinc_crypto::{IdentityAlg, NodeId};
use vinc_tests::SplitMix64;

const MAX: u128 = u64::MAX as u128;
const MS: u64 = 1_000_000;

fn node(p: u32) -> NodeId {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&p.to_be_bytes());
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes,
    }
}
fn peer_no(n: &NodeId) -> u32 {
    u32::from_be_bytes(n.bytes[..4].try_into().unwrap())
}

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}
fn opt(v: Option<u64>) -> String {
    v.map_or_else(|| "[]".to_owned(), limbs)
}

/// The node written from the module documentation, in `u128`.
#[derive(Default)]
struct Naive {
    tab: Vec<(u32, u128)>,
    lrtt: u128,
    tgr: u128,
    floor: u128,
}

impl Naive {
    fn put(&mut self, p: u32, v: u128) -> bool {
        if let Some(e) = self.tab.iter_mut().find(|e| e.0 == p) {
            e.1 = v;
            true
        } else if self.tab.len() < PEER_RTTS {
            self.tab.push((p, v));
            true
        } else {
            false
        }
    }
    fn hs(&mut self, p: u32, v: u128) {
        if v == 0 {
            return;
        }
        self.put(p, v);
        self.floor = 0;
        self.lrtt = if self.lrtt == 0 {
            v
        } else {
            (7 * self.lrtt + v).min(MAX) / 8
        };
    }
    fn restore(&mut self, p: u32, v: u128) -> bool {
        self.put(p, v)
    }
    fn peak(&mut self, v: u128) {
        self.tgr = v.max(self.tgr - self.tgr / 32);
    }
    fn timeout(&mut self) {
        self.floor = u128::from(FLOOR_MAX).min(u128::from(FIRST_RESEND).max(2 * self.floor));
    }
    fn krtt(&self, p: u32) -> Option<u128> {
        self.tab.iter().find(|e| e.0 == p).map(|e| e.1)
    }
    fn base(&self, p: u32) -> u128 {
        self.krtt(p).filter(|r| *r > 0).unwrap_or(self.lrtt)
    }
    fn first(&self, p: u32) -> u128 {
        u128::from(FIRST_RESEND)
            .max((2 * self.base(p)).min(MAX))
            .max(self.floor)
    }
    fn remembered(&self, p: u32) -> Option<u128> {
        let r = self.base(p).max(self.floor.div_ceil(2));
        (r > 0).then_some(r)
    }
    fn hub(&self, p: u32) -> Option<u128> {
        let r0 = self.krtt(p).filter(|r| *r > 0)?;
        Some(u128::from(HUB_RESEND).max((3 * (r0 / 2) + 20 * u128::from(MS)).min(MAX)))
    }
    fn thin_node(&self) -> bool {
        self.tgr.max(self.lrtt) >= u128::from(SLOW_RTT)
    }
    fn thin(&self, srtt: u64, min: u64) -> bool {
        srtt == 0 || self.tgr.max(self.lrtt).max(u128::from(min)).max(u128::from(srtt / 2)) >= u128::from(SLOW_RTT)
    }
}

fn val(rng: &mut SplitMix64) -> u64 {
    let slow = SLOW_RTT;
    match rng.next_u64() % 22 {
        0 | 1 => 0,
        2 => 1,
        3 | 4 => 1 + rng.next_u64() % (2 * MS),
        5 | 6 => slow - 1,
        7 | 8 => slow,
        9 => slow + 1,
        10 => 500 * MS,
        11 => 2 * slow,
        12 => 8_000 * MS,
        13 | 14 => 1 + rng.next_u64() % (3_000 * MS),
        15 => u64::MAX,
        16 => u64::MAX - 1,
        17 => u64::MAX / 8,
        18 => u64::MAX / 8 + 1,
        19 => 1 << 63,
        20 => (1 << 62) + rng.next_u64() % 1000,
        _ => rng.next_u64(),
    }
}

/// What a set of runs exercised.
#[derive(Default)]
struct Seen {
    full_refused: u32,
    saturated_avg: u32,
    floor_top: u32,
    floor_reset: u32,
    peak_kept_floor: u32,
    zero_ignored: u32,
    thin_node: u32,
    not_thin_node: u32,
    peak_zero_avg_positive: u32,
    hub_saturated: u32,
    replaced: u32,
    restored_new: u32,
}

/// The state and the readers, as one json object; the real node is checked against the naive one on the way.
fn view(real: &NodeRtt, naive: &Naive, touched: u32, rng: &mut SplitMix64) -> String {
    let peers: Vec<(u32, u64)> = real.peers().map(|(n, v)| (peer_no(n), *v)).collect();
    assert!(peers.len() <= PEER_RTTS, "the table holds more than its bound");
    assert_eq!(
        peers.iter().map(|e| (e.0, u128::from(e.1))).collect::<Vec<_>>(),
        naive.tab,
        "the table differs from the naive one"
    );
    assert_eq!(
        (
            u128::from(real.lrtt()),
            u128::from(real.tgr()),
            u128::from(real.hs_floor())
        ),
        (naive.lrtt, naive.tgr, naive.floor),
        "the numbers differ from the naive node's"
    );
    assert_eq!(real.thin_node(), naive.thin_node());
    let tab = if peers.len() <= 8 {
        peers
            .iter()
            .map(|e| format!("[{},{}]", e.0, limbs(e.1)))
            .collect::<Vec<_>>()
            .join(",")
    } else {
        String::new()
    };
    let mut q = Vec::new();
    for p in [touched, 1, 2, 9999] {
        let id = node(p);
        assert_eq!(real.krtt(&id).map(u128::from), naive.krtt(p), "krtt of {p}");
        assert_eq!(
            u128::from(real.first_resend(&id)),
            naive.first(p),
            "first_resend of {p}"
        );
        assert_eq!(
            real.remembered_for(&id).map(u128::from),
            naive.remembered(p),
            "remembered_for of {p}"
        );
        assert_eq!(real.hub_resend(&id).map(u128::from), naive.hub(p), "hub_resend of {p}");
        assert!(naive.first(p) >= u128::from(FIRST_RESEND) && naive.first(p) >= naive.floor);
        q.push(format!(
            "[{p},{},{},{},{}]",
            opt(real.krtt(&id)),
            limbs(real.first_resend(&id)),
            opt(real.remembered_for(&id)),
            opt(real.hub_resend(&id))
        ));
    }
    let (s, m) = (val(rng), val(rng));
    assert_eq!(real.thin(s, m), naive.thin(s, m));
    let v = format!(
        r#"{{"len":{},"peers":[{}],"tab":[{}],"lrtt":{},"tgr":{},"floor":{},"tn":{},"q":[{}],"th":[{},{},{}]}}"#,
        peers.len(),
        peers.iter().map(|e| e.0.to_string()).collect::<Vec<_>>().join(","),
        tab,
        limbs(real.lrtt()),
        limbs(real.tgr()),
        limbs(real.hs_floor()),
        real.thin_node(),
        q.join(","),
        limbs(s),
        limbs(m),
        real.thin(s, m)
    );
    v
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, peers: u32, fill: bool, seen: &mut Seen) {
    let mut real = NodeRtt::new(rng.next_u64());
    let mut naive = Naive::default();
    let v = view(&real, &naive, 1, rng);
    let _ = writeln!(
        out,
        r#"{{"t":"corr","run":{id},"op":"init","cap":{PEER_RTTS},"v":{v}}}"#
    );
    let mut next_new = 1u32;
    for step in 0..steps {
        let before_floor = naive.floor;
        let known: Vec<u32> = naive.tab.iter().map(|e| e.0).collect();
        let pick = |rng: &mut SplitMix64, next_new: &mut u32| -> u32 {
            if fill && (step as usize) < PEER_RTTS + 4 {
                let p = *next_new;
                *next_new += 1;
                p
            } else if !known.is_empty() && rng.next_u64().is_multiple_of(3) {
                known[(rng.next_u64() % known.len() as u64) as usize]
            } else {
                1 + (rng.next_u64() % u64::from(peers)) as u32
            }
        };
        let roll = if fill && (step as usize) < PEER_RTTS + 4 {
            rng.next_u64() % 2 * 4 // handshakes and restores only, filling the table
        } else {
            rng.next_u64() % 10
        };
        let touched;
        match roll {
            0..=3 => {
                let p = pick(rng, &mut next_new);
                let mut x = val(rng);
                if fill && (step as usize) < PEER_RTTS + 4 {
                    x = x.max(1);
                }
                touched = p;
                let was = naive.krtt(p).is_some();
                let full = naive.tab.len() == PEER_RTTS;
                let lrtt_before = naive.lrtt;
                real.note_handshake(node(p), x);
                naive.hs(p, u128::from(x));
                if x == 0 {
                    seen.zero_ignored += 1;
                } else {
                    assert_eq!(real.hs_floor(), 0, "a handshake sample left the floor up");
                    seen.floor_reset += u32::from(before_floor > 0);
                    seen.full_refused += u32::from(!was && full);
                    seen.replaced += u32::from(was);
                    seen.saturated_avg += u32::from(lrtt_before > 0 && 7 * lrtt_before + u128::from(x) > MAX);
                    assert!(naive.lrtt > 0 && naive.lrtt <= lrtt_before.max(u128::from(x)));
                }
                let v = view(&real, &naive, touched, rng);
                let _ = writeln!(
                    out,
                    r#"{{"t":"corr","run":{id},"op":"hs","p":{p},"x":{},"v":{v}}}"#,
                    limbs(x)
                );
            }
            4..=5 => {
                let p = pick(rng, &mut next_new);
                let x = val(rng);
                touched = p;
                let full = naive.tab.len() == PEER_RTTS;
                let was = naive.krtt(p).is_some();
                let (l, t, f) = (real.lrtt(), real.tgr(), real.hs_floor());
                let ok = real.restore_peer(node(p), x);
                assert_eq!(ok, naive.restore(p, u128::from(x)), "restore_peer answers differently");
                assert_eq!(ok, was || !full);
                assert_eq!(
                    (real.lrtt(), real.tgr(), real.hs_floor()),
                    (l, t, f),
                    "a restored peer moved a number"
                );
                seen.full_refused += u32::from(!ok);
                seen.restored_new += u32::from(ok && !was);
                let v = view(&real, &naive, touched, rng);
                let _ = writeln!(
                    out,
                    r#"{{"t":"corr","run":{id},"op":"restore","p":{p},"x":{},"ok":{ok},"v":{v}}}"#,
                    limbs(x)
                );
            }
            6..=7 => {
                let x = val(rng);
                touched = 1 + (rng.next_u64() % u64::from(peers)) as u32;
                real.note_peak(x);
                naive.peak(u128::from(x));
                assert!(real.tgr() >= x);
                assert_eq!(u128::from(real.hs_floor()), before_floor, "a peak moved the floor");
                seen.peak_kept_floor += u32::from(before_floor > 0);
                seen.peak_zero_avg_positive += u32::from(real.tgr() == 0 && real.lrtt() > 0);
                let v = view(&real, &naive, touched, rng);
                let _ = writeln!(out, r#"{{"t":"corr","run":{id},"op":"peak","x":{},"v":{v}}}"#, limbs(x));
            }
            _ => {
                touched = 1 + (rng.next_u64() % u64::from(peers)) as u32;
                real.note_timeout();
                naive.timeout();
                assert!(real.hs_floor() >= FIRST_RESEND && real.hs_floor() <= FLOOR_MAX);
                seen.floor_top += u32::from(real.hs_floor() == FLOOR_MAX && before_floor == u128::from(FLOOR_MAX));
                let v = view(&real, &naive, touched, rng);
                let _ = writeln!(out, r#"{{"t":"corr","run":{id},"op":"timeout","v":{v}}}"#);
            }
        }
        seen.thin_node += u32::from(naive.thin_node());
        seen.not_thin_node += u32::from(!naive.thin_node());
        seen.hub_saturated += u32::from(naive.tab.iter().any(|e| 3 * (e.1 / 2) + 20_000_000 > MAX));
        // the floor is zero or one of its five values, whatever happened
        assert!(
            [0, 500, 1000, 2000, 4000, 8000].contains(&(naive.floor / u128::from(MS)))
                && naive.floor % u128::from(MS) == 0
        );
    }
}

#[test]
fn the_node_round_trips_match_the_models() {
    let mut rng = SplitMix64::new(0x7274_7400_0001);
    let mut out = String::new();
    let mut seen = Seen::default();
    for id in 1..=160u32 {
        run(&mut rng, &mut out, id, 70, 5, false, &mut seen);
    }
    for id in 500..503u32 {
        run(&mut rng, &mut out, id, 330, 300, true, &mut seen);
    }
    assert!(seen.full_refused > 0, "the table never refused a peer");
    assert!(seen.replaced > 0 && seen.restored_new > 0);
    assert!(seen.saturated_avg > 0, "the average never saturated");
    assert!(seen.floor_top > 0, "the floor never stayed at its ceiling");
    assert!(seen.floor_reset > 0, "a handshake sample never reset a raised floor");
    assert!(seen.peak_kept_floor > 0, "a peak was never seen with a raised floor");
    assert!(seen.zero_ignored > 0);
    assert!(seen.thin_node > 0 && seen.not_thin_node > 0);
    assert!(
        seen.peak_zero_avg_positive > 0,
        "a zero peak beside a positive average never happened"
    );
    assert!(seen.hub_saturated > 0, "the hub resend never saturated");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("rtt.ndjson"), &out).unwrap();
    }
}
