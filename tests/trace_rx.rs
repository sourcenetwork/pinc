//! Trace generation for the received-packet tracker: seeded random runs of real `ReceivedPackets` (`pinc-transport`,
//! built with the `trace` feature), recorded as ndjson (`rx.ndjson`) for the TLA+ trace check (`TraceRx.tla`) and the
//! Lean replay (`Pinc/TraceRx.lean`).
//!
//! A run receives packets (in order, with gaps, old, duplicated, bulk, ack-eliciting or not, and a sparse mode that
//! fills the range set so the oldest range is forgotten), sets the minimum round trip and the acknowledgement
//! interval, sends acknowledgements, takes the peer's acknowledgements of ours, and queries the ranges to report,
//! the deadline and the numbers seen. After every call the tracker shows its state (`trace_view`); the checkers
//! replay each call with the operators of the model and require the state and the outcome recorded. A second file
//! (`rx_wide.ndjson`, read by the Lean replay only: the TLA+ checker has 32-bit integers) holds packet numbers up to
//! 2^62 and times up to `u64::MAX`.
//!
//! The test asserts what it can itself (the range set is exact against a plain set, never over its bound, the
//! ranges reported are the newest) so it is meaningful without the proof tools.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::many_single_char_names,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    unreachable_pub
)]

use std::collections::BTreeSet;
use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::recovery::trace::RxView;
use pinc_transport::recovery::{MS, ReceivedPackets, RxOutcome, RxPacket, SECOND};

fn b(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

fn opt(x: Option<u64>) -> i128 {
    x.map_or(-1, i128::from)
}

/// The largest value of a 32-bit checker integer. A deadline above it is recorded as it, and the model's saturating
/// arithmetic reaches it in the same cases; the run's own clock stays far below it.
const TOP: u64 = (1 << 31) - 1;

/// `wide` runs (read by the Lean replay only) record the values as they are.
fn opt_top(x: Option<u64>, wide: bool) -> i128 {
    opt(x.map(|v| if wide { v } else { v.min(TOP) }))
}

fn pairs<I: IntoIterator<Item = (u64, u64)>>(it: I) -> String {
    let v: Vec<String> = it.into_iter().map(|(a, c)| format!("[{a},{c}]")).collect();
    format!("[{}]", v.join(","))
}

fn view_json(v: &RxView) -> String {
    view_json_w(v, false)
}

fn view_json_w(v: &RxView, wide: bool) -> String {
    format!(
        r#"{{"items":{},"floor":{},"pending":{},"due":{},"every":{},"mrtt":{},"sent":{},"conf":{},"cf":{}}}"#,
        pairs(v.items.iter().copied()),
        v.floor,
        v.pending,
        opt_top(v.due, wide),
        v.every.map_or(-1, i64::from),
        opt(v.min_rtt),
        pairs(v.sent.iter().copied()),
        pairs(v.confirms.iter().copied()),
        opt(v.confirmed_floor)
    )
}

struct Run<'a, const N: usize> {
    rx: ReceivedPackets<N>,
    out: &'a mut String,
    id: u32,
    seen: BTreeSet<u64>,
    now: u64,
    apn: u64,
    dup: u32,
    new: u32,
    forgot: u32,
    thin: u32,
}

impl<const N: usize> Run<'_, N> {
    fn log(&mut self, body: &str) {
        let v = view_json(&self.rx.trace_view());
        let _ = writeln!(self.out, r#"{{"t":"txrx","run":{},{body},"v":{v}}}"#, self.id);
    }

    fn recv(&mut self, pn: u64, elic: bool, bytes: u32) {
        let before = self.rx.trace_view();
        let r = self.rx.on_packet_received(RxPacket {
            pn,
            now: self.now,
            ack_eliciting: elic,
            stream_bytes: bytes,
        });
        let name = match &r {
            Ok(RxOutcome::New) => {
                self.new += 1;
                // a packet reported New was not seen and is not below the floor
                assert!(
                    !self.seen.contains(&pn) && pn >= before.floor,
                    "New for a number seen or forgotten"
                );
                self.seen.insert(pn);
                "New"
            }
            Ok(RxOutcome::Duplicate) => {
                self.dup += 1;
                "Duplicate"
            }
            Err(_) => "PacketNumberOutOfRange",
        };
        let after = self.rx.trace_view();
        if after.floor > before.floor {
            self.forgot += 1;
        }
        self.log(&format!(
            r#""op":"recv","pn":{pn},"now":{},"elic":{},"bytes":{bytes},"out":"{name}""#,
            self.now,
            b(elic)
        ));
        self.check_exact();
    }

    /// The range set is exactly the numbers seen at or above the floor; every number seen reads as received.
    fn check_exact(&self) {
        let v = self.rx.trace_view();
        assert!(v.items.len() <= N);
        let mut covered = BTreeSet::new();
        for w in v.items.windows(2) {
            assert!(w[0].1 < w[1].0, "ranges not disjoint, sorted and merged");
        }
        for (s, e) in &v.items {
            assert!(s < e);
            if e - s < 4096 {
                covered.extend(*s..*e);
            }
        }
        if v.items.iter().all(|(s, e)| e - s < 4096) {
            let want: BTreeSet<u64> = self.seen.iter().copied().filter(|p| *p >= v.floor).collect();
            assert_eq!(covered, want, "the ranges are not the numbers seen");
        }
        for p in self.seen.iter().take(200) {
            assert!(self.rx.contains(*p));
        }
    }

    fn query(&mut self, probes: &[u64]) {
        let rgs: Vec<_> = self.rx.ack_ranges(self.now).collect();
        let v = self.rx.trace_view();
        if rgs.len() < v.items.len() && rgs.len() < 32 {
            self.thin += 1;
        }
        let has: Vec<String> = probes
            .iter()
            .map(|p| format!("[{p},{}]", b(self.rx.contains(*p))))
            .collect();
        let body = format!(
            r#""op":"query","now":{},"rgs":{},"dl":{},"pend":{},"due":{},"lg":{},"rc":{},"has":[{}]"#,
            self.now,
            pairs(rgs.iter().map(|r| (*r.start(), *r.end()))),
            opt_top(self.rx.ack_deadline(), false),
            b(self.rx.ack_pending()),
            b(self.rx.ack_due(self.now)),
            opt(self.rx.largest()),
            self.rx.range_count(),
            has.join(",")
        );
        // the ranges reported are the newest, largest first
        for (k, r) in rgs.iter().enumerate() {
            let it = v.items[v.items.len() - 1 - k];
            assert_eq!((*r.start(), *r.end() + 1), it);
        }
        self.log(&body);
    }
}

fn run<const N: usize>(seed: u64, out: &mut String, id: u32, steps: u32, sparse: bool) -> (u32, u32, u32, u32) {
    let mut rng = SplitMix64::traced(seed);
    let mut r = Run::<N> {
        rx: ReceivedPackets::new(),
        out,
        id,
        seen: BTreeSet::new(),
        now: 0,
        apn: 0,
        dup: 0,
        new: 0,
        forgot: 0,
        thin: 0,
    };
    let _ = writeln!(
        r.out,
        r#"{{"t":"txrx","run":{id},"op":"init","cap":{N},"v":{}}}"#,
        view_json(&r.rx.trace_view())
    );
    let mut next = 0u64;
    for _ in 0..steps {
        match rng.next_u64() % 100 {
            0..=54 => {
                let pn = if sparse {
                    next += 2;
                    next
                } else {
                    match rng.next_u64() % 10 {
                        0..=4 => {
                            next += 1;
                            next
                        }
                        5 | 6 => {
                            next += 2 + rng.next_u64() % 5;
                            next
                        }
                        7 => rng.next_u64() % (next + 2),
                        _ => next.saturating_sub(rng.next_u64() % 4),
                    }
                };
                let elic = !rng.next_u64().is_multiple_of(5);
                let bytes = [0u32, 500, 1000, 1400][(rng.next_u64() % 4) as usize];
                r.recv(pn, elic, bytes);
                if r.now > 0 && rng.next_u64().is_multiple_of(3) {
                    r.recv(pn, elic, bytes);
                }
            }
            55..=64 => {
                // the checker's integers end at 2^31 ns: one jump of 2 s per run (it ages the confirmations that
                // came early), and small steps before and after it, none past the end of the range
                let d = [0, 1, 10 * MS, 30 * MS, 2 * SECOND][(rng.next_u64() % 5) as usize];
                if r.now + d <= 2_140_000_000 && (d < SECOND || r.now <= 100 * MS) {
                    r.now += d;
                }
            }
            65..=69 => {
                let m = [None, Some(10 * MS), Some(300 * MS), Some(2 * SECOND)][(rng.next_u64() % 4) as usize];
                r.rx.set_min_rtt(m);
                r.log(&format!(r#""op":"rtt","m":{}"#, opt(m)));
            }
            70..=72 => {
                let e = [None, Some(0u32), Some(1), Some(4)][(rng.next_u64() % 4) as usize];
                r.rx.set_every(e);
                r.log(&format!(r#""op":"every","e":{}"#, e.map_or(-1, i64::from)));
            }
            73..=84 => {
                let apn = r.apn;
                r.apn += 1;
                r.rx.on_ack_sent(apn, r.now);
                r.log(&format!(r#""op":"acksent","apn":{apn},"now":{}"#, r.now));
            }
            85..=92 => {
                let mut rgs = Vec::new();
                let mut hi = r.apn;
                for _ in 0..(rng.next_u64() % 3) {
                    if hi == 0 {
                        break;
                    }
                    let top = rng.next_u64() % (hi + 1);
                    let low = top.saturating_sub(rng.next_u64() % 3);
                    rgs.push(low..=top);
                    hi = low.saturating_sub(1);
                    if low == 0 {
                        break;
                    }
                }
                if r.now + MS <= 2_140_000_000 {
                    r.now += MS;
                }
                r.rx.on_peer_ack(r.now, &rgs);
                let shown = pairs(rgs.iter().map(|g| (*g.start(), *g.end())));
                r.log(&format!(r#""op":"peer","now":{},"rgs":{shown}"#, r.now));
            }
            _ => {
                let probes: Vec<u64> = (0..4).map(|_| rng.next_u64() % (next + 4)).collect();
                r.query(&probes);
            }
        }
    }
    r.query(&[0, 1, 2, next]);
    r.log(r#""op":"end""#);
    (r.new, r.dup, r.forgot, r.thin)
}

/// Packet numbers up to 2^62 and times near `u64::MAX`: Lean only.
fn wide(out: &mut String) {
    let mut rx = ReceivedPackets::<4>::new();
    let id = 900;
    let log = |rx: &ReceivedPackets<4>, out: &mut String, body: &str| {
        let _ = writeln!(
            out,
            r#"{{"t":"txrx","run":{id},{body},"v":{}}}"#,
            view_json_w(&rx.trace_view(), true)
        );
    };
    let _ = writeln!(
        out,
        r#"{{"t":"txrx","run":{id},"op":"init","cap":4,"v":{}}}"#,
        view_json_w(&rx.trace_view(), true)
    );
    let max_pn = (1u64 << 62) - 1;
    for (pn, now) in [
        (max_pn, u64::MAX - 5),
        (max_pn + 1, 0),
        (max_pn - 1, u64::MAX),
        (0, 7),
        (max_pn, 9),
        (max_pn - 3, u64::MAX - 1),
    ] {
        let r = rx.on_packet_received(RxPacket {
            pn,
            now,
            ack_eliciting: true,
            stream_bytes: 1200,
        });
        let name = match r {
            Ok(RxOutcome::New) => "New",
            Ok(RxOutcome::Duplicate) => "Duplicate",
            Err(_) => "PacketNumberOutOfRange",
        };
        log(
            &rx,
            out,
            &format!(r#""op":"recv","pn":{pn},"now":{now},"elic":true,"bytes":1200,"out":"{name}""#),
        );
    }
    rx.set_min_rtt(Some(u64::MAX));
    log(&rx, out, &format!(r#""op":"rtt","m":{}"#, u64::MAX));
    let _ = rx.on_packet_received(RxPacket {
        pn: 5,
        now: u64::MAX - 1,
        ack_eliciting: true,
        stream_bytes: 0,
    });
    log(
        &rx,
        out,
        &format!(
            r#""op":"recv","pn":5,"now":{},"elic":true,"bytes":0,"out":"New""#,
            u64::MAX - 1
        ),
    );
    rx.on_ack_sent(1, u64::MAX);
    log(&rx, out, &format!(r#""op":"acksent","apn":1,"now":{}"#, u64::MAX));
    rx.on_peer_ack(u64::MAX, &std::iter::once(0..=1).collect::<Vec<_>>());
    log(&rx, out, &format!(r#""op":"peer","now":{},"rgs":[[0,1]]"#, u64::MAX));
    let rgs: Vec<_> = rx.ack_ranges(u64::MAX).collect();
    log(
        &rx,
        out,
        &format!(
            r#""op":"query","now":{},"rgs":{},"dl":{},"pend":{},"due":{},"lg":{},"rc":{},"has":[]"#,
            u64::MAX,
            pairs(rgs.iter().map(|r| (*r.start(), *r.end()))),
            opt(rx.ack_deadline()),
            b(rx.ack_pending()),
            b(rx.ack_due(u64::MAX)),
            opt(rx.largest()),
            rx.range_count()
        ),
    );
}

#[test]
fn received_packet_runs_match_the_models() {
    let mut out = String::new();
    let (mut new, mut dup, mut forgot, mut thin) = (0, 0, 0, 0);
    let mut add = |t: (u32, u32, u32, u32)| {
        new += t.0;
        dup += t.1;
        forgot += t.2;
        thin += t.3;
    };
    for id in 1..=60u32 {
        let seed = 0x5258_0000 + u64::from(id);
        match id % 4 {
            0 => add(run::<2>(seed, &mut out, id, 120, id.is_multiple_of(8))),
            1 => add(run::<4>(seed, &mut out, id, 200, id.is_multiple_of(5))),
            2 => add(run::<3>(seed, &mut out, id, 160, false)),
            _ => add(run::<128>(seed, &mut out, id, 400, id.is_multiple_of(3))),
        }
    }
    // the long sparse runs fill the real set of 128 ranges, so the oldest is forgotten and a report is thinned
    add(run::<128>(0x5258_ffff, &mut out, 99, 1200, true));
    let mut wide_out = String::new();
    wide(&mut wide_out);
    for needle in [
        r#""out":"New""#,
        r#""out":"Duplicate""#,
        r#""op":"peer""#,
        r#""op":"acksent""#,
    ] {
        assert!(
            pinc_tests::soaking() || out.contains(needle),
            "the runs never reach {needle}"
        );
    }
    assert!(wide_out.contains(r#""out":"PacketNumberOutOfRange""#));
    assert!(
        pinc_tests::soaking() || new > 0 && dup > 0 && forgot > 0 && thin > 0,
        "new {new} dup {dup} forgot {forgot} thin {thin}"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("rx.ndjson"), &out).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("rx_wide.ndjson"), &wide_out).unwrap();
    }
}
