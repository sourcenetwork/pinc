//! Model-based tests of the received-packet tracker's range set and the ACK ranges it reports: a real
//! `ReceivedPackets<N>` (`vinc-transport`, built with the `trace` feature) driven along every edge of the state graph
//! of `proofs/tla/MbtRanges.tla`.
//!
//! TLC enumerates every state the operators of `RxOps.tla` reach at the capacity of a config and writes the graph;
//! `scripts/mbt.py` turns it into paths from the empty tracker that take every edge, which `scripts/proofs.sh` writes
//! to the directory `VINC_MBT_DIR`: `ranges.ndjson` from `MbtRanges.cfg` (2 ranges) and `ranges_wide.ndjson` from
//! `MbtRanges_wide.cfg` (3 ranges). This test runs each path on a fresh tracker of the config's capacity: after every
//! call the result must be the model's, and the whole tracker (`trace_view`: the ranges, the floor, the table of our
//! acknowledgements, the confirmations and the floor they made, and the acknowledgement policy state, which these
//! calls leave at its start), `largest` and `range_count` must be the model's state. It stops at the first difference
//! and names the file, the case, the step and the calls that led there. Without `VINC_MBT_DIR` it checks nothing.
//!
//! The model's numbers stand for the code's as `MbtRanges.tla` says: packet numbers are the code's, and model time `t`
//! is `origin + t * MS` (the model's `MS` is 1 and its `SEC` 1000, the code's `SECOND` is `1000 * MS`), the origin
//! being 0 or an odd time, by case.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub
)]

use std::fmt::Write as _;
use std::ops::RangeInclusive;

use vinc_tests::{Json, MbtCase, mbt_cases};
use vinc_transport::recovery::{MAX_ACK_RANGES, MS, ReceivedPackets, RxOutcome, RxPacket, SECOND};

fn num(v: &Json) -> u64 {
    v.u64().unwrap()
}

/// A number that is `-1` for none in the model.
fn opt(v: &Json) -> Option<u64> {
    v.u64()
}

/// The pairs of a model sequence of pairs.
fn pairs(v: &Json) -> Vec<(u64, u64)> {
    v.arr()
        .unwrap()
        .iter()
        .map(|p| {
            let p = p.arr().unwrap();
            (num(&p[0]), num(&p[1]))
        })
        .collect()
}

/// The calls of `case` up to step `upto`, for a failure message.
fn calls(case: &MbtCase, upto: usize) -> String {
    let mut s = String::new();
    for (i, st) in case.steps.iter().take(upto + 1).enumerate() {
        let _ = write!(s, "\n  {i}: {st}");
    }
    s
}

/// The model's tracker `x` against the real one; `origin` is the code's time for the model's time 0.
fn same<const N: usize>(rx: &ReceivedPackets<N>, x: &Json, origin: u64, at: &dyn Fn() -> String) {
    let f = |n: &str| x.get(n).unwrap();
    let v = rx.trace_view();
    assert_eq!(v.items, pairs(f("items")), "{}: the ranges differ", at());
    assert_eq!(v.floor, num(f("floor")), "{}: the floor differs", at());
    assert_eq!(
        v.sent,
        pairs(f("sent")),
        "{}: the table of our acknowledgements differs",
        at()
    );
    let conf: Vec<(u64, u64)> = pairs(f("conf"))
        .into_iter()
        .map(|(t, n)| (origin + t * MS, n))
        .collect();
    assert_eq!(v.confirms, conf, "{}: the confirmations differ", at());
    assert_eq!(v.confirmed_floor, opt(f("cf")), "{}: the confirmed floor differs", at());
    // the acknowledgement policy: not ack-eliciting packets leave it at its start
    assert_eq!(
        (v.pending, v.due, v.every, v.min_rtt),
        (0, None, None, None),
        "{}: the acknowledgement policy state moved",
        at()
    );
    assert_eq!(num(f("pending")), 0, "{}: the model's policy state moved", at());
    assert_eq!(rx.range_count(), v.items.len(), "{}: range_count differs", at());
    assert_eq!(
        rx.largest(),
        v.items.last().map(|iv| iv.1 - 1),
        "{}: largest differs",
        at()
    );
}

/// Runs one case of `file` on a fresh tracker of `N` ranges; returns the number of calls.
fn run<const N: usize>(file: &str, case: &MbtCase, init: &Json) -> usize {
    let origin = [0, 5 * SECOND + 123_457][(case.id % 2) as usize];
    let time = |t: u64| origin + t * MS;
    let mut rx = ReceivedPackets::<N>::new();
    let who = format!("{file} case {}", case.id);
    same(&rx, init.get("x").unwrap(), origin, &|| {
        format!("{who}: the empty tracker")
    });
    for (i, st) in case.steps.iter().enumerate() {
        let a = &st.args;
        match (st.call.as_str(), a.as_slice()) {
            ("CallRecv", [pn, new]) => {
                let got = rx
                    .on_packet_received(RxPacket {
                        pn: num(pn),
                        now: time(0),
                        ack_eliciting: false,
                        stream_bytes: 0,
                    })
                    .unwrap();
                assert_eq!(
                    got == RxOutcome::New,
                    new.bool().unwrap(),
                    "{who} step {i}: the packet came back {got:?}; calls:{}",
                    calls(case, i)
                );
            }
            ("CallContains", [pn, seen]) => {
                assert_eq!(
                    rx.contains(num(pn)),
                    seen.bool().unwrap(),
                    "{who} step {i}: contains differs; calls:{}",
                    calls(case, i)
                );
            }
            ("CallAckRanges", [now, rgs]) => {
                let got: Vec<(u64, u64)> = rx.ack_ranges(time(num(now))).map(|r| (*r.start(), *r.end())).collect();
                assert!(got.len() <= MAX_ACK_RANGES);
                assert_eq!(
                    got,
                    pairs(rgs),
                    "{who} step {i}: the ranges reported differ; calls:{}",
                    calls(case, i)
                );
            }
            ("CallAckSent", [apn, now]) => rx.on_ack_sent(num(apn), time(num(now))),
            ("CallPeerAck", [now, rgs]) => {
                let v: Vec<RangeInclusive<u64>> = pairs(rgs).into_iter().map(|(s, e)| s..=e).collect();
                rx.on_peer_ack(time(num(now)), &v);
            }
            _ => panic!("{who}: a call the test does not know: {st}"),
        }
        same(&rx, st.state.get("x").unwrap(), origin, &|| {
            format!("{who} after step {i}; calls:{}", calls(case, i))
        });
    }
    case.steps.len()
}

/// Walks every case of `file` on trackers of `N` ranges; false when `VINC_MBT_DIR` is unset.
fn walk<const N: usize>(file: &str) -> bool {
    let Some(cases) = mbt_cases(file) else {
        return false;
    };
    let mut cases = cases.unwrap();
    let head = cases.head.clone();
    let c = head.get("constants").unwrap();
    let k = |n: &str| num(c.get(n).unwrap());
    assert_eq!(k("CAP"), N as u64, "{file}: the model's capacity is not this test's");
    assert_eq!(
        (k("MS"), k("SEC"), k("MAXACK")),
        (1, 1000, MAX_ACK_RANGES as u64),
        "{file}: the model's time unit or ACK limit is not the code's"
    );
    assert_eq!(SECOND, 1000 * MS);
    let init = head.get("init").unwrap();
    let (mut n, mut steps) = (0u64, 0usize);
    for case in &mut cases {
        steps += run::<N>(file, &case.unwrap(), init);
        n += 1;
    }
    let count = |f: &str| num(head.get(f).unwrap());
    assert_eq!(
        (n, steps as u64),
        (count("cases"), count("steps")),
        "{file}: the file ends early"
    );
    eprintln!(
        "mbt_ranges: {file}: {n} cases, {steps} calls, every one of the {} edges between the {} states of the graph",
        count("edges"),
        count("states")
    );
    true
}

#[test]
fn the_received_ranges_follow_every_edge_of_the_model() {
    // MbtRanges.cfg (2 ranges) and MbtRanges_wide.cfg (3 ranges)
    let walked = [walk::<2>("ranges.ndjson"), walk::<3>("ranges_wide.ndjson")];
    if walked == [false; 2] {
        eprintln!("mbt_ranges: VINC_MBT_DIR is not set, nothing checked (scripts/proofs.sh generates the cases)");
    }
}
