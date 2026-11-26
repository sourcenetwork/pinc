//! `pinc-transport` recovery: the sent-packet engine (`Recovery`) and the received-packet set (`ReceivedPackets`)
//! against reference models, driven by sequences of sends, acknowledgements, timers and path events on a clock
//! that may stand still or jump far.
//!
//! Where the expected behaviour comes from:
//! - `recovery` module docs: "bytes sent = bytes acknowledged + bytes in flight + bytes declared lost, always. A late
//!   acknowledgement moves bytes from lost to acknowledged"; "The congestion window never drops below `MIN_CWND` and
//!   never exceeds `MAX_CWND`"; "All arithmetic is integer and cannot overflow or panic".
//! - `Event` docs: `Acked` "the packet was acknowledged", `LateAcked` "a packet already declared lost was acknowledged
//!   after all", `Lost` "the packet was declared lost", with `requeue` "false for a repair packet or a path MTU probe".
//!   `Summary` counts the packets and bytes of one call.
//! - `ack` module docs: "An acknowledgement of a packet number that is not in flight and not a ghost is ignored".
//! - `pto` module docs: the probe timeout "never exceeds 2 s, except when the minimum round trip is 250 ms or more or
//!   the smoothed round trip is 1 s or more, where the cap is `max(2 s, 2 * srtt)`".
//! - `recovery::deadline_after`: "A deadline saturated at `u64::MAX` could never be later than a call made at
//!   `u64::MAX`, so it would fire on every call": a timer that fired at its deadline moves on.
//! - `recv` module docs: "everything below `floor` is treated as already received, so a forgotten packet is dropped as
//!   a duplicate rather than processed twice"; an acknowledgement is due "at once when the packet number is not the
//!   one after the largest received", otherwise within `max_ack_delay`; "Reported ranges are largest first and at
//!   most `MAX_ACK_RANGES`"; "the set never holds more than `RANGES` ranges".
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]

use std::collections::{BTreeMap, BTreeSet};
use std::ops::RangeInclusive;

use ephyra::prelude::*;
use ephyra::{Arbitrary, gens};
use pinc_transport::recovery::{
    Event, FrameRef, FrameRefs, INITIAL_RTT, MAX_ACK_RANGES, MAX_CWND, MIN_CWND, MS, PathKind, ReceivedPackets,
    Recovery, RxOutcome, RxPacket, SECOND, Sent, Summary, max_ack_delay,
};

/// A clock step: mostly standing still or small, sometimes seconds, rarely a jump of years.
fn clock_gap() -> ephyra::BoxGen<u64> {
    gens::frequency(vec![
        (3, gens::constant(0u64).boxed()),
        (6, gens::int(0u64..=50 * MS).boxed()),
        (2, gens::int(0u64..=5 * SECOND).boxed()),
        (1, gens::int(0u64..=(1u64 << 45)).boxed()),
    ])
    .boxed()
}

#[derive(Clone, Debug, Arbitrary)]
enum RecOp {
    Send {
        #[ephyra(gen = gens::int(1u8..=4))]
        count: u8,
        #[ephyra(gen = gens::frequency(vec![(4, gens::int(1u32..=1500).boxed()), (1, gens::int(0u32..=65_535).boxed()), (1, gens::edges(0u32..=u32::MAX).boxed())]))]
        size: u32,
        #[ephyra(gen = gens::int(0u8..=3))]
        path: u8,
        #[ephyra(gen = gens::bool_with(0.1))]
        repair: bool,
        #[ephyra(gen = gens::bool_with(0.1))]
        probe: bool,
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    Untracked {
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    Ack {
        /// (distance below the previous range, length) pairs from the top.
        #[ephyra(gen = gens::vec((gens::frequency(vec![(4, gens::int(0u64..=4).boxed()), (1, gens::int(0u64..=200).boxed())]), gens::int(0u64..=8))).len(0..=5))]
        ranges: Vec<(u64, u64)>,
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    /// Run the timer at its own deadline.
    Fire,
    /// Run the timer at an arbitrary time.
    Timeout {
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    Flush {
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    ResendOffPath {
        #[ephyra(gen = gens::int(0u8..=3))]
        path: u8,
        #[ephyra(gen = gens::int(0usize..=8))]
        limit: usize,
    },
    Switch {
        #[ephyra(gen = gens::int(0u8..=3))]
        path: u8,
    },
    Follow {
        #[ephyra(gen = gens::int(0u8..=3))]
        path: u8,
    },
    Sleep(#[ephyra(gen = gens::bool())] bool),
    Dark(#[ephyra(gen = gens::bool())] bool),
    Peer {
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    Mtu(#[ephyra(gen = gens::frequency(vec![(3, gens::int(1200u64..=9000).boxed()), (1, gens::edges(0u64..=u64::MAX).boxed())]))] u64),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum St {
    InFlight,
    Lost,
    Done,
}

#[derive(Clone, Debug)]
struct Pkt {
    size: u32,
    st: St,
    repair: bool,
    probe: bool,
    frames: FrameRefs,
}

/// The reference model of the recorded packets.
struct Model {
    pkts: BTreeMap<u64, Pkt>,
    acked_bytes: u128,
    sent_bytes: u128,
    node_rtt: u64,
}

impl Model {
    fn in_flight(&self) -> (u64, u32) {
        self.pkts
            .values()
            .filter(|p| p.st == St::InFlight)
            .fold((0, 0), |(b, n), p| (b + u64::from(p.size), n + 1))
    }
}

fn frames_for(pn: u64, size: u32) -> FrameRefs {
    let mut f = FrameRefs::new();
    f.push(FrameRef::Stream {
        id: pn % 3 * 4,
        offset: pn.wrapping_mul(1000),
        len: size,
        fin: pn % 7 == 0,
    })
    .unwrap();
    if pn % 2 == 0 {
        f.push(FrameRef::Control { kind: 1, id: pn }).unwrap();
    }
    f
}

/// Check every event of one call against the model and return the summary they add up to. `ranges` is `Some` for
/// an acknowledgement (the only call that may acknowledge).
fn apply(model: &mut Model, events: &[(u8, u64, u32, bool, bool, FrameRefs)], ranges: Option<&[RangeInclusive<u64>]>) -> Summary {
    let mut s = Summary::default();
    for &(kind, pn, size, requeue, probe, ref frames) in events {
        let in_ranges = ranges.is_some_and(|r| r.iter().any(|r| r.contains(&pn)));
        let p = model.pkts.get_mut(&pn);
        assert!(p.is_some(), "an event names packet {pn}, which was never recorded");
        let p = p.unwrap();
        match kind {
            0 => {
                assert!(in_ranges, "packet {pn} acknowledged outside the acknowledged ranges");
                assert_eq!(p.st, St::InFlight, "packet {pn} acknowledged while not in flight");
                assert_eq!(size, p.size, "acknowledged size of {pn}");
                assert_eq!(probe, p.probe, "mtu_probe flag of acknowledged {pn}");
                assert_eq!(*frames, p.frames, "frames of acknowledged {pn}");
                p.st = St::Done;
                s.acked_packets += 1;
                s.acked_bytes += u64::from(size);
                model.acked_bytes += u128::from(size);
            },
            1 => {
                assert!(in_ranges, "packet {pn} late-acknowledged outside the acknowledged ranges");
                assert_eq!(p.st, St::Lost, "packet {pn} late-acknowledged while not lost");
                assert!(
                    frames.iter().all(|f| p.frames.as_slice().contains(f)),
                    "late-acknowledged {pn} names frames it never carried"
                );
                p.st = St::Done;
                s.late_acked_packets += 1;
                model.acked_bytes += u128::from(p.size);
            },
            _ => {
                assert_eq!(p.st, St::InFlight, "packet {pn} declared lost while not in flight");
                assert_eq!(size, p.size, "lost size of {pn}");
                assert_eq!(requeue, !p.repair && !p.probe, "requeue flag of lost {pn}");
                assert_eq!(probe, p.probe, "mtu_probe flag of lost {pn}");
                assert_eq!(*frames, p.frames, "frames of lost {pn}");
                p.st = St::Lost;
                s.lost_packets += 1;
                s.lost_bytes += u64::from(size);
            },
        }
    }
    s
}

type Log = Vec<(u8, u64, u32, bool, bool, FrameRefs)>;

fn logger(log: &mut Log) -> impl FnMut(Event<'_>) + '_ {
    |e| match e {
        Event::Acked {
            pn, size, frames, mtu_probe, ..
        } => log.push((0, pn, size, false, mtu_probe, *frames)),
        Event::LateAcked { pn, frames } => log.push((1, pn, 0, false, false, *frames)),
        Event::Lost {
            pn,
            size,
            frames,
            requeue,
            mtu_probe,
        } => log.push((2, pn, size, requeue, mtu_probe, *frames)),
    }
}

/// The documented ceiling of the probe timeout.
fn pto_ceiling<const N: usize>(rec: &Recovery<N>, node_rtt: u64) -> u64 {
    let rtt = rec.rtt();
    let srtt = if rtt.has_sample() { rtt.smoothed() } else { INITIAL_RTT.max(node_rtt.saturating_mul(2)) };
    let slow = rtt.min_rtt().is_some_and(|m| m >= 250 * MS) || srtt >= SECOND;
    if slow { (2 * SECOND).max(srtt.saturating_mul(2)) } else { 2 * SECOND }
}

fn run_recovery(start: u64, node_rtt: u64, ops: &[RecOp]) {
    let mut rec = Recovery::<48>::new(1200);
    rec.set_path_kind(1, PathKind::Relay).unwrap();
    rec.set_path_kind(3, PathKind::Relay).unwrap();
    if node_rtt > 0 {
        rec.set_node_rtt(node_rtt);
    }
    let mut model = Model {
        pkts: BTreeMap::new(),
        acked_bytes: 0,
        sent_bytes: 0,
        node_rtt,
    };
    let mut now = start;
    for (step, op) in ops.iter().enumerate() {
        let mut log = Log::new();
        let mut ack_ranges: Option<Vec<RangeInclusive<u64>>> = None;
        let mut summary: Option<Summary> = None;
        let mut fired_at: Option<u64> = None;
        match *op {
            RecOp::Send {
                count,
                size,
                path,
                repair,
                probe,
                gap,
            } => {
                now = now.saturating_add(gap);
                for _ in 0..count {
                    let pn = rec.next_pn();
                    let frames = frames_for(pn, size);
                    let p = Sent {
                        pn,
                        time: now,
                        size,
                        path,
                        is_repair: repair,
                        is_mtu_probe: probe,
                        frames,
                    };
                    let room = rec.ring_has_room();
                    match rec.on_packet_sent(p) {
                        Ok(()) => {
                            model.sent_bytes += u128::from(size);
                            model.pkts.insert(pn, Pkt {
                                size,
                                st: St::InFlight,
                                repair,
                                probe,
                                frames,
                            });
                        },
                        Err(e) => {
                            assert!(!room, "step {step}: a send refused with room in the ring: {e:?}");
                        },
                    }
                }
            },
            RecOp::Untracked { gap } => {
                now = now.saturating_add(gap);
                assert!(rec.on_packet_untracked(rec.next_pn()).is_ok(), "step {step}: untracked send refused");
            },
            RecOp::Ack { ref ranges, gap } => {
                now = now.saturating_add(gap);
                let Some(top) = rec.largest_sent() else { continue };
                let mut out = Vec::new();
                let mut cursor = Some(top);
                for &(below, len) in ranges {
                    let Some(c) = cursor else { break };
                    let Some(end) = c.checked_sub(below) else { break };
                    let start = end.saturating_sub(len);
                    out.push(start..=end);
                    cursor = start.checked_sub(2);
                }
                let r = rec.on_ack_received(now, out.iter().cloned(), logger(&mut log));
                assert!(r.is_ok(), "step {step}: a valid acknowledgement refused: {r:?}");
                summary = r.ok();
                ack_ranges = Some(out);
            },
            RecOp::Fire => {
                if let Some(t) = rec.next_timeout() {
                    now = now.max(t);
                    summary = Some(rec.on_timeout(now, logger(&mut log)).summary);
                    fired_at = Some(now);
                }
            },
            RecOp::Timeout { gap } => {
                now = now.saturating_add(gap);
                summary = Some(rec.on_timeout(now, logger(&mut log)).summary);
            },
            RecOp::Flush { gap } => {
                now = now.saturating_add(gap);
                summary = Some(rec.flush_in_flight(now, logger(&mut log)));
            },
            RecOp::ResendOffPath { path, limit } => {
                let s = rec.resend_off_path(now, path, limit, logger(&mut log));
                assert!(s.lost_packets as usize <= limit, "step {step}: resend_off_path lost more than its limit");
                summary = Some(s);
            },
            RecOp::Switch { path } => {
                rec.switch_path(path).unwrap();
            },
            RecOp::Follow { path } => rec.follow_path(path).unwrap(),
            RecOp::Sleep(b) => rec.set_peer_asleep(b),
            RecOp::Dark(b) => rec.set_link_down(b),
            RecOp::Peer { gap } => {
                now = now.saturating_add(gap);
                rec.note_peer_activity(now);
            },
            RecOp::Mtu(m) => rec.set_max_datagram_size(m),
        }
        let expect = apply(&mut model, &log, ack_ranges.as_deref());
        if let Some(s) = summary {
            assert_eq!(s, expect, "step {step}: the summary differs from the events reported");
        } else {
            assert!(log.is_empty(), "step {step}: events from a call that reports none");
        }
        let (bytes, packets) = model.in_flight();
        assert_eq!(rec.bytes_in_flight(), bytes, "step {step}: bytes in flight");
        assert_eq!(rec.packets_in_flight(), packets, "step {step}: packets in flight");
        assert_eq!(rec.bytes_sent(), model.sent_bytes, "step {step}: bytes sent");
        assert_eq!(rec.bytes_acked(), model.acked_bytes, "step {step}: bytes acknowledged");
        assert_eq!(
            rec.bytes_sent(),
            rec.bytes_acked() + u128::from(rec.bytes_in_flight()) + rec.bytes_lost(),
            "step {step}: conservation"
        );
        assert!(rec.cwnd() >= MIN_CWND, "step {step}: cwnd {} below the minimum", rec.cwnd());
        assert!(rec.cwnd() <= MAX_CWND, "step {step}: cwnd {} above the maximum", rec.cwnd());
        let pto = rec.pto_duration();
        assert!(pto > 0, "step {step}: a zero probe timeout");
        assert!(
            pto <= pto_ceiling(&rec, model.node_rtt),
            "step {step}: probe timeout {pto} above its documented ceiling {}",
            pto_ceiling(&rec, model.node_rtt)
        );
        assert!(rec.pacer().next_release(now) >= now, "step {step}: pacer release before now");
        let _ = rec.health(now);
        let _ = rec.can_send();
        // A timer that just ran at its deadline moves on: running it again at the same instant a few times at most
        // must leave it later than that instant or disarmed.
        if let Some(t) = fired_at {
            let mut again = 0;
            while rec.next_timeout().is_some_and(|d| d <= t) {
                again += 1;
                assert!(again <= 3, "step {step}: the timer stays due at {t} after firing {again} times");
                let mut log = Log::new();
                let s = rec.on_timeout(t, logger(&mut log)).summary;
                let expect = apply(&mut model, &log, None);
                assert_eq!(s, expect, "step {step}: summary of a repeated firing");
            }
        }
    }
}

fn recovery_case(start: ephyra::BoxGen<u64>) -> impl Gen<Value = (u64, u64, Vec<RecOp>)> {
    (
        start,
        // A node round trip up to 100 s: a seed from an earlier connection. Larger values push the probe deadline to
        // the end of the clock, which the second property covers on its own.
        gens::frequency(vec![
            (3, gens::constant(0u64).boxed()),
            (1, gens::int(0u64..=2 * SECOND).boxed()),
            (1, gens::edges(0u64..=100 * SECOND).boxed()),
        ]),
        gens::vec(ephyra::any::<RecOp>()).len(1..=120),
    )
}

/// The engine against the model on a clock that starts anywhere a monotonic clock plausibly reads (0 to 2^62 ns).
#[ephyra::test(gen = recovery_case(gens::frequency(vec![(2, gens::constant(0u64).boxed()), (2, gens::constant(1_000_000_000_000u64).boxed()), (1, gens::int(0u64..=(1u64 << 62)).boxed())]).boxed()), tests = 3000)]
fn recovery_matches_the_model(case: (u64, u64, Vec<RecOp>)) {
    let (start, node_rtt, ops) = case;
    run_recovery(start, node_rtt, &ops);
}

/// The same near the end of the clock: deadlines there saturate, which `deadline_after` says must not make a timer
/// fire on every call.
#[ephyra::test(gen = recovery_case(gens::int((u64::MAX - (1u64 << 40))..=u64::MAX).boxed()), tests = 1000)]
fn recovery_matches_the_model_near_the_end_of_the_clock(case: (u64, u64, Vec<RecOp>)) {
    let (start, node_rtt, ops) = case;
    run_recovery(start, node_rtt, &ops);
}

// ---- received packets ----------------------------------------------------------------------------------------

#[derive(Clone, Debug, Arbitrary)]
enum RxOp {
    /// A packet `ahead` past the largest received (0 = the next one).
    Ahead {
        #[ephyra(gen = gens::frequency(vec![(6, gens::constant(0u64).boxed()), (3, gens::int(0u64..=6).boxed()), (1, gens::int(0u64..=40_000).boxed())]))]
        ahead: u64,
        #[ephyra(gen = gens::bool_with(0.85))]
        eliciting: bool,
        #[ephyra(gen = gens::frequency(vec![(1, gens::constant(0u32).boxed()), (1, gens::int(0u32..=1400).boxed())]))]
        bytes: u32,
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    /// A packet `back` below the largest received: a reordered one or a duplicate.
    Behind {
        #[ephyra(gen = gens::frequency(vec![(4, gens::int(0u64..=8).boxed()), (2, gens::int(0u64..=300).boxed()), (1, gens::int(0u64..=1u64 << 20).boxed())]))]
        back: u64,
        #[ephyra(gen = gens::bool_with(0.85))]
        eliciting: bool,
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    AckSent {
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    /// The peer acknowledges some of our acknowledgement packets: (distance below our newest, length) ranges.
    PeerAck {
        #[ephyra(gen = gens::vec((gens::int(0u64..=4), gens::int(0u64..=6))).len(0..=3))]
        ranges: Vec<(u64, u64)>,
        #[ephyra(gen = clock_gap())]
        gap: u64,
    },
    MinRtt(#[ephyra(gen = gens::option(gens::frequency(vec![(2, gens::int(0u64..=400 * MS).boxed()), (1, gens::edges(0u64..=u64::MAX).boxed())])))] Option<u64>),
    Every(#[ephyra(gen = gens::option(gens::int(0u32..=6)))] Option<u32>),
}

fn run_rx<const R: usize>(base: u64, ops: &[RxOp]) {
    let mut rx = ReceivedPackets::<R>::new();
    let mut seen = BTreeSet::new();
    let mut now = 1_000 * SECOND;
    let mut our_pn = 0u64;
    let mut min_rtt = None;
    for (step, op) in ops.iter().enumerate() {
        match *op {
            RxOp::Ahead {
                ahead,
                eliciting,
                bytes,
                gap,
            } => {
                now = now.saturating_add(gap);
                let pn = rx.largest().map_or(base, |l| l + 1).saturating_add(ahead);
                if pn > (1u64 << 62) - 1 {
                    continue;
                }
                receive(&mut rx, &mut seen, step, pn, now, eliciting, bytes, min_rtt);
            },
            RxOp::Behind { back, eliciting, gap } => {
                now = now.saturating_add(gap);
                let Some(l) = rx.largest() else { continue };
                receive(&mut rx, &mut seen, step, l.saturating_sub(back), now, eliciting, 0, min_rtt);
            },
            RxOp::AckSent { gap } => {
                now = now.saturating_add(gap);
                let ranges: Vec<_> = rx.ack_ranges(now).collect();
                if ranges.is_empty() {
                    continue;
                }
                rx.on_ack_sent(our_pn, now);
                our_pn += 1;
                assert!(!rx.ack_pending(), "step {step}: an acknowledgement is still pending after one went out");
            },
            RxOp::PeerAck { ref ranges, gap } => {
                now = now.saturating_add(gap);
                let mut out = Vec::new();
                let mut cursor = our_pn.checked_sub(1);
                for &(below, len) in ranges {
                    let Some(c) = cursor else { break };
                    let Some(end) = c.checked_sub(below) else { break };
                    let start = end.saturating_sub(len);
                    out.push(start..=end);
                    cursor = start.checked_sub(2);
                }
                rx.on_peer_ack(now, &out);
            },
            RxOp::MinRtt(m) => {
                min_rtt = m;
                rx.set_min_rtt(m);
            },
            RxOp::Every(e) => rx.set_every(e),
        }
        assert!(rx.range_count() <= R, "step {step}: {} ranges tracked in room for {R}", rx.range_count());
        assert_eq!(rx.largest(), seen.last().copied(), "step {step}: largest received");
        let ranges: Vec<RangeInclusive<u64>> = rx.ack_ranges(now).collect();
        assert!(ranges.len() <= MAX_ACK_RANGES, "step {step}: {} ranges reported", ranges.len());
        for w in ranges.windows(2) {
            assert!(
                w[1].end().saturating_add(1) < *w[0].start(),
                "step {step}: reported ranges not descending and apart: {ranges:?}"
            );
        }
        for r in &ranges {
            assert!(r.start() <= r.end(), "step {step}: an empty range {r:?}");
            // Small ranges only: a range is at most as long as what was received.
            let n = r.end() - r.start() + 1;
            assert!(n <= seen.len() as u64, "step {step}: range {r:?} longer than everything received");
            assert!(
                seen.range(r.clone()).count() as u64 == n,
                "step {step}: range {r:?} acknowledges a packet never received"
            );
        }
        for &pn in seen.iter().rev().take(64) {
            assert!(rx.contains(pn), "step {step}: received packet {pn} not contained");
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn receive<const R: usize>(
    rx: &mut ReceivedPackets<R>,
    seen: &mut BTreeSet<u64>,
    step: usize,
    pn: u64,
    now: u64,
    eliciting: bool,
    bytes: u32,
    min_rtt: Option<u64>,
) {
    let expected = rx.largest().map_or(0, |l| l + 1);
    let above = rx.largest().is_none_or(|l| pn > l);
    let out = rx.on_packet_received(RxPacket {
        pn,
        now,
        ack_eliciting: eliciting,
        stream_bytes: bytes,
    });
    assert!(out.is_ok(), "step {step}: packet {pn} refused: {out:?}");
    let out = out.unwrap();
    let fresh = !seen.contains(&pn);
    if out == RxOutcome::New {
        assert!(fresh, "step {step}: packet {pn} reported new a second time");
        seen.insert(pn);
        if eliciting {
            let due = rx.ack_deadline();
            assert!(due.is_some(), "step {step}: no acknowledgement scheduled for eliciting {pn}");
            if pn != expected {
                assert!(rx.ack_due(now), "step {step}: packet {pn} out of order ({expected} expected) not acknowledged at once");
            }
            assert!(
                due.unwrap() <= now.saturating_add(max_ack_delay(min_rtt)),
                "step {step}: acknowledgement deadline beyond the delay"
            );
        }
    }
    if above {
        assert_eq!(out, RxOutcome::New, "step {step}: a packet {pn} above every one received was dropped");
    }
}

fn rx_case() -> impl Gen<Value = (u64, Vec<RxOp>)> {
    (
        gens::frequency(vec![
            (3, gens::constant(0u64).boxed()),
            (1, gens::int(0u64..=(1u64 << 62) - 1).boxed()),
            (1, gens::int(((1u64 << 62) - 5000)..=(1u64 << 62) - 1).boxed()),
        ]),
        gens::vec(ephyra::any::<RxOp>()).len(1..=300),
    )
}

#[ephyra::test(gen = rx_case(), tests = 2000)]
fn received_packets_match_the_model_with_4_ranges(case: (u64, Vec<RxOp>)) {
    let (base, ops) = case;
    run_rx::<4>(base, &ops);
}

#[ephyra::test(gen = rx_case(), tests = 2000)]
fn received_packets_match_the_model_with_128_ranges(case: (u64, Vec<RxOp>)) {
    let (base, ops) = case;
    run_rx::<128>(base, &ops);
}
