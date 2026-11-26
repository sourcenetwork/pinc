//! `pinc-connect` client: the held queue of a carrier, the lookup table and the punch timer, each against a reference
//! model written from its module doc.
//!
//! Where the expected behaviour comes from:
//! - `client::queue`: "A packet for a peer through a carrier that is still dialing waits here, oldest first, and
//!   leaves in order when the carrier opens. The queue holds up to [`QUEUED`] packets and [`QUEUE_BYTES`] bytes ... A
//!   full queue drops its oldest packet", `push`: "Returns how many older packets were dropped to make room (0 or
//!   more); a packet longer than [`MAX_PACKET_LEN`] is refused and counts as one drop", `retain`: "Keep the packets
//!   for which `keep(queue, position, packet)` holds, in order. `keep` sees the whole queue as it was before the call".
//! - `client::lookup`: "If no answer came within [`RETRY_NS`] it is asked again, and the retry is also sent to every
//!   other relay", "A node that never heard a UDP datagram asks over its open home carrier instead ... a new one waits
//!   at least [`CARRIER_WAIT_NS`]; with no carrier open nothing is sent", "An answer too large for a datagram is asked
//!   again over the carrier", "A thin node ... repeats a query only after twice its round trip, at most
//!   [`THIN_WAIT_MAX_NS`]", and the invariants: "the table is bounded and a full table refuses a new query rather than
//!   forgetting an old one; a query is outstanding from the moment it is asked until it is answered or
//!   [`Lookups::clear`]ed". `ask`'s comment: "The first query goes over UDP even from a dark node".
//! - `client::punch`: "A [`Puncher`] decides when a session punches: 1 ms after it is established, then every 60 s,
//!   except that a session whose active path is direct and answers in 10 ms or less stops, a session with no
//!   application data for 20 s only waits another 60 s, and a session inside a quiet window after a resume whose
//!   direct path already carries it waits for the window to end."

use std::collections::{BTreeMap, VecDeque};

use ephyra::prelude::*;
use pinc_connect::carrier::MAX_PACKET_LEN;
use pinc_connect::client::lookup::{Ask, CARRIER_WAIT_NS, Lookups, RETRY_NS, THIN_WAIT_MAX_NS};
use pinc_connect::client::punch::{
    ACTIVE_KEEP, Born, FIRST_DELAY, GOOD_LATENCY, MTU_DEFER, Puncher, Step, UPGRADE_INTERVAL, View,
};
use pinc_connect::client::queue::{HeldQueue, QUEUE_BYTES, QUEUED};
use pinc_crypto::{IdentityAlg, Keypair, NodeId};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000_000_000;
const T0: u64 = 1_700_000_000 * SEC;

/// The node ids 0 to 4, made once: a key per call would make the bursts of the queue property slow.
fn node(i: u8) -> NodeId {
    static IDS: std::sync::OnceLock<Vec<NodeId>> = std::sync::OnceLock::new();
    IDS.get_or_init(|| {
        (1u8..=5).map(|s| Keypair::from_seed(IdentityAlg::Ed25519, &[s; 32]).expect("a seed makes a key").node_id()).collect()
    })[usize::from(i)]
}

// ---------------------------------------------------------------------------------------------------------------
// The held queue

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum QOp {
    /// Push a packet of this length for this peer.
    Push(#[ephyra(gen = gens::int(0u8..=3))] u8, #[ephyra(gen = qlen())] u16),
    /// Push this many packets of this length: what reaches the count limit.
    Burst(#[ephyra(gen = gens::int(1u16..=600))] u16, #[ephyra(gen = gens::pick_from(vec![0u16, 1, 40, 90, 97]))] u16),
    Pop,
    /// Keep the packets whose position's bit is set in the mask (repeating every 64), or by the next packet's peer.
    Retain(#[ephyra(gen = gens::int(0u64..=u64::MAX))] u64, bool),
}

fn qlen() -> ephyra::BoxGen<u16> {
    let max = u16::try_from(MAX_PACKET_LEN).unwrap_or(1452);
    gens::frequency(vec![
        (5, gens::int(0u16..=200).boxed()),
        (3, gens::int(0u16..=max).boxed()),
        (2, gens::pick_from(vec![0u16, 1, max - 1, max, max + 1, u16::MAX]).boxed()),
    ])
    .boxed()
}

fn packet(seq: u32, len: u16) -> Vec<u8> {
    let mut p: Vec<u8> = seq.to_le_bytes().iter().copied().cycle().take(usize::from(len)).collect();
    if let Some(b) = p.last_mut() {
        *b ^= 0xa5;
    }
    p
}

/// The held queue against a `VecDeque`: the same packets, in the same order, the same drops, within both limits.
#[ephyra::test(gen = gens::vec(ephyra::any::<QOp>()).len(1..=60), tests = 400)]
fn the_held_queue_keeps_the_newest_packets_in_order_within_its_limits(ops: Vec<QOp>) {
    let mut q = Box::new(HeldQueue::new());
    let mut m: VecDeque<(u8, Vec<u8>)> = VecDeque::new();
    let mut seq = 0u32;
    let mut out = Box::new([0u8; MAX_PACKET_LEN]);
    let mut push = |q: &mut HeldQueue, m: &mut VecDeque<(u8, Vec<u8>)>, dst: u8, len: u16| {
        seq += 1;
        let p = packet(seq, len);
        let mut want = 0;
        if p.len() > MAX_PACKET_LEN {
            want = 1;
        } else {
            while !m.is_empty() && (m.len() >= QUEUED || m.iter().map(|e| e.1.len()).sum::<usize>() + p.len() > QUEUE_BYTES) {
                m.pop_front();
                want += 1;
            }
            m.push_back((dst, p.clone()));
        }
        let got = q.push(&node(dst), &p);
        assert_eq!(got, want, "the drops of a push of {} bytes", p.len());
    };
    for (step, op) in ops.iter().enumerate() {
        match op {
            QOp::Push(d, len) => push(&mut q, &mut m, *d, *len),
            QOp::Burst(k, len) => (0..*k).for_each(|i| push(&mut q, &mut m, u8::try_from(i % 4).unwrap_or(0), *len)),
            QOp::Pop => {
                let got = q.pop(&mut out).map(|(d, n)| (d, out[..n].to_vec()));
                let want = m.pop_front().map(|(d, p)| (node(d), p));
                assert_eq!(got, want, "step {step}: the oldest packet");
            },
            QOp::Retain(mask, by_next) => {
                let snapshot: Vec<NodeId> = m.iter().map(|e| node(e.0)).collect();
                let keep = |i: usize| {
                    if *by_next { snapshot.get(i + 1).is_some_and(|n| *n == snapshot[i]) } else { mask >> (i % 64) & 1 == 1 }
                };
                let mut seen = Vec::new();
                q.retain(|whole, i, h| {
                    seen.push(i);
                    assert_eq!(whole.len(), snapshot.len(), "keep sees the whole queue as it was");
                    assert_eq!(whole.get(i + 1).map(|n| n.dst), snapshot.get(i + 1).copied(), "keep sees the next packet");
                    assert_eq!(h.dst, snapshot[i]);
                    keep(i)
                });
                assert_eq!(seen, (0..snapshot.len()).collect::<Vec<_>>(), "keep is asked once per packet, in order");
                let mut i = 0;
                m.retain(|_| {
                    i += 1;
                    keep(i - 1)
                });
            },
        }
        assert_eq!(q.len(), m.len(), "step {step}: the count");
        assert!(q.len() <= QUEUED, "step {step}: the count limit");
        let bytes: usize = (0..q.len()).filter_map(|i| q.get(i)).map(|h| h.packet.len()).sum();
        assert!(bytes <= QUEUE_BYTES, "step {step}: the byte limit");
        for (i, (d, p)) in m.iter().enumerate() {
            let h = q.get(i).expect("every held packet is readable");
            assert_eq!((h.dst, h.packet), (node(*d), p.as_slice()), "step {step}: packet {i}");
        }
        assert!(q.get(m.len()).is_none(), "step {step}: nothing past the end");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The lookup table

const LN: usize = 3;

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum LOp {
    Ask {
        #[ephyra(gen = gens::int(0u8..=4))]
        peer: u8,
        #[ephyra(gen = gens::bool_with(0.7))]
        udp_any: bool,
        carrier_open: bool,
        #[ephyra(gen = gens::option(gens::pick_from(vec![250 * MS, 400 * MS, 3 * SEC, 5 * SEC, 60 * SEC, u64::MAX])))]
        thin: Option<u64>,
    },
    Answered(#[ephyra(gen = gens::int(0u8..=4))] u8),
    TooLarge(#[ephyra(gen = gens::int(0u8..=4))] u8),
    Clear,
    Time(#[ephyra(gen = ldt())] u64),
}

fn ldt() -> ephyra::BoxGen<u64> {
    gens::frequency(vec![
        (4, gens::pick_from(vec![0, 1, 299 * MS, 300 * MS, 300 * MS + 1, 499 * MS, 2 * SEC, 2 * SEC + 1]).boxed()),
        (2, gens::int(0u64..=20 * SEC).boxed()),
    ])
    .boxed()
}

#[derive(Debug, Clone, Copy)]
struct LItem {
    /// When the query may be repeated: a repeat before this is refused.
    next: u64,
    carrier_only: bool,
    again: bool,
}

/// The lookup table against a model of its doc: when a query is sent, how, and when it is repeated.
#[ephyra::test(gen = gens::vec(ephyra::any::<LOp>()).len(1..=50), tests = 600)]
fn the_lookup_table_asks_and_repeats_as_its_doc_says(ops: Vec<LOp>) {
    let mut t: Lookups<LN> = Lookups::new();
    let mut m: BTreeMap<u8, LItem> = BTreeMap::new();
    let mut now = T0;
    for (step, op) in ops.iter().enumerate() {
        match *op {
            LOp::Time(dt) => now += dt,
            LOp::Answered(p) => {
                t.answered(&node(p));
                m.remove(&p);
            },
            LOp::TooLarge(p) => {
                t.too_large(&node(p));
                if let Some(i) = m.get_mut(&p) {
                    i.carrier_only = true;
                    i.again = true;
                }
            },
            LOp::Clear => {
                t.clear();
                m.clear();
            },
            LOp::Ask { peer, udp_any, carrier_open, thin } => {
                let before: Vec<u8> = m.keys().copied().collect();
                let got = t.ask(now, &node(peer), udp_any, carrier_open, thin);
                let prev = m.get(&peer).copied();
                let want = match prev {
                    None if m.len() >= LN => Ask::Skip,
                    Some(i) if !i.again && now < i.next => Ask::Skip,
                    _ => {
                        let repeat = prev.is_some();
                        let by_carrier = !udp_any || prev.is_some_and(|i| i.carrier_only);
                        let wait = RETRY_NS.max(thin.map_or(0, |r| THIN_WAIT_MAX_NS.min(r.saturating_mul(2))));
                        let (ask, next) = if by_carrier && (carrier_open || repeat) {
                            let a = if carrier_open { Ask::Carrier } else { Ask::Later };
                            (a, now + CARRIER_WAIT_NS.max(wait).max(CARRIER_WAIT_NS - RETRY_NS + wait))
                        } else {
                            (Ask::Udp { others: repeat && !by_carrier }, now + wait)
                        };
                        let carrier_only = prev.is_some_and(|i| i.carrier_only);
                        m.insert(peer, LItem { next, carrier_only, again: false });
                        ask
                    },
                };
                assert_eq!(got, want, "step {step}: how the query for {peer} is sent");
                for p in &before {
                    assert!(t.contains(&node(*p)), "step {step}: the query for {p} is still outstanding");
                }
            },
        }
        assert_eq!(t.len(), m.len(), "step {step}: the outstanding queries");
        assert!(t.len() <= LN, "step {step}: the table is bounded");
        for p in 0u8..=4 {
            assert_eq!(t.contains(&node(p)), m.contains_key(&p), "step {step}: whether {p} is outstanding");
        }
        let mut due: Vec<NodeId> = t.due(now).collect();
        due.sort_by_key(|n| n.bytes);
        let mut want: Vec<NodeId> = m.iter().filter(|(_, i)| now > i.next).map(|(p, _)| node(*p)).collect();
        want.sort_by_key(|n| n.bytes);
        assert_eq!(due, want, "step {step}: the queries due");
        assert_eq!(t.next_deadline(), m.values().map(|i| i.next + 1).min(), "step {step}: the first deadline");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The punch timer

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum POp {
    Established,
    Born(#[ephyra(gen = gens::int(0u8..=2))] u8),
    Arm(#[ephyra(gen = gens::pick_from(vec![0u64, 1, 100 * MS, 3 * SEC]))] u64),
    Due {
        #[ephyra(gen = gens::pick_from(vec![0u64, 19 * SEC, 20 * SEC, 600 * SEC]))]
        app_idle: u64,
        direct: bool,
        #[ephyra(gen = gens::pick_from(vec![0u64, 1, 10 * MS, 10 * MS + 1, 200 * MS]))]
        rtt: u64,
        #[ephyra(gen = gens::pick_from(vec![0u64, 1, 50 * MS, 5 * SEC]))]
        quiet_in: u64,
    },
    Time(#[ephyra(gen = gens::pick_from(vec![0u64, 1, MS - 1, MS, 3 * SEC, 60 * SEC, 61 * SEC]))] u64),
}

/// The punch timer against its doc; its deadline only moves forward when it fires, and a fire is never early.
#[ephyra::test(gen = gens::vec(ephyra::any::<POp>()).len(1..=40), tests = 600)]
fn the_punch_timer_fires_as_its_doc_says(ops: Vec<POp>) {
    let mut p = Puncher::off();
    let mut want: Option<u64> = None;
    let mut now = T0;
    for (step, op) in ops.iter().enumerate() {
        match *op {
            POp::Time(dt) => now += dt,
            POp::Established => {
                p.established(now);
                want = Some(now + FIRST_DELAY);
            },
            POp::Born(how) => {
                let (b, w) = match how {
                    0 => (Born::Plain, Some(now + FIRST_DELAY)),
                    1 => (Born::LateHubDirect, Some(now + MTU_DEFER)),
                    _ => (Born::SubDirect, None),
                };
                p = Puncher::born(now, b);
                want = w;
            },
            POp::Arm(dt) => {
                p.arm(now + dt);
                want = Some(now + dt);
            },
            POp::Due { app_idle, direct, rtt, quiet_in } => {
                let quiet_until = if quiet_in == 0 { 0 } else { now + quiet_in };
                let v = View { app_idle, direct, rtt, quiet_until };
                let step_got = p.due(now, &v);
                let step_want = match want {
                    Some(at) if now >= at => {
                        if now < quiet_until && direct {
                            want = Some(quiet_until + 1);
                            Step::Wait
                        } else if app_idle >= ACTIVE_KEEP {
                            want = Some(now + UPGRADE_INTERVAL);
                            Step::Wait
                        } else {
                            let good = direct && rtt != 0 && rtt <= GOOD_LATENCY;
                            want = (!good).then_some(now + UPGRADE_INTERVAL);
                            Step::Punch
                        }
                    },
                    _ => Step::Wait,
                };
                assert_eq!(step_got, step_want, "step {step}: what the due timer does");
                if let Some(at) = want {
                    assert!(at > now, "step {step}: the next deadline is later than now");
                }
            },
        }
        assert_eq!(p.deadline(), want, "step {step}: the deadline");
    }
}
