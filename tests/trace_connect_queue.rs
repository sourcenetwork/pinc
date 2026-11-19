//! Trace generation for the packets a carrier holds while it is not open (`pinc_connect::client::queue::HeldQueue`):
//! seeded runs of the real queue, recorded as ndjson (`connect_queue.ndjson`) for the TLA+ trace check
//! (`TraceConnectHeldQueue.tla`).
//!
//! A run starts with a fresh queue (`new`) and makes `push`, `pop` and `retain` calls. Every pushed packet carries the
//! next serial `d` of its run: its destination holds `d` in its first four bytes and its bytes are a pattern of `d`, so
//! that a packet that lost or kept its bytes wrongly through a compaction or a wrap is seen. After every call the event
//! shows the whole queue as `[serial, length]` pairs. The runs fill the queue by count and by bytes, push a large
//! packet after many small ones, push packets over the limit, retain with edge answers and with answers that look at
//! the neighbours, retain after the bytes wrapped, and then 40 random runs.
//!
//! The test checks by itself: the bounds after every call, the order of the serials, that a push drops exactly the
//! oldest packets and leaves the new one last, that a refused push changes nothing, that a pop gives the oldest packet
//! with its bytes, and that a retain keeps exactly the answered positions, in order.
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
    unreachable_pub,
    clippy::assert_is_empty,
    clippy::manual_is_multiple_of,
    clippy::needless_for_each,
    clippy::replace_box,
    clippy::single_match_else
)]

use std::fmt::Write as _;

use pinc_connect::carrier::frame::MAX_PACKET_LEN;
use pinc_connect::client::queue::{HeldQueue, QUEUE_BYTES, QUEUED};
use pinc_crypto::{IdentityAlg, NodeId};
use pinc_tests::{SplitMix64, soaking};

fn dst(d: u32) -> NodeId {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&d.to_le_bytes());
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes,
    }
}

fn serial_of(n: &NodeId) -> u32 {
    assert!(n.bytes[4..].iter().all(|b| *b == 0), "a destination changed");
    u32::from_le_bytes([n.bytes[0], n.bytes[1], n.bytes[2], n.bytes[3]])
}

fn pkt(d: u32, len: usize) -> Vec<u8> {
    (0..len).map(|j| (d as u8) ^ (j as u8)).collect()
}

fn vstr(v: &[(u32, usize)]) -> String {
    let items: Vec<String> = v.iter().map(|(d, l)| format!("[{d},{l}]")).collect();
    format!("[{}]", items.join(","))
}

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    drop2: u32,
    refused: u32,
    keep_none: u32,
    keep_all: u32,
    pop_none: u32,
}

struct T {
    out: String,
    q: Box<HeldQueue>,
    d: u32,
    seen: Seen,
}

impl T {
    /// The queue as `[serial, length]` pairs, with the bounds and the order checked.
    fn check(&self) -> Vec<(u32, usize)> {
        let mut v = Vec::new();
        let mut i = 0;
        while let Some(h) = self.q.get(i) {
            let d = serial_of(&h.dst);
            assert_eq!(h.packet, &pkt(d, h.packet.len())[..], "the bytes of packet {d} changed");
            v.push((d, h.packet.len()));
            i += 1;
        }
        assert!(self.q.get(self.q.len()).is_none());
        assert_eq!(v.len(), self.q.len());
        assert_eq!(self.q.is_empty(), v.is_empty());
        assert!(v.len() <= QUEUED, "more than QUEUED packets held");
        assert!(
            v.iter().map(|p| p.1).sum::<usize>() <= QUEUE_BYTES,
            "more than QUEUE_BYTES held"
        );
        assert!(v.windows(2).all(|w| w[0].0 < w[1].0), "the serials are not increasing");
        v
    }

    fn new_run(&mut self) {
        self.q = Box::new(HeldQueue::new());
        self.d = 0;
        assert!(self.check().is_empty());
        self.out.push_str("{\"t\":\"hq\",\"op\":\"new\",\"view\":[]}\n");
    }

    fn push(&mut self, len: usize) {
        self.d += 1;
        let d = self.d;
        let before = self.check();
        let dropped = self.q.push(&dst(d), &pkt(d, len));
        let after = self.check();
        if len > MAX_PACKET_LEN {
            assert_eq!(dropped, 1, "a refused packet counts as one drop");
            assert_eq!(after, before, "a refused packet changed the queue");
            self.seen.refused += 1;
        } else {
            assert!(dropped <= before.len());
            let mut want = before[dropped..].to_vec();
            want.push((d, len));
            assert_eq!(after, want, "a push did not drop the oldest and append");
            self.seen.drop2 += u32::from(dropped >= 2);
        }
        let _ = writeln!(
            self.out,
            r#"{{"t":"hq","op":"push","d":{d},"len":{len},"dropped":{dropped},"view":{}}}"#,
            vstr(&after)
        );
    }

    fn pop(&mut self) {
        let before = self.check();
        let mut out = [0u8; MAX_PACKET_LEN];
        let r = self.q.pop(&mut out);
        let after = self.check();
        let (some, d, len) = match r {
            Some((n, len)) => {
                let d = serial_of(&n);
                assert_eq!(before.first(), Some(&(d, len)), "pop did not give the oldest");
                assert_eq!(out[..len], pkt(d, len)[..]);
                assert_eq!(after, before[1..]);
                (true, d, len)
            }
            None => {
                assert!(before.is_empty() && after.is_empty());
                self.seen.pop_none += 1;
                (false, 0, 0)
            }
        };
        let _ = writeln!(
            self.out,
            r#"{{"t":"hq","op":"pop","some":{some},"d":{d},"len":{len},"view":{}}}"#,
            vstr(&after)
        );
    }

    /// A retain whose answer for position `i` is `f(queue, i)`.
    fn retain(&mut self, mut f: impl FnMut(&HeldQueue, usize) -> bool) {
        let before = self.check();
        let mut keep: Vec<bool> = Vec::new();
        self.q.retain(|q, i, h| {
            assert_eq!(i, keep.len(), "retain did not visit the positions in order");
            let d = serial_of(&h.dst);
            assert_eq!(before[i], (d, h.packet.len()));
            assert_eq!(h.packet, &pkt(d, h.packet.len())[..]);
            let k = f(q, i);
            keep.push(k);
            k
        });
        assert_eq!(keep.len(), before.len(), "retain did not visit every packet once");
        let after = self.check();
        let want: Vec<(u32, usize)> = before.iter().zip(&keep).filter(|p| *p.1).map(|p| *p.0).collect();
        assert_eq!(after, want, "retain did not keep exactly the answered positions");
        if !before.is_empty() {
            self.seen.keep_none += u32::from(keep.iter().all(|k| !*k));
            self.seen.keep_all += u32::from(keep.iter().all(|k| *k));
        }
        let ks: Vec<&str> = keep.iter().map(|k| if *k { "true" } else { "false" }).collect();
        let _ = writeln!(
            self.out,
            r#"{{"t":"hq","op":"retain","keep":[{}],"view":{}}}"#,
            ks.join(","),
            vstr(&after)
        );
    }
}

const MIXED: [usize; 10] = [5, 0, 100, 1452, 7, 7, 300, 1, 64, 9];

/// Run 2: the count fill, ending with a queue whose bytes have wrapped.
fn count_fill(t: &mut T) {
    t.new_run();
    for _ in 0..520 {
        t.push(1);
    }
    for _ in 0..3 {
        t.pop();
    }
    for _ in 0..5 {
        t.push(1);
    }
}

#[test]
fn held_queue_runs_match_the_model() {
    let mut rng = SplitMix64::traced(0x4E1D_0001);
    let mut t = T {
        out: String::new(),
        q: Box::new(HeldQueue::new()),
        d: 0,
        seen: Seen::default(),
    };
    // 1. lengths
    t.new_run();
    for len in [0, 1, 2, 1451, 1452, 1453, 4000] {
        t.push(len);
    }
    while !t.q.is_empty() {
        t.pop();
    }
    t.pop();
    // 2. count fill
    count_fill(&mut t);
    // 3. byte fill
    t.new_run();
    for _ in 0..40 {
        t.push(1452);
    }
    t.push(1300);
    // 4. many small, then one large
    t.new_run();
    for _ in 0..512 {
        t.push(96);
    }
    t.push(1452);
    t.push(0);
    // 5. retain edges on ten packets of mixed lengths
    t.new_run();
    let refill = |t: &mut T| {
        while !t.q.is_empty() {
            t.pop();
        }
        MIXED.iter().for_each(|l| t.push(*l));
    };
    refill(&mut t);
    t.retain(|_, _| false);
    refill(&mut t);
    t.retain(|_, _| true);
    t.retain(|_, i| i == 0);
    refill(&mut t);
    t.retain(|q, i| i + 1 == q.len());
    refill(&mut t);
    t.retain(|_, i| i % 2 == 0);
    for l in [11, 22, 33] {
        t.push(l);
    }
    t.pop();
    t.pop();
    // 6. retain that looks at the neighbours
    t.new_run();
    for l in [3, 3, 3, 5, 5, 1, 1, 1, 1, 2, 2, 9, 9, 9, 4, 4, 0, 0, 6, 6] {
        t.push(l);
    }
    t.retain(|q, i| {
        q.get(i + 1)
            .is_none_or(|n| n.packet.len() != q.get(i).map_or(usize::MAX, |h| h.packet.len()))
    });
    // 7. a retain on a queue whose bytes wrapped past the start of the store
    count_fill(&mut t);
    t.retain(|_, i| i % 2 == 1);
    // 8. random runs
    for _ in 0..40 {
        t.new_run();
        for _ in 0..300 {
            match rng.next_u64() % 100 {
                0..=59 => {
                    let len = match rng.next_u64() % 100 {
                        0..=19 => (rng.next_u64() % 9) as usize,
                        20..=69 => 9 + (rng.next_u64() % 192) as usize,
                        70..=89 => 201 + (rng.next_u64() % 1252) as usize,
                        90..=94 => 1452,
                        _ => 1453 + (rng.next_u64() % 148) as usize,
                    };
                    t.push(len);
                }
                60..=84 => t.pop(),
                _ => t.retain(|_, _| rng.next_u64() % 2 == 0),
            }
        }
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("connect_queue.ndjson"), &t.out).unwrap();
    }
    if !soaking() {
        let s = &t.seen;
        assert!(s.drop2 > 0, "no push dropped two or more at once");
        assert!(s.refused > 0, "no push was refused");
        assert!(
            s.keep_none > 0 && s.keep_all > 0,
            "no retain kept none, or none kept all"
        );
        assert!(s.pop_none > 0, "no pop came back empty");
    }
}
