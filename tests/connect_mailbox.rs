//! The mailbox: bounds, drop-oldest with counters, age, ordering and at-most-once delivery.
#![allow(
    clippy::many_single_char_names,
    clippy::assert_is_empty,
    clippy::decimal_bitwise_operands,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::cast_lossless,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements
)]

mod connect_common;

use std::collections::VecDeque;

use connect_common::{SEC, nid};
use proptest::prelude::*;
use vinc_connect::carrier::MAX_PACKET_LEN;
use vinc_connect::mailbox::{ENTRY_HEAD, Mailbox, Offer, Push};

const B: usize = 1000;
type M = Mailbox<3, B>;

fn pop(m: &mut M, now: u64, n: u8) -> Option<(u8, u8, Vec<u8>, u64)> {
    let mut buf = [0u8; MAX_PACKET_LEN];
    m.pop(now, &nid(n), &mut buf)
        .map(|d| (d.src.bytes[0], d.flag, buf[..d.len].to_vec(), d.seq))
}

#[test]
fn messages_leave_in_order_and_only_once() {
    let mut m = M::new(100 * SEC, 1);
    let to = nid(1);
    for i in 0..5u8 {
        let r = m.push(0, &to, &nid(10 + i), i, &[i; 20]);
        assert_eq!(
            r,
            Push::Stored {
                seq: u64::from(i),
                dropped: 0,
                first: i == 0
            }
        );
    }
    assert_eq!(m.pending(&to), (5, 5 * (ENTRY_HEAD + 20)));
    for i in 0..5u8 {
        assert_eq!(pop(&mut m, 0, 1), Some((10 + i, i, vec![i; 20], u64::from(i))));
    }
    assert_eq!(pop(&mut m, 0, 1), None, "each message is delivered once");
    assert_eq!(m.pending(&to), (0, 0));
    assert_eq!(m.members(), 0, "an empty member frees its slot");
    assert_eq!(m.stats().delivered, 5);
}

#[test]
fn held_messages_can_be_read_in_order_and_put_back_with_their_arrival_time() {
    let mut m = M::new(100 * SEC, 1);
    let to = nid(1);
    // a ring that has wrapped, so the read walks across the end
    for i in 0..9u8 {
        m.push(u64::from(i) * SEC, &to, &nid(10 + i), i, &[i; 150]);
    }
    let (count, _) = m.pending(&to);
    assert!(count > 0 && count < 9, "the quota pushed some out: {count}");
    let mut buf = [0u8; MAX_PACKET_LEN];
    let mut seen = Vec::new();
    for i in 0..count {
        let (d, at) = m.peek(&to, i, &mut buf).unwrap();
        assert_eq!(buf[..d.len], vec![d.flag; 150]);
        seen.push((d.src.bytes[0], d.flag, buf[..d.len].to_vec(), at));
    }
    assert!(m.peek(&to, count, &mut buf).is_none());
    assert!(seen.windows(2).all(|w| w[0].3 < w[1].3), "oldest first");

    // put them back in a mailbox of a restarted relay: same order, and the age counts from the arrival
    let mut r = M::new(100 * SEC, 2);
    for (src, flag, body, at) in &seen {
        let p = r.restore(50 * SEC, *at, &to, &nid(*src), *flag, body);
        assert!(matches!(p, Push::Stored { .. }), "{p:?}");
    }
    assert_eq!(r.pending(&to), m.pending(&to));
    for (src, flag, body, _) in &seen {
        let (s, f, b, _) = pop(&mut r, 50 * SEC, 1).unwrap();
        assert_eq!((s, f, &b), (*src, *flag, body));
    }
    // a restored message expires 100 s after it arrived, not after it was restored
    r.restore(107 * SEC, 6 * SEC, &to, &nid(9), 0, &[1; 10]);
    r.restore(107 * SEC, 8 * SEC, &to, &nid(9), 1, &[2; 10]);
    assert_eq!(
        pop(&mut r, 107 * SEC, 1).map(|p| p.1),
        Some(1),
        "the one that arrived at 6 s has expired at 107 s"
    );
}

#[test]
fn the_byte_quota_includes_headers_and_drops_oldest_first() {
    let mut m = M::new(100 * SEC, 1);
    let to = nid(1);
    let body = 100;
    let per = ENTRY_HEAD + body;
    let fit = B / per;
    assert_eq!(fit, 6);
    for i in 0..fit as u8 {
        m.push(0, &to, &nid(2), i, &[i; 100]);
    }
    assert_eq!(m.pending(&to), (fit, fit * per));
    assert!(m.pending(&to).1 <= B);
    // one more pushes the oldest out
    let r = m.push(0, &to, &nid(2), 99, &[99; 100]);
    assert_eq!(
        r,
        Push::Stored {
            seq: fit as u64,
            dropped: 1,
            first: false
        }
    );
    assert_eq!(m.stats().dropped_oldest, 1);
    assert_eq!(m.stats().dropped_oldest_bytes, per as u64);
    assert_eq!(pop(&mut m, 0, 1).unwrap().1, 1, "message 0 was dropped");
    // a big message pushes out several
    let big = vec![7u8; 600];
    let r = m.push(0, &to, &nid(2), 50, &big);
    let Push::Stored { dropped, .. } = r else { panic!() };
    assert!(dropped >= 3);
    assert!(m.pending(&to).1 <= B);
    // the newest is always kept
    let mut last = None;
    while let Some(x) = pop(&mut m, 0, 1) {
        last = Some(x);
    }
    assert_eq!(last.unwrap().1, 50);
}

#[test]
fn a_message_that_cannot_fit_is_refused_and_counted() {
    let mut m = M::new(100 * SEC, 1);
    let to = nid(1);
    assert_eq!(m.push(0, &to, &nid(2), 0, &[]), Push::TooLarge);
    assert_eq!(m.push(0, &to, &nid(2), 0, &vec![0; B - ENTRY_HEAD + 1]), Push::TooLarge);
    assert_eq!(m.push(0, &to, &nid(2), 0, &vec![0; MAX_PACKET_LEN + 1]), Push::TooLarge);
    assert_eq!(m.stats().refused_oversize, 3);
    assert_eq!(m.stats().stored, 0);
    assert!(
        matches!(
            m.push(0, &to, &nid(2), 0, &vec![0; B - ENTRY_HEAD]),
            Push::Stored { .. }
        ),
        "exactly the quota"
    );
    assert_eq!(m.pending(&to), (1, B));
}

#[test]
fn messages_expire_at_the_maximum_age() {
    let mut m = M::new(100 * SEC, 1);
    let to = nid(1);
    m.push(0, &to, &nid(2), 1, &[1; 10]);
    m.push(50 * SEC, &to, &nid(2), 2, &[2; 10]);
    m.push(99 * SEC, &to, &nid(2), 3, &[3; 10]);
    // at 99.999999999 s nothing has expired; at exactly 100 s the first has
    let mut buf = [0u8; MAX_PACKET_LEN];
    let d = m.pop(100 * SEC - 1, &to, &mut buf).unwrap();
    assert_eq!(d.flag, 1);
    let d = m.pop(150 * SEC, &to, &mut buf).unwrap();
    assert_eq!(d.flag, 3, "the one stored at 50 s expired at 150 s");
    assert_eq!(m.stats().expired, 1);
    assert!(m.pop(150 * SEC, &to, &mut buf).is_none());
    // the sweep expires without a delivery attempt and frees the slot
    m.push(200 * SEC, &to, &nid(2), 4, &[4; 10]);
    assert_eq!(m.members(), 1);
    m.sweep(300 * SEC);
    assert_eq!((m.members(), m.stats().expired), (0, 2));
}

#[test]
fn the_number_of_members_is_bounded() {
    let mut m = M::new(100 * SEC, 1);
    for n in 1..=3u8 {
        assert!(matches!(m.push(0, &nid(n), &nid(9), 0, &[1]), Push::Stored { .. }));
    }
    assert_eq!(m.push(0, &nid(4), &nid(9), 0, &[1]), Push::NoSlot);
    assert_eq!(m.stats().refused_members, 1);
    // an existing member still takes messages, and a freed slot is reusable
    assert!(matches!(m.push(0, &nid(2), &nid(9), 0, &[2]), Push::Stored { .. }));
    while pop(&mut m, 0, 1).is_some() {}
    assert!(matches!(m.push(0, &nid(4), &nid(9), 0, &[1]), Push::Stored { .. }));
    m.clear(&nid(4));
    assert_eq!(m.pending(&nid(4)), (0, 0));
}

#[test]
fn the_ring_wraps_without_corrupting_messages() {
    let mut m = M::new(1000 * SEC, 1);
    let to = nid(1);
    let mut want = VecDeque::new();
    let mut seq = 0u32;
    for round in 0..400u32 {
        let len = 1 + (round as usize * 37) % 211;
        let body: Vec<u8> = (0..len).map(|i| (i as u32 + round) as u8).collect();
        let r = m.push(0, &to, &nid(7), (round % 250) as u8, &body);
        assert!(matches!(r, Push::Stored { .. }));
        want.push_back((round, body));
        let (_, bytes) = m.pending(&to);
        while want.iter().map(|(_, b)| b.len() + ENTRY_HEAD).sum::<usize>() > B {
            want.pop_front();
        }
        assert!(bytes <= B);
        if round % 3 == 0 {
            let got = pop(&mut m, 0, 1).unwrap();
            let (rd, body) = want.pop_front().unwrap();
            assert_eq!((got.1, got.2), ((rd % 250) as u8, body));
            seq += 1;
        }
    }
    assert!(seq > 100);
}

#[derive(Debug, Clone)]
enum Op {
    Push { to: u8, len: usize, at: u64 },
    Pop { to: u8, at: u64 },
}

fn ops() -> impl Strategy<Value = Vec<Op>> {
    proptest::collection::vec(
        prop_oneof![
            (1u8..4, 1usize..400, 0u64..4).prop_map(|(to, len, at)| Op::Push { to, len, at }),
            (1u8..4, 0u64..4).prop_map(|(to, at)| Op::Pop { to, at }),
        ],
        1..200,
    )
}

proptest! {
    #[test]
    fn the_mailbox_matches_a_plain_model(ops in ops()) {
        const AGE: u64 = 30;
        let mut m = M::new(AGE * SEC, 3);
        let mut model: [VecDeque<(u8, Vec<u8>, u64, u64)>; 4] = Default::default();
        let (mut now, mut next_seq) = (0u64, 0u64);
        let (mut dropped, mut expired, mut delivered) = (0u64, 0u64, 0u64);
        let mut tag = 0u8;
        for op in ops {
            match op {
                Op::Push { to, len, at } => {
                    now += at * 5;
                    tag = tag.wrapping_add(1);
                    let body = vec![tag; len];
                    let q = &mut model[usize::from(to)];
                    while q.front().is_some_and(|f| now - f.2 >= AGE) { q.pop_front(); expired += 1; }
                    let size = ENTRY_HEAD + len;
                    let r = m.push(now * SEC, &nid(to), &nid(9), tag, &body);
                    if size > B {
                        prop_assert_eq!(r, Push::TooLarge);
                        continue;
                    }
                    while q.iter().map(|x| ENTRY_HEAD + x.1.len()).sum::<usize>() + size > B { q.pop_front(); dropped += 1; }
                    q.push_back((tag, body, now, next_seq));
                    next_seq += 1;
                    let stored = matches!(r, Push::Stored { .. });
                    prop_assert!(stored);
                }
                Op::Pop { to, at } => {
                    now += at * 5;
                    let q = &mut model[usize::from(to)];
                    while q.front().is_some_and(|f| now - f.2 >= AGE) { q.pop_front(); expired += 1; }
                    let want = q.pop_front();
                    let got = pop(&mut m, now * SEC, to);
                    if want.is_some() { delivered += 1; }
                    prop_assert_eq!(got.map(|g| (g.1, g.2, g.3)), want.map(|w| (w.0, w.1, w.3)));
                }
            }
            for n in 1..4u8 {
                let want: usize = model[usize::from(n)].iter().map(|x| ENTRY_HEAD + x.1.len()).sum();
                prop_assert!(m.pending(&nid(n)).1 <= B);
                prop_assert_eq!(m.pending(&nid(n)).1, want, "bytes held for {}", n);
            }
        }
        let st = m.stats();
        prop_assert_eq!((st.dropped_oldest, st.expired, st.delivered), (dropped, expired, delivered));
    }
}

#[test]
fn a_looked_at_message_stays_held_with_its_seq_until_it_is_removed() {
    let mut m = M::new(100 * SEC, 1);
    let to = nid(1);
    for i in 0..3u8 {
        m.push(0, &to, &nid(10), i, &[i; 20]);
    }
    let before = m.pending(&to);
    let mut buf = [0u8; MAX_PACKET_LEN];
    let a = m.look(0, &to, &mut buf, MAX_PACKET_LEN).unwrap();
    let b = m.look(0, &to, &mut buf, MAX_PACKET_LEN).unwrap();
    assert_eq!((a, &buf[..a.len]), (b, &[0u8; 20][..]), "a look removes nothing");
    assert_eq!(m.pending(&to), before);
    assert_eq!(m.stats().delivered, 0);
    assert!(!m.remove(&to, a.seq + 1), "only the oldest can be removed");
    assert!(m.remove(&to, a.seq));
    assert!(!m.remove(&to, a.seq), "removed once");
    assert_eq!(m.pending(&to), (2, 2 * (ENTRY_HEAD + 20)));
    assert_eq!(m.stats().delivered, 1);
    let c = m.look(0, &to, &mut buf, MAX_PACKET_LEN).unwrap();
    assert_eq!(
        (c.seq, c.flag),
        (a.seq + 1, 1),
        "the order and the seq of what stays are unchanged"
    );
    assert!(
        m.look(0, &to, &mut buf, 19).is_none(),
        "a body over the limit is not returned"
    );
    assert_eq!(m.pending(&to).0, 2);
    // looking past the age expires, and the last removal frees the member
    assert!(m.look(100 * SEC, &to, &mut buf, MAX_PACKET_LEN).is_none());
    assert_eq!((m.pending(&to), m.members(), m.stats().expired), ((0, 0), 0, 2));
    m.push(0, &to, &nid(10), 9, &[9; 5]);
    let d = m.look(0, &to, &mut buf, MAX_PACKET_LEN).unwrap();
    assert!(m.remove(&to, d.seq));
    assert_eq!((m.pending(&to), m.members()), ((0, 0), 0));
}

/// One drain of `m` for `to` against the plain model: the caller declines every second offer when `decline`, and at
/// the `stop`th offer either takes it and stops (`take_on_stop`) or stops without it. Returns what was offered.
fn drain(
    m: &mut M,
    to: &vinc_crypto::NodeId,
    fit: usize,
    stop: usize,
    take_on_stop: bool,
    decline: bool,
) -> Vec<(u64, u8, usize)> {
    let mut offered = Vec::new();
    let mut buf = [0u8; MAX_PACKET_LEN];
    Mailbox::drain(
        m,
        |m| m,
        0,
        to,
        fit,
        &mut buf,
        |_, d, body| {
            assert_eq!(body.len(), d.len);
            assert!(body.iter().all(|b| *b == d.flag), "the body is the message's own");
            let i = offered.len();
            offered.push((d.seq, d.flag, d.len));
            if i == stop {
                return Offer {
                    taken: take_on_stop,
                    go_on: false,
                };
            }
            Offer {
                taken: !(decline && i % 2 == 1),
                go_on: true,
            }
        },
    );
    offered
}

proptest! {
    /// A drain offers what fits, in order, up to where the caller stops; takes what the caller takes; and leaves the
    /// rest in order with exact counts, through a wrap of the ring (the quota pushes the oldest out) and two passes.
    #[test]
    fn draining_offers_what_fits_in_order_and_keeps_the_rest_in_order(
        lens in proptest::collection::vec(1usize..300, 1..14),
        fit in 0usize..300,
        pops in 0usize..3,
        stop in 0usize..16,
        take_on_stop in any::<bool>(),
        decline in any::<bool>(),
    ) {
        let mut m = M::new(100 * SEC, 1);
        let to = nid(1);
        let mut buf = [0u8; MAX_PACKET_LEN];
        for (i, len) in lens.iter().enumerate() {
            m.push(0, &to, &nid(9), i as u8, &vec![i as u8; *len]);
        }
        for _ in 0..pops {
            m.pop(0, &to, &mut buf);
        }
        for round in 0..2 {
            let held: Vec<(u64, u8, usize)> = (0..m.pending(&to).0)
                .map(|i| {
                    let (d, _) = m.peek(&to, i, &mut buf).unwrap();
                    (d.seq, d.flag, d.len)
                })
                .collect();
            let before = m.stats().delivered;
            let offered = drain(&mut m, &to, fit, stop, take_on_stop, decline);
            // the model
            let mut want_offered = Vec::new();
            let mut left = Vec::new();
            let mut taken = 0u64;
            let mut stopped = false;
            for h in &held {
                if stopped || h.2 > fit {
                    left.push(*h);
                    continue;
                }
                let i = want_offered.len();
                want_offered.push(*h);
                if i == stop {
                    stopped = true;
                    if take_on_stop { taken += 1; } else { left.push(*h); }
                } else if decline && i % 2 == 1 {
                    left.push(*h);
                } else {
                    taken += 1;
                }
            }
            prop_assert_eq!(&offered, &want_offered, "offered, round {}", round);
            prop_assert_eq!(m.stats().delivered - before, taken, "delivered");
            prop_assert_eq!(m.pending(&to).0, left.len(), "count");
            prop_assert_eq!(m.pending(&to).1, left.iter().map(|h| ENTRY_HEAD + h.2).sum::<usize>(), "bytes");
            for (i, h) in left.iter().enumerate() {
                let (d, _) = m.peek(&to, i, &mut buf).unwrap();
                prop_assert_eq!((d.seq, d.flag, d.len), *h, "left, in order");
                prop_assert!(buf[..d.len].iter().all(|b| *b == d.flag), "the body survived the move");
            }
            prop_assert_eq!(m.members(), usize::from(!left.is_empty()), "the member is freed when nothing is left");
            // a later push goes last and the ring still reads right
            if round == 0 {
                m.push(0, &to, &nid(9), 200, &[200u8; 20]);
            }
        }
    }
}
