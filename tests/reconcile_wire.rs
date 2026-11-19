//! The reconcile wire format is canonical: a bound has one encoding (the shared prefix length is the longest one the
//! encoder writes, capped at 255) and a reply bitmap has zero padding bits. Both refusals carry their reason.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names
)]

#[path = "reconcile_common.rs"]
mod common;

use common::{Dir, Err, fixed_set, index, run_with};
use pinc_reconcile::wire::{frame_body, put_bound, read_bound, read_parts, tag};
use pinc_reconcile::{Error, Initiator, Limits, Reason, Responder};
use pinc_tests::SplitMix64;
use pinc_wire::Reader;

fn read(last: &[u8], bytes: &[u8]) -> Result<Vec<u8>, Reason> {
    let mut l = last.to_vec();
    let mut r = Reader::new(bytes);
    read_bound(&mut l, &mut r, 4096).map(|()| l)
}

#[test]
fn a_bound_with_a_shorter_shared_prefix_than_the_encoder_writes_is_refused() {
    // last = 1 2 3, bound = 1 2 4: the encoder writes c = 2 and the suffix 4.
    let (mut last, mut enc) = (vec![1u8, 2, 3], Vec::new());
    put_bound(&mut enc, &mut last, &[1, 2, 4]).unwrap();
    assert_eq!(enc, [2, 1, 4]);
    assert_eq!(read(&[1, 2, 3], &enc), Ok(vec![1, 2, 4]));
    // The same bound with c = 1 and the suffix 2 4 would read back as the same bytes, so it must be refused.
    assert_eq!(read(&[1, 2, 3], &[1, 2, 2, 4]), Err(Reason::Bound));
    // c = 0, the whole bound as the suffix.
    assert_eq!(read(&[1, 2, 3], &[0, 3, 1, 2, 4]), Err(Reason::Bound));
    // A shorter prefix is fine when the next bytes differ (that is the longest prefix).
    assert_eq!(read(&[1, 2, 3], &[1, 2, 9, 4]), Ok(vec![1, 9, 4]));
}

#[test]
fn the_cap_of_the_shared_prefix_is_the_longest_prefix_when_it_is_255() {
    let last = vec![7u8; 300];
    let mut enc = Vec::new();
    let mut l = last.clone();
    put_bound(&mut enc, &mut l, &last).unwrap();
    assert_eq!(enc[0], 255, "the prefix length is capped at 255");
    assert_eq!(read(&last, &enc), Ok(last.clone()));
    // 254 with the suffix of 46 equal bytes is another encoding of the same bound.
    let mut other = vec![254, 46];
    other.extend(std::iter::repeat_n(7u8, 46));
    assert_eq!(read(&last, &other), Err(Reason::Bound));
}

#[test]
fn a_reply_bitmap_with_a_padding_bit_set_is_refused() {
    let mut rng = SplitMix64::new(77);
    // The initiator is small enough to send ids at once, the responder too large for one reply: ids leaves follow.
    let a = fixed_set(&mut rng, 30, 8);
    let mut b = a.clone();
    b.extend(fixed_set(&mut rng, 10, 8));
    let b = common::sorted(b);
    let (ia, ib) = (index(&a), index(&b));
    let mut tampered = 0;
    let res: Result<_, Err> = run_with(
        &mut Initiator::new(Limits::default()),
        &mut Responder::new(Limits::default()),
        &ia,
        &ib,
        |d, m| {
            if d != Dir::ToInitiator {
                return;
            }
            let body = frame_body(m).unwrap();
            let mut r = Reader::new(body);
            let (np, _) = read_parts(&mut r).unwrap();
            if np == 0 {
                return;
            }
            let t = r.read_u8().unwrap();
            if t & !tag::INF != tag::REPLY {
                return;
            }
            let mut last = Vec::new();
            read_bound(&mut last, &mut r, 4096).unwrap();
            if t & tag::INF == 0 {
                read_bound(&mut last, &mut r, 4096).unwrap();
            }
            let c = r.read_varint().unwrap() as usize;
            if c.is_multiple_of(8) || tampered > 0 {
                return;
            }
            let at = 3 + r.position() + c.div_ceil(8) - 1;
            m[at] |= 0x80;
            tampered += 1;
        },
    );
    assert_eq!(tampered, 1, "a reply with a partial bitmap byte was found");
    assert_eq!(res.err(), Some(Error::Malformed(Reason::Count)));
}

/// A message whose first part was merged into the report and whose second item is cut short is refused; the session
/// is then dead, so a caller that ignores the error and goes on never gets a report with the half-merged items.
#[test]
fn a_failed_message_leaves_no_session_that_can_report() {
    let a = vec![b"a".to_vec(), b"b".to_vec()];
    let ia = index(&a);
    let mut init = Initiator::new(Limits::default());
    let mut tx = Vec::new();
    init.start(&ia, b"set", &mut tx).unwrap();
    // body: count 1, a cold part with an infinite upper bound, two items, the second longer than what is left
    let body = [2u8, tag::COLD | tag::INF, 0, 0, 2, 1, b'z', 5, b'x'];
    let mut msg = vec![0, 0, body.len() as u8];
    msg.extend_from_slice(&body);
    let mut out = Vec::new();
    assert_eq!(
        init.handle(&ia, &msg, &mut out).err(),
        Some(Error::Malformed(Reason::Truncated))
    );
    // the empty message that would end an exchange
    let end = [0, 0, 1, 0];
    assert_eq!(
        init.handle(&ia, &end, &mut out).err(),
        Some(Error::Malformed(Reason::State))
    );
    assert!(init.report().is_none(), "no report after a failed message");
}

#[test]
fn a_failed_responder_message_ends_its_session() {
    let b: Vec<Vec<u8>> = (0..100u8).map(|i| vec![i]).collect();
    let ib = index(&b);
    let a: Vec<Vec<u8>> = (0..90u8).map(|i| vec![i]).collect();
    let ia = index(&a);
    let (mut init, mut resp) = (Initiator::new(Limits::default()), Responder::new(Limits::default()));
    let (mut tx, mut rx) = (Vec::new(), Vec::new());
    init.start(&ia, b"set", &mut tx).unwrap();
    resp.handle(&ib, &tx, &mut rx).unwrap();
    // a second message with a part count that the bytes do not hold
    let msg = [0, 0, 2, 8, 1];
    assert!(resp.handle(&ib, &msg, &mut rx).is_err());
    assert_eq!(
        resp.handle(&ib, &[0, 0, 1, 0], &mut rx).err(),
        Some(Error::Malformed(Reason::State))
    );
    // reset starts a new session
    resp.reset();
    init.start(&ia, b"set", &mut tx).unwrap();
    resp.handle(&ib, &tx, &mut rx).unwrap();
}

/// Items that share a long prefix make the separators of the root split long, so a small message limit narrows the
/// root's fan. The narrowing rolls the message back to its start, which must leave the previous bound empty even
/// when the initiator is reused after an earlier session.
#[test]
fn a_reused_initiator_narrows_the_root_split_correctly() {
    const LEN: usize = 300;
    let lim = Limits {
        max_item: LEN,
        ..Limits::default()
    };
    let lim = Limits {
        max_message: lim.min_message(),
        ..lim
    };
    let mut rng = SplitMix64::new(77);
    let dense = |rng: &mut SplitMix64, n: usize| -> Vec<Vec<u8>> {
        let mut v: Vec<Vec<u8>> = (0..n)
            .map(|_| {
                let mut it = vec![7u8; LEN];
                rng.fill(&mut it[LEN - 20..]);
                it
            })
            .collect();
        v.sort_unstable();
        v.dedup();
        v
    };
    let (mut init, mut resp) = (Initiator::new(lim), Responder::new(lim));
    for round in 0..3 {
        let a = dense(&mut rng, 600);
        let mut b = a.clone();
        b.drain(round..round + 5);
        b.extend(dense(&mut rng, 5));
        b.sort_unstable();
        b.dedup();
        let (ia, ib) = (index(&a), index(&b));
        let o = run_with(&mut init, &mut resp, &ia, &ib, |_, _| {}).unwrap();
        common::assert_exact(&o, &a, &b);
    }
}
