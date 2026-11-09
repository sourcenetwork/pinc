//! Rounds larger than one message: a difference whose round does not fit the message limit is spread over as many
//! messages as it needs, every message stays within the limit, the result is the exact symmetric difference, a reset
//! in the middle retries the session once, and a malformed or truncated chunk is refused with a reason.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::expect_used
)]

#[path = "reconcile_common.rs"]
mod common;

use std::thread;

use common::{Dir, assert_exact, fixed_set, index, mutate, pair, run_with, sorted, var_set};
use vinc_reconcile::wire::{frame_body, read_parts};
use vinc_reconcile::{Error, Initiator, Limits, MemError, MemIndex, Reason, Responder, RunError, Step};
use vinc_tests::SplitMix64;
use vinc_wire::Reader;

const ITEM: usize = 40;
/// What a message may add to the parts the limit bounds: the count and, in the first message, the set reference.
const FRAMING: usize = 16;

fn limited(max_message: usize) -> Limits {
    Limits {
        max_message,
        ..Limits::default()
    }
}

/// Run a session and return the outcome, the largest body, and how many messages said they hold more.
fn measured(a: &[Vec<u8>], b: &[Vec<u8>], limits: Limits) -> (common::Outcome, usize, usize) {
    let (ia, ib) = (index(a), index(b));
    let (mut largest, mut more, mut seen) = (0, 0, 0);
    let o = run_with(
        &mut Initiator::new(limits),
        &mut Responder::new(limits),
        &ia,
        &ib,
        |_, m| {
            largest = largest.max(m.len() - 3);
            if seen > 0 {
                let mut r = Reader::new(frame_body(m).unwrap());
                more += usize::from(read_parts(&mut r).unwrap().1);
            }
            seen += 1;
        },
    )
    .unwrap();
    (o, largest, more)
}

fn report(label: &str, o: &common::Outcome, largest: usize, more: usize) {
    eprintln!(
        "{label}: {} bytes, {} messages ({more} holding more), largest body {largest}, {} + {} items",
        o.bytes(),
        o.messages,
        o.here.len(),
        o.there.len()
    );
}

#[test]
fn a_large_difference_is_spread_over_many_messages_within_a_small_limit() {
    let mut rng = SplitMix64::new(31);
    let a = fixed_set(&mut rng, 60_000, ITEM);
    let (b, ..) = mutate(&mut rng, &a, 30_000, ITEM);
    for max_message in [16_384, 65_536] {
        let (o, largest, more) = measured(&a, &b, limited(max_message));
        report(&format!("limit {max_message}"), &o, largest, more);
        assert_exact(&o, &a, &b);
        assert!(largest <= max_message + FRAMING, "largest body {largest}");
        assert!(more > 0, "the round fitted one message");
        // The messages follow the bytes, not the rounds: most of them are nearly full.
        assert!(
            o.messages <= 3 * o.bytes() / max_message + 60,
            "{} messages for {} bytes",
            o.messages,
            o.bytes()
        );
    }
}

#[test]
fn a_large_difference_under_the_default_limit_is_exact() {
    let mut rng = SplitMix64::new(32);
    let a = fixed_set(&mut rng, 200_000, ITEM);
    let (b, ..) = mutate(&mut rng, &a, 100_000, ITEM);
    let (o, largest, more) = measured(&a, &b, Limits::default());
    report("default limit", &o, largest, more);
    assert_exact(&o, &a, &b);
    assert!(o.messages <= 16, "{} messages", o.messages);
}

#[test]
fn a_dense_range_on_one_side_narrows_to_leaves_within_the_limit() {
    // The responder holds 40 000 items in one key range where the initiator has none: a leaf cannot list them.
    let mut rng = SplitMix64::new(33);
    let a = fixed_set(&mut rng, 5000, ITEM);
    let dense: Vec<Vec<u8>> = {
        let mut v = fixed_set(&mut rng, 40_000, ITEM);
        for x in &mut v {
            x[..4].copy_from_slice(&[0x80; 4]);
        }
        v
    };
    let b = sorted(a.iter().cloned().chain(dense).collect());
    for max_message in [16_384, 1 << 20] {
        let (o, largest, more) = measured(&a, &b, limited(max_message));
        report(&format!("dense, limit {max_message}"), &o, largest, more);
        assert_exact(&o, &a, &b);
        assert!(largest <= max_message + FRAMING, "largest body {largest}");
        let (o, largest, _) = measured(&b, &a, limited(max_message));
        assert_exact(&o, &b, &a);
        assert!(largest <= max_message + FRAMING, "largest body {largest}");
    }
}

#[test]
fn long_items_under_a_small_limit_are_exact() {
    let mut rng = SplitMix64::new(34);
    let a = fixed_set(&mut rng, 3000, 2000);
    let (b, ..) = mutate(&mut rng, &a, 1500, 2000);
    let (o, largest, more) = measured(&a, &b, limited(16_384));
    report("2000-byte items", &o, largest, more);
    assert_exact(&o, &a, &b);
    assert!(largest <= 16_384 + FRAMING, "largest body {largest}");
    let a = var_set(&mut rng, 3000, 900);
    let (b, ..) = mutate(&mut rng, &a, 600, 700);
    let (o, largest, _) = measured(&a, &b, limited(8192));
    assert_exact(&o, &a, &b);
    assert!(largest <= 8192 + FRAMING, "largest body {largest}");
}

#[test]
fn the_smallest_valid_limit_reconciles_exactly() {
    let mut rng = SplitMix64::new(35);
    let a = var_set(&mut rng, 800, 30);
    let (b, ..) = mutate(&mut rng, &a, 200, 30);
    let limits = Limits {
        max_item: 32,
        ..Limits::default()
    };
    let limits = Limits {
        max_message: limits.min_message(),
        ..limits
    };
    let (o, largest, more) = measured(&a, &b, limits);
    report("smallest limit", &o, largest, more);
    assert_exact(&o, &a, &b);
    assert!(largest <= limits.max_message + FRAMING, "largest body {largest}");
}

// ---- resets -----------------------------------------------------------------------------------------------------

#[test]
fn a_reset_in_the_middle_of_a_chunked_round_retries_exactly_once() {
    let mut rng = SplitMix64::new(36);
    let a = fixed_set(&mut rng, 20_000, ITEM);
    let (b, ..) = mutate(&mut rng, &a, 6000, ITEM);
    let limits = limited(16_384);
    let (ia, ib) = (index(&a), index(&b));
    let (full, ..) = measured(&a, &b, limits);
    assert!(full.messages > 40, "{} messages", full.messages);
    for reset_at in [2usize, 5, 11, 23] {
        let (mut attempt, mut servers) = (0, Vec::new());
        let mut init = Initiator::new(limits);
        init.run_retry(
            || {
                attempt += 1;
                let (mut c1, mut c2) = pair();
                if attempt == 1 {
                    c1.reset_after = Some(reset_at);
                }
                let set: MemIndex = ib.clone();
                servers.push(thread::spawn(move || {
                    Responder::new(limits).serve(&mut c2, |r| (r == b"set").then_some(&set))
                }));
                Ok(c1)
            },
            &&ia,
            b"set",
            3,
        )
        .unwrap();
        assert_eq!(attempt, 2, "reset at message {reset_at}: exactly one retry");
        let rep = init.report().unwrap();
        let (only_b, only_a) = common::sym_diff(&a, &b);
        assert_eq!(sorted(rep.missing_here().map(<[u8]>::to_vec).collect()), only_b);
        assert_eq!(sorted(rep.missing_there().map(<[u8]>::to_vec).collect()), only_a);
        for s in servers {
            let r: Result<(), RunError<(), MemError>> = s.join().unwrap();
            assert!(matches!(r, Ok(()) | Err(RunError::Reset | RunError::Closed)), "{r:?}");
        }
    }
}

// ---- malformed chunks -------------------------------------------------------------------------------------------

/// The messages of a chunked session that say they hold more, with their direction and the sets' indexes.
fn chunks() -> (Vec<(Dir, Vec<u8>)>, MemIndex, MemIndex) {
    let mut rng = SplitMix64::new(37);
    let a = fixed_set(&mut rng, 1500, ITEM);
    let (b, ..) = mutate(&mut rng, &a, 600, ITEM);
    let limits = limited(2048);
    let (ia, ib) = (index(&a), index(&b));
    let mut log = Vec::new();
    run_with(
        &mut Initiator::new(limits),
        &mut Responder::new(limits),
        &ia,
        &ib,
        |d, m| {
            log.push((d, m.clone()));
        },
    )
    .unwrap();
    let held = log
        .into_iter()
        .skip(1)
        .filter(|(_, m)| read_parts(&mut Reader::new(frame_body(m).unwrap())).unwrap().1)
        .collect::<Vec<_>>();
    assert!(held.len() > 4, "{} chunks", held.len());
    (held, ia, ib)
}

fn reframe(body: &[u8]) -> Vec<u8> {
    let mut msg = vec![(body.len() >> 16) as u8, (body.len() >> 8) as u8, body.len() as u8];
    msg.extend_from_slice(body);
    msg
}

/// A receiver, with the default limits so that every part of a message is read at once, that is ready for `dir`.
fn receiver(dir: Dir, ia: &MemIndex, ib: &MemIndex) -> impl FnMut(&[u8]) -> Result<(), Error<MemError>> {
    let mut out = Vec::new();
    let mut first = Vec::new();
    let mut init = Initiator::new(Limits::default());
    let mut resp = Responder::new(Limits::default());
    init.start(ia, b"set", &mut first).unwrap();
    if dir == Dir::ToResponder {
        resp.handle(ib, &first, &mut out).unwrap();
    }
    let (ia, ib) = (ia.clone(), ib.clone());
    move |m: &[u8]| match dir {
        Dir::ToInitiator => init.handle(&ia, m, &mut out).map(|_| ()),
        Dir::ToResponder => resp.handle(&ib, m, &mut out).map(|_| ()),
    }
}

#[test]
fn every_truncated_chunk_is_refused_with_a_reason() {
    let (held, ia, ib) = chunks();
    for (dir, msg) in held.iter().step_by(held.len() / 4 + 1) {
        let body = frame_body(msg).unwrap();
        for cut in (0..body.len()).step_by(5).chain([body.len() - 1]) {
            let r = receiver(*dir, &ia, &ib)(&reframe(&body[..cut]));
            assert!(
                matches!(r, Err(Error::Malformed(_))),
                "{dir:?}: cut at {cut} of {}: {r:?}",
                body.len()
            );
        }
        // Bytes after the last part.
        let mut long = body.to_vec();
        long.push(0);
        assert_eq!(
            receiver(*dir, &ia, &ib)(&reframe(&long)),
            Err(Error::Malformed(Reason::Frame))
        );
        // A frame whose length disagrees.
        let mut bad = msg.clone();
        bad.pop();
        assert_eq!(receiver(*dir, &ia, &ib)(&bad), Err(Error::Malformed(Reason::Frame)));
    }
}

#[test]
fn an_empty_chunk_that_claims_more_is_refused() {
    let (_, ia, ib) = chunks();
    for dir in [Dir::ToInitiator, Dir::ToResponder] {
        // venc(0 << 1 | 1): no parts, but more to come.
        assert_eq!(
            receiver(dir, &ia, &ib)(&[0, 0, 1, 1]),
            Err(Error::Malformed(Reason::Count)),
            "{dir:?}"
        );
    }
}

#[test]
fn a_chunk_after_the_session_ended_is_refused() {
    let (held, ia, ib) = chunks();
    let mut rng = SplitMix64::new(38);
    let a = fixed_set(&mut rng, 100, ITEM);
    let ix = index(&a);
    let (mut init, mut resp) = (Initiator::new(Limits::default()), Responder::new(Limits::default()));
    common::run_with(&mut init, &mut resp, &ix, &ix, |_, _| {}).unwrap();
    let mut out = Vec::new();
    let r = init.handle(&ia, &held[0].1, &mut out);
    assert_eq!(r, Err(Error::Malformed(Reason::State)));
    let r = resp.handle(&ib, &held[0].1, &mut out);
    assert_eq!(r, Err(Error::Malformed(Reason::State)));
}

#[test]
fn a_chunk_that_never_ends_is_bounded() {
    // A peer that answers every message with a full chunk that says it holds more must hit a limit, not grow memory.
    let (held, ia, _) = chunks();
    let (_, chunk) = held.iter().find(|(d, _)| *d == Dir::ToInitiator).unwrap();
    let limits = Limits {
        max_rounds: 64,
        ..limited(4096)
    };
    let mut init = Initiator::new(limits);
    let mut out = Vec::new();
    init.start(&ia, b"set", &mut out).unwrap();
    let mut last = Ok(Step::Send);
    for _ in 0..200 {
        last = init.handle(&ia, chunk, &mut out);
        if last.is_err() {
            break;
        }
    }
    assert!(
        matches!(
            last,
            Err(Error::TooManyRounds | Error::Malformed(_) | Error::ReportTooLarge)
        ),
        "{last:?}"
    );
}
