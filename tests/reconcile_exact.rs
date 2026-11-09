//! Exactness and failure handling: forced id collisions are detected by the final check and resolved by items, a
//! lying peer fails loudly, a reset stream retries the whole session, and malformed input is refused.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::expect_used
)]

#[path = "reconcile_common.rs"]
mod common;

use std::thread;

use common::{Dir, End, assert_exact, fixed_set, index, mutate, pair, run_with};
use vinc_reconcile::wire::{frame_body, tag};
use vinc_reconcile::{
    Error, Fingerprint, Initiator, ItemIndex, Limits, MemError, MemIndex, Reason, Responder, RunError, item_id,
};
use vinc_tests::SplitMix64;

/// Replace `from` by `to` in `msg` (an id inside an ids part), and fix nothing else: the lengths do not change.
fn swap_bytes(msg: &mut [u8], from: &[u8], to: &[u8]) -> bool {
    match msg.windows(from.len()).position(|w| w == from) {
        Some(at) => {
            msg[at..at + to.len()].copy_from_slice(to);
            true
        }
        None => false,
    }
}

/// Two sets of 200 items that differ in one item each way: `y` on the initiator, `x` (the next key) on the responder.
/// A tampering channel makes the initiator's id of `y` read as the id of `x`, which is exactly what an id collision
/// looks like to the responder: it takes `y` for an item it has, and never sends `x`. Without the final check the
/// session would end with an empty difference.
#[test]
fn a_forced_id_collision_is_detected_and_resolved_by_items() {
    let mut rng = SplitMix64::new(9);
    let common = fixed_set(&mut rng, 198, 40);
    let y = vec![0xBB; 40];
    let mut x = y.clone();
    x[39] = 0xBC;
    let (mut a, mut b) = (common.clone(), common);
    a.push(y.clone());
    b.push(x.clone());
    let (a, b) = (common::sorted(a), common::sorted(b));
    let (ia, ib) = (index(&a), index(&b));

    let (mut collided, mut checks, mut misses) = (0, 0, 0);
    let o = run_with(
        &mut Initiator::new(Limits::default()),
        &mut Responder::new(Limits::default()),
        &ia,
        &ib,
        |d, m| {
            let kind = frame_body(m).ok().and_then(|body| body.get(1).map(|t| t & !tag::INF));
            if d == Dir::ToResponder {
                collided += usize::from(swap_bytes(m, &item_id(&y), &item_id(&x)));
                checks += usize::from(kind == Some(tag::CHECK));
            } else {
                misses += usize::from(kind == Some(tag::MISS));
            }
        },
    )
    .unwrap();
    assert_eq!(collided, 1, "the collision was injected once, in the ids part");
    assert_eq!(
        (checks, misses),
        (2, 1),
        "the check failed once, then passed after the exact pass"
    );
    assert_exact(&o, &a, &b);
    assert_eq!(o.here, vec![x]);
    assert_eq!(o.there, vec![y]);
}

/// A responder whose whole-set fingerprint is wrong, as a faulty or lying peer would have it.
struct Lying<'a>(&'a MemIndex);

impl ItemIndex for Lying<'_> {
    type Error = MemError;
    fn count(&self) -> Result<usize, MemError> {
        self.0.count()
    }
    fn rank(&self, bound: &[u8]) -> Result<usize, MemError> {
        self.0.rank(bound)
    }
    fn read(&self, i: usize, buf: &mut [u8]) -> Result<usize, MemError> {
        self.0.read(i, buf)
    }
    fn fingerprint(&self, a: usize, b: usize) -> Result<Fingerprint, MemError> {
        let fp = self.0.fingerprint(a, b)?;
        Ok(if a == 0 && b == self.0.len() {
            fp ^ Fingerprint::of_item(b"lie")
        } else {
            fp
        })
    }
}

#[test]
fn a_peer_that_still_disagrees_after_the_exact_pass_fails_loudly() {
    let mut rng = SplitMix64::new(11);
    let a = fixed_set(&mut rng, 500, 40);
    let (b, ..) = mutate(&mut rng, &a, 6, 40);
    let (ia, ib) = (index(&a), index(&b));
    let r = run_with(
        &mut Initiator::new(Limits::default()),
        &mut Responder::new(Limits::default()),
        &ia,
        &Lying(&ib),
        |_, _| {},
    );
    assert!(matches!(r, Err(Error::Mismatch)), "{r:?}");
}

// ---- resets ------------------------------------------------------------------------------------------------------

fn serve(mut end: End, set: MemIndex) -> thread::JoinHandle<Result<(), RunError<(), MemError>>> {
    thread::spawn(move || Responder::new(Limits::default()).serve(&mut end, |r| (r == b"set").then_some(&set)))
}

#[test]
fn the_driver_reconciles_over_a_channel() {
    let mut rng = SplitMix64::new(12);
    let a = fixed_set(&mut rng, 5000, 40);
    let (b, added, removed) = mutate(&mut rng, &a, 40, 40);
    let (ia, ib) = (index(&a), index(&b));
    let (mut c1, c2) = pair();
    let server = serve(c2, ib);
    let mut init = Initiator::new(Limits::default());
    init.run(&mut c1, &&ia, b"set").unwrap();
    server.join().unwrap().unwrap();
    let rep = init.report().unwrap();
    assert_eq!(common::sorted(rep.missing_here().map(<[u8]>::to_vec).collect()), added);
    assert_eq!(
        common::sorted(rep.missing_there().map(<[u8]>::to_vec).collect()),
        removed
    );
}

#[test]
fn a_reset_mid_exchange_retries_the_whole_session() {
    let mut rng = SplitMix64::new(13);
    let a = fixed_set(&mut rng, 20_000, 40);
    let (b, added, removed) = mutate(&mut rng, &a, 200, 40);
    let (ia, ib) = (index(&a), index(&b));
    for reset_at in [1usize, 2, 3, 4] {
        let mut attempt = 0;
        let mut servers = Vec::new();
        let mut init = Initiator::new(Limits::default());
        init.run_retry(
            || {
                attempt += 1;
                let (mut c1, c2) = pair();
                if attempt == 1 {
                    c1.reset_after = Some(reset_at);
                }
                servers.push(serve(c2, ib.clone()));
                Ok(c1)
            },
            &&ia,
            b"set",
            3,
        )
        .unwrap();
        assert_eq!(attempt, 2, "reset at message {reset_at}: one retry");
        let rep = init.report().unwrap();
        assert_eq!(common::sorted(rep.missing_here().map(<[u8]>::to_vec).collect()), added);
        assert_eq!(
            common::sorted(rep.missing_there().map(<[u8]>::to_vec).collect()),
            removed
        );
        for s in servers {
            // The first responder saw the initiator reset or vanish; the second finished.
            let _ = s.join().unwrap();
        }
    }
}

#[test]
fn every_attempt_reset_is_exhausted_not_hung() {
    let mut rng = SplitMix64::new(14);
    let a = fixed_set(&mut rng, 2000, 40);
    let (b, ..) = mutate(&mut rng, &a, 20, 40);
    let (ia, ib) = (index(&a), index(&b));
    let mut init = Initiator::new(Limits::default());
    let r = init.run_retry(
        || {
            let (mut c1, c2) = pair();
            c1.reset_after = Some(1);
            let _ = serve(c2, ib.clone());
            Ok(c1)
        },
        &&ia,
        b"set",
        3,
    );
    assert_eq!(r, Err(RunError::Exhausted));
}

#[test]
fn an_unknown_set_resets_the_stream() {
    let mut rng = SplitMix64::new(15);
    let a = fixed_set(&mut rng, 100, 40);
    let ia = index(&a);
    let (mut c1, mut c2) = pair();
    let server = thread::spawn(move || Responder::new(Limits::default()).serve(&mut c2, |_| None::<MemIndex>));
    let r = Initiator::new(Limits::default()).run(&mut c1, &&ia, b"nope");
    assert_eq!(r, Err(RunError::Reset));
    assert_eq!(server.join().unwrap(), Err(RunError::UnknownSet));
}

// ---- malformed input -----------------------------------------------------------------------------------------------

#[test]
fn malformed_messages_are_refused_with_a_reason() {
    let mut rng = SplitMix64::new(16);
    let a = fixed_set(&mut rng, 300, 40);
    let ia = index(&a);
    let mut out = Vec::new();
    let mut resp = Responder::new(Limits::default());
    // A frame whose length disagrees.
    assert_eq!(
        resp.handle(&ia, &[0, 0, 5, 1], &mut out),
        Err(Error::Malformed(Reason::Frame))
    );
    assert_eq!(
        resp.handle(&ia, &[0], &mut out),
        Err(Error::Malformed(Reason::Truncated))
    );
    // A first message that ends inside the header.
    let mut resp = Responder::new(Limits::default());
    assert_eq!(
        resp.handle(&ia, &[0, 0, 2, 9, 1], &mut out),
        Err(Error::Malformed(Reason::Truncated))
    );
    // An initiator that is not started refuses a message.
    let mut init = Initiator::new(Limits::default());
    assert_eq!(
        init.handle(&ia, &[0, 0, 1, 0], &mut out),
        Err(Error::Malformed(Reason::State))
    );
}

#[test]
fn a_hostile_message_never_panics_and_never_exceeds_the_limits() {
    let mut rng = SplitMix64::new(17);
    let a = fixed_set(&mut rng, 1000, 40);
    let (b, ..) = mutate(&mut rng, &a, 30, 40);
    let (ia, ib) = (index(&a), index(&b));
    let limits = Limits {
        max_message: 4096,
        max_report: 4096,
        max_item: 64,
        max_rounds: 8,
    };
    // Take real messages of a session and flip, drop and extend bytes.
    let mut seen: Vec<Vec<u8>> = Vec::new();
    run_with(
        &mut Initiator::new(Limits::default()),
        &mut Responder::new(Limits::default()),
        &ia,
        &ib,
        |_, m| {
            seen.push(m.clone());
        },
    )
    .unwrap();
    let mut out = Vec::new();
    for msg in &seen {
        for round in 0..200 {
            let mut m = msg.clone();
            match round % 4 {
                0 => {
                    let i = (rng.next_u64() as usize) % m.len();
                    m[i] ^= 1 << (rng.next_u64() % 8);
                }
                1 => m.truncate((rng.next_u64() as usize) % m.len()),
                2 => m.extend((0..(rng.next_u64() % 16)).map(|_| rng.next_u64() as u8)),
                _ => {
                    let n = m.len();
                    let i = 3 + (rng.next_u64() as usize) % (n - 3).max(1);
                    m[i.min(n - 1)] = rng.next_u64() as u8;
                    // Keep the frame valid so the parts are reached.
                    let len = m.len() - 3;
                    m[..3].copy_from_slice(&[(len >> 16) as u8, (len >> 8) as u8, len as u8]);
                }
            }
            let mut resp = Responder::new(limits);
            let _ = resp.handle(&ib, &m, &mut out);
            assert!(out.len() <= 4096 + 200);
            let mut init = Initiator::new(limits);
            let mut first = Vec::new();
            init.start(&ia, b"set", &mut first).unwrap();
            let _ = init.handle(&ia, &m, &mut out);
        }
    }
}
