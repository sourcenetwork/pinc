//! Shared harness of the reconcile tests: set generators, a sans-IO runner that counts bytes and messages, and an
//! in-process channel pair for the driver tests.
#![allow(
    dead_code,
    unreachable_pub,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::expect_used
)]

use std::sync::mpsc::{Receiver, Sender, channel};

use vinc_reconcile::{Channel, Error, Initiator, ItemIndex, Limits, MemError, MemIndex, Recv, Responder, Step};
use vinc_tests::SplitMix64;

pub type Item = Vec<u8>;
pub type Err = Error<MemError>;

pub fn index(set: &[Item]) -> MemIndex {
    MemIndex::from_sorted(set.iter().map(Vec::as_slice)).unwrap()
}

pub fn sorted(mut v: Vec<Item>) -> Vec<Item> {
    v.sort_unstable();
    v.dedup();
    v
}

/// `n` distinct random items of exactly `len` bytes.
pub fn fixed_set(rng: &mut SplitMix64, n: usize, len: usize) -> Vec<Item> {
    let mut v: Vec<Item> = (0..n)
        .map(|_| {
            let mut it = vec![0; len];
            rng.fill(&mut it);
            it
        })
        .collect();
    v.sort_unstable();
    v.dedup();
    v
}

/// About `n` distinct random items of 1 to `max_len` bytes; the first bytes come from a small alphabet so that many
/// items are prefixes of others.
pub fn var_set(rng: &mut SplitMix64, n: usize, max_len: usize) -> Vec<Item> {
    sorted(
        (0..n)
            .map(|_| {
                let len = 1 + (rng.next_u64() as usize) % max_len;
                let mut it = vec![0; len];
                rng.fill(&mut it);
                for b in it.iter_mut().take(3) {
                    *b %= 3;
                }
                it
            })
            .collect(),
    )
}

/// `base` with `d` changes: about half removed, the rest added. Returns the new set, the added and the removed items.
pub fn mutate(rng: &mut SplitMix64, base: &[Item], d: usize, len: usize) -> (Vec<Item>, Vec<Item>, Vec<Item>) {
    let removed_n = (d / 2).min(base.len());
    let mut removed = std::collections::BTreeSet::new();
    while removed.len() < removed_n {
        removed.insert((rng.next_u64() as usize) % base.len());
    }
    let mut added = std::collections::BTreeSet::new();
    while added.len() < d - removed_n {
        let mut it = vec![0; len];
        rng.fill(&mut it);
        if base.binary_search(&it).is_err() {
            added.insert(it);
        }
    }
    let gone: Vec<Item> = removed.iter().map(|&i| base[i].clone()).collect();
    let mut out: Vec<Item> = base
        .iter()
        .enumerate()
        .filter(|(i, _)| !removed.contains(i))
        .map(|(_, x)| x.clone())
        .collect();
    let added: Vec<Item> = added.into_iter().collect();
    out.extend(added.iter().cloned());
    out.sort_unstable();
    (out, added, gone)
}

/// The items only in `b` and only in `a`, both ascending.
pub fn sym_diff(a: &[Item], b: &[Item]) -> (Vec<Item>, Vec<Item>) {
    let only_b = b.iter().filter(|x| a.binary_search(x).is_err()).cloned().collect();
    let only_a = a.iter().filter(|x| b.binary_search(x).is_err()).cloned().collect();
    (only_b, only_a)
}

/// Which way a message travels.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Dir {
    ToResponder,
    ToInitiator,
}

/// What a sans-IO run measured.
#[derive(Debug, Default)]
pub struct Outcome {
    pub here: Vec<Item>,
    pub there: Vec<Item>,
    pub bytes_up: usize,
    pub bytes_down: usize,
    pub messages: usize,
}

impl Outcome {
    pub fn bytes(&self) -> usize {
        self.bytes_up + self.bytes_down
    }
}

/// Run a session between an initiator over `a` and a responder over `b`, passing every message through `tamper`.
pub fn run_with<A: ItemIndex<Error = MemError>, B: ItemIndex<Error = MemError>>(
    init: &mut Initiator,
    resp: &mut Responder,
    a: &A,
    b: &B,
    mut tamper: impl FnMut(Dir, &mut Vec<u8>),
) -> Result<Outcome, Err> {
    let mut o = Outcome::default();
    let (mut tx, mut rx) = (Vec::new(), Vec::new());
    resp.reset();
    init.start(a, b"set", &mut tx)?;
    loop {
        tamper(Dir::ToResponder, &mut tx);
        o.bytes_up += tx.len();
        o.messages += 1;
        let mut replies: Vec<Vec<u8>> = Vec::new();
        let mut step = resp.handle(b, &tx, &mut rx)?;
        loop {
            match step {
                Step::Send | Step::Last => replies.push(rx.clone()),
                Step::Chunk => {
                    replies.push(rx.clone());
                    step = resp.resume(b, &mut rx)?;
                    continue;
                }
                Step::Done | Step::Wait => {}
            }
            break;
        }
        let mut next = None;
        for mut m in replies {
            tamper(Dir::ToInitiator, &mut m);
            o.bytes_down += m.len();
            o.messages += 1;
            match init.handle(a, &m, &mut tx)? {
                Step::Send => next = Some(tx.clone()),
                Step::Last => {
                    o.bytes_up += tx.len();
                    o.messages += 1;
                    resp.handle(b, &tx, &mut rx)?;
                }
                Step::Wait | Step::Done | Step::Chunk => {}
            }
        }
        match next {
            Some(m) => tx = m,
            None => break,
        }
    }
    let rep = init.report().expect("session finished");
    o.here = rep.missing_here().map(<[u8]>::to_vec).collect();
    o.there = rep.missing_there().map(<[u8]>::to_vec).collect();
    Ok(o)
}

pub fn run(a: &[Item], b: &[Item]) -> Outcome {
    let (ia, ib) = (index(a), index(b));
    run_with(
        &mut Initiator::new(Limits::default()),
        &mut Responder::new(Limits::default()),
        &ia,
        &ib,
        |_, _| {},
    )
    .unwrap()
}

/// Check that a run found exactly the symmetric difference.
pub fn assert_exact(o: &Outcome, a: &[Item], b: &[Item]) {
    let (only_b, only_a) = sym_diff(a, b);
    assert_eq!(sorted(o.here.clone()), only_b, "items missing here");
    assert_eq!(sorted(o.there.clone()), only_a, "items missing there");
    assert_eq!(o.here.len(), only_b.len(), "no duplicates in here");
    assert_eq!(o.there.len(), only_a.len(), "no duplicates in there");
}

// ---- channels ----------------------------------------------------------------------------------------------------

pub enum Wire {
    Data(Vec<u8>, bool),
    Reset,
}

/// One end of an in-process stream. `reset_after` makes the end see a reset instead of its n-th received message.
pub struct End {
    tx: Sender<Wire>,
    rx: Receiver<Wire>,
    pub received: usize,
    pub reset_after: Option<usize>,
    finished: bool,
}

pub fn pair() -> (End, End) {
    let (t1, r1) = channel();
    let (t2, r2) = channel();
    let mk = |tx, rx| End {
        tx,
        rx,
        received: 0,
        reset_after: None,
        finished: false,
    };
    (mk(t1, r2), mk(t2, r1))
}

impl Channel for End {
    type Error = ();

    fn send(&mut self, msg: &[u8], fin: bool) -> Result<(), ()> {
        // A peer that already left is not an error for the sender: the receiver reports it.
        let _ = self.tx.send(Wire::Data(msg.to_vec(), fin));
        Ok(())
    }

    fn recv(&mut self, buf: &mut Vec<u8>) -> Result<Recv, ()> {
        buf.clear();
        loop {
            if self.finished {
                return Ok(Recv::Finished);
            }
            match self.rx.recv() {
                Ok(Wire::Data(m, fin)) => {
                    self.finished = fin;
                    if m.is_empty() {
                        continue;
                    }
                    self.received += 1;
                    if self.reset_after == Some(self.received) {
                        return Ok(Recv::Reset);
                    }
                    buf.extend_from_slice(&m);
                    return Ok(Recv::Message);
                }
                Ok(Wire::Reset) | Err(_) => return Ok(Recv::Reset),
            }
        }
    }

    fn reset(&mut self) {
        let _ = self.tx.send(Wire::Reset);
    }
}
