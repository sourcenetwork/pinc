//! `pinc-connect`: the mailbox against a plain model, over every operation interleaved.
//!
//! Where the expected behaviour comes from: the module documentation of `pinc_connect::mailbox`:
//! "The bytes held for one member never exceed `BYTES` (headers included), and the members never exceed `NODES`",
//! "A message is delivered at most once", "Overflow drops the oldest messages first, and age drops from the front;
//! every drop is counted in [`Stats`], so a loss is never silent", "Messages leave in the order they arrived.
//! [`Mailbox::drain`] steps over a message too long for the caller: the ones it hands over keep their order and the
//! ones it leaves stay in theirs", and the doc comment of each method (`push`, `restore`, `peek`, `pop`,
//! `pop_fitting`, `look`, `remove`, `drain`, `sweep`, `clear`).
//!
//! The existing proptest (`tests/connect_mailbox.rs`) checks push and pop alone with every member fitting, and drain
//! alone at time zero. This model runs all of them interleaved, with more members than slots, with expiry inside
//! `look`, `drain` and `sweep`, with `restore` and `clear`, and checks every held message (body included) after every
//! step. Expiry is lazy in the code (a member's messages expire only when that member is touched, or on `sweep`), and
//! the model is lazy in the same places: the doc of `look`, `drain` and `push` names them.

use std::collections::{BTreeMap, VecDeque};

use ephyra::prelude::*;
use pinc_connect::carrier::MAX_PACKET_LEN;
use pinc_connect::mailbox::{ENTRY_HEAD, Mailbox, Offer, Push, Stats};
use pinc_crypto::{IdentityAlg, NodeId};

const MEMBERS: u8 = 6;

fn nid(tag: u8) -> NodeId {
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [tag; 32],
    }
}

fn to_gen() -> impl Gen<Value = u8> {
    gens::int(1u8..=MEMBERS)
}

/// Body lengths: mostly small, with the refusal and quota edges of both mailbox shapes tested below.
fn len_gen() -> ephyra::BoxGen<usize> {
    gens::frequency(vec![
        (6, gens::int(1usize..=160).boxed()),
        (2, gens::int(1usize..=MAX_PACKET_LEN + 1).boxed()),
        (
            2,
            gens::pick_from(vec![0usize, 1, 547, 548, 549, 1547, 1548, MAX_PACKET_LEN, MAX_PACKET_LEN + 1]).boxed(),
        ),
    ])
    .boxed()
}

fn dt_gen() -> ephyra::BoxGen<u64> {
    gens::frequency(vec![(6, gens::int(0u64..=3).boxed()), (1, gens::int(0u64..=60).boxed())]).boxed()
}

fn max_len_gen() -> ephyra::BoxGen<usize> {
    gens::frequency(vec![
        (3, gens::constant(MAX_PACKET_LEN).boxed()),
        (3, gens::int(0usize..=200).boxed()),
        (1, gens::int(0usize..=usize::MAX).boxed()),
    ])
    .boxed()
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    Sweep(#[ephyra(gen = dt_gen())] u64),
    Clear(#[ephyra(gen = to_gen())] u8),
    Push(
        #[ephyra(gen = to_gen())] u8,
        #[ephyra(gen = to_gen())] u8,
        #[ephyra(gen = len_gen())] usize,
        #[ephyra(gen = dt_gen())] u64,
    ),
    /// A restored message that arrived `back` before now (never before the member's newest, never expired).
    Restore(
        #[ephyra(gen = to_gen())] u8,
        #[ephyra(gen = to_gen())] u8,
        #[ephyra(gen = len_gen())] usize,
        #[ephyra(gen = gens::int(0u64..=80))] u64,
    ),
    Pop(#[ephyra(gen = to_gen())] u8, #[ephyra(gen = dt_gen())] u64),
    Look(
        #[ephyra(gen = to_gen())] u8,
        #[ephyra(gen = max_len_gen())] usize,
        #[ephyra(gen = dt_gen())] u64,
    ),
    PopFitting(
        #[ephyra(gen = to_gen())] u8,
        #[ephyra(gen = max_len_gen())] usize,
        #[ephyra(gen = dt_gen())] u64,
    ),
    /// Remove by a seq: 0 the front's, 1 the one after the front's, 2 the newest stored anywhere.
    Remove(#[ephyra(gen = to_gen())] u8, #[ephyra(gen = gens::int(0u8..=2))] u8),
    /// A drain whose caller answers from `policy` (bit 0 taken, bit 1 go on), then takes everything.
    Drain(
        #[ephyra(gen = to_gen())] u8,
        #[ephyra(gen = max_len_gen())] usize,
        #[ephyra(gen = gens::vec(gens::int(0u8..=3)).len(0..=6))] Vec<u8>,
        #[ephyra(gen = dt_gen())] u64,
    ),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Msg {
    src: u8,
    flag: u8,
    body: Vec<u8>,
    at: u64,
    seq: u64,
}

struct Model<const N: usize, const B: usize> {
    held: BTreeMap<u8, VecDeque<Msg>>,
    stats: Stats,
    next_seq: u64,
    age: u64,
}

impl<const N: usize, const B: usize> Model<N, B> {
    fn expire(&mut self, to: u8, now: u64) {
        let age = self.age;
        if let Some(q) = self.held.get_mut(&to) {
            while q.front().is_some_and(|m| now.saturating_sub(m.at) >= age) {
                q.pop_front();
                self.stats.expired += 1;
            }
        }
    }

    fn free_if_empty(&mut self, to: u8) {
        if self.held.get(&to).is_some_and(VecDeque::is_empty) {
            self.held.remove(&to);
        }
    }

    fn push(&mut self, now: u64, at: u64, to: u8, src: u8, flag: u8, body: &[u8]) -> Push {
        let size = ENTRY_HEAD + body.len();
        if body.is_empty() || body.len() > MAX_PACKET_LEN || size > B {
            self.stats.refused_oversize += 1;
            return Push::TooLarge;
        }
        if !self.held.contains_key(&to) {
            if self.held.len() >= N {
                self.stats.refused_members += 1;
                return Push::NoSlot;
            }
            self.held.insert(to, VecDeque::new());
        }
        self.expire(to, now);
        let q = self.held.entry(to).or_default();
        let first = q.is_empty();
        let mut dropped = 0u32;
        while q.iter().map(|m| ENTRY_HEAD + m.body.len()).sum::<usize>() + size > B {
            let Some(m) = q.pop_front() else { break };
            self.stats.dropped_oldest += 1;
            self.stats.dropped_oldest_bytes += (ENTRY_HEAD + m.body.len()) as u64;
            dropped += 1;
        }
        let seq = self.next_seq;
        q.push_back(Msg {
            src,
            flag,
            body: body.to_vec(),
            at,
            seq,
        });
        self.next_seq += 1;
        self.stats.stored += 1;
        Push::Stored { seq, dropped, first }
    }

    /// `look`: expire, the front if it fits, free the member if it is empty.
    fn look(&mut self, now: u64, to: u8, max_len: usize) -> Option<Msg> {
        self.held.get(&to)?;
        self.expire(to, now);
        let out = self.held.get(&to).and_then(|q| q.front()).filter(|m| m.body.len() <= max_len).cloned();
        self.free_if_empty(to);
        out
    }

    fn remove(&mut self, to: u8, seq: u64) -> bool {
        let Some(q) = self.held.get_mut(&to) else { return false };
        let removed = q.front().is_some_and(|m| m.seq == seq);
        if removed {
            q.pop_front();
            self.stats.delivered += 1;
        }
        self.free_if_empty(to);
        removed
    }

    /// `drain`: what is offered, in order, and the answer given to each.
    fn drain(&mut self, now: u64, to: u8, max_len: usize, policy: &[u8]) -> Vec<(Msg, Offer)> {
        let mut offered = Vec::new();
        if !self.held.contains_key(&to) {
            return offered;
        }
        self.expire(to, now);
        let q = self.held.remove(&to).unwrap_or_default();
        let mut kept = VecDeque::new();
        let mut rest = q.into_iter();
        for m in rest.by_ref() {
            if m.body.len() > max_len.min(MAX_PACKET_LEN) {
                kept.push_back(m);
                continue;
            }
            let p = policy.get(offered.len()).copied().unwrap_or(3);
            let answer = Offer {
                taken: p & 1 != 0,
                go_on: p & 2 != 0,
            };
            offered.push((m.clone(), answer));
            if answer.taken {
                self.stats.delivered += 1;
            } else {
                kept.push_back(m);
            }
            if !answer.go_on {
                break;
            }
        }
        kept.extend(rest);
        if !kept.is_empty() {
            self.held.insert(to, kept);
        }
        offered
    }

    fn sweep(&mut self, now: u64) {
        let members: Vec<u8> = self.held.keys().copied().collect();
        for to in members {
            self.expire(to, now);
            self.free_if_empty(to);
        }
    }

    fn clear(&mut self, to: u8) {
        if let Some(q) = self.held.remove(&to) {
            self.stats.expired += q.len() as u64;
        }
    }
}

fn body_of(tag: u8, len: usize) -> Vec<u8> {
    (0..len).map(|i| tag ^ (i as u8).wrapping_mul(31)).collect()
}

fn delivered_eq(d: Option<pinc_connect::mailbox::Delivered>, buf: &[u8], want: Option<&Msg>) -> bool {
    match (d, want) {
        (None, None) => true,
        (Some(d), Some(m)) => {
            d.src == nid(m.src) && d.flag == m.flag && d.len == m.body.len() && d.seq == m.seq && buf.get(..d.len) == Some(&m.body[..])
        },
        _ => false,
    }
}

/// Runs `ops` on a mailbox of `N` members and `B` bytes each and on the model, comparing after every step.
fn run<const N: usize, const B: usize>(age: u64, start: u64, ops: &[Op]) {
    let mut m: Mailbox<N, B> = Mailbox::new(age, 0x5eed);
    let mut model: Model<N, B> = Model {
        held: BTreeMap::new(),
        stats: Stats::default(),
        next_seq: 0,
        age,
    };
    let mut now = start;
    let mut tag = 0u8;
    let mut buf = [0u8; MAX_PACKET_LEN];
    for (step, op) in ops.iter().enumerate() {
        match *op {
            Op::Sweep(dt) => {
                now = now.saturating_add(dt);
                m.sweep(now);
                model.sweep(now);
            },
            Op::Clear(to) => {
                m.clear(&nid(to));
                model.clear(to);
            },
            Op::Push(to, src, len, dt) => {
                now = now.saturating_add(dt);
                tag = tag.wrapping_add(1);
                let body = body_of(tag, len);
                let got = m.push(now, &nid(to), &nid(src), tag, &body);
                let want = model.push(now, now, to, src, tag, &body);
                assert_eq!(got, want, "step {step}: push {op:?}");
            },
            Op::Restore(to, src, len, back) => {
                let newest = model.held.get(&to).and_then(|q| q.back()).map_or(0, |m| m.at);
                let at = now.saturating_sub(back).max(newest).min(now);
                // The host does not restore a message that has expired (the doc of `restore`).
                if now.saturating_sub(at) >= age {
                    continue;
                }
                tag = tag.wrapping_add(1);
                let body = body_of(tag, len);
                let got = m.restore(now, at, &nid(to), &nid(src), tag, &body);
                let want = model.push(now, at, to, src, tag, &body);
                assert_eq!(got, want, "step {step}: restore {op:?} at {at}");
            },
            Op::Pop(to, dt) => {
                now = now.saturating_add(dt);
                let got = m.pop(now, &nid(to), &mut buf);
                let want = model.look(now, to, MAX_PACKET_LEN);
                if let Some(w) = &want {
                    assert!(model.remove(to, w.seq));
                }
                assert!(delivered_eq(got, &buf, want.as_ref()), "step {step}: pop {op:?}: got {got:?}, want {want:?}");
            },
            Op::Look(to, max_len, dt) => {
                now = now.saturating_add(dt);
                let got = m.look(now, &nid(to), &mut buf, max_len);
                let want = model.look(now, to, max_len);
                assert!(delivered_eq(got, &buf, want.as_ref()), "step {step}: look {op:?}: got {got:?}, want {want:?}");
            },
            Op::PopFitting(to, max_len, dt) => {
                now = now.saturating_add(dt);
                let got = m.pop_fitting(now, &nid(to), &mut buf, max_len);
                let want = model.look(now, to, max_len);
                if let Some(w) = &want {
                    assert!(model.remove(to, w.seq));
                }
                assert!(
                    delivered_eq(got, &buf, want.as_ref()),
                    "step {step}: pop_fitting {op:?}: got {got:?}, want {want:?}"
                );
            },
            Op::Remove(to, which) => {
                let front = model.held.get(&to).and_then(|q| q.front()).map_or(0, |m| m.seq);
                let seq = match which {
                    0 => front,
                    1 => front + 1,
                    _ => model.next_seq.saturating_sub(1),
                };
                let got = m.remove(&nid(to), seq);
                let want = model.remove(to, seq);
                assert_eq!(got, want, "step {step}: remove {op:?} seq {seq}");
            },
            Op::Drain(to, max_len, ref policy, dt) => {
                now = now.saturating_add(dt);
                let mut got: Vec<(u8, u8, Vec<u8>, u64)> = Vec::new();
                let mut i = 0usize;
                Mailbox::drain(&mut m, |m| m, now, &nid(to), max_len, &mut buf, |_, d, body| {
                    got.push((d.src.bytes[0], d.flag, body.to_vec(), d.seq));
                    let p = policy.get(i).copied().unwrap_or(3);
                    i += 1;
                    Offer {
                        taken: p & 1 != 0,
                        go_on: p & 2 != 0,
                    }
                });
                let want: Vec<(u8, u8, Vec<u8>, u64)> = model
                    .drain(now, to, max_len, policy)
                    .into_iter()
                    .map(|(m, _)| (m.src, m.flag, m.body, m.seq))
                    .collect();
                assert_eq!(got, want, "step {step}: drain {op:?}: what was offered");
            },
        }
        // The whole state, after every step.
        assert_eq!(m.stats(), model.stats, "step {step}: {op:?}: the counters");
        assert_eq!(m.members(), model.held.len(), "step {step}: {op:?}: the members");
        assert!(m.members() <= N, "step {step}: more members than slots");
        for to in 1..=MEMBERS {
            let q = model.held.get(&to);
            let want = q.map_or((0, 0), |q| (q.len(), q.iter().map(|m| ENTRY_HEAD + m.body.len()).sum()));
            let got = m.pending(&nid(to));
            assert!(got.1 <= B, "step {step}: member {to} holds {} bytes, over the quota", got.1);
            assert_eq!(got, want, "step {step}: {op:?}: pending of member {to}");
            for (i, w) in q.into_iter().flatten().enumerate() {
                let got = m.peek(&nid(to), i, &mut buf);
                assert!(
                    got.is_some_and(|(d, at)| at == w.at && delivered_eq(Some(d), &buf, Some(w))),
                    "step {step}: {op:?}: message {i} of member {to}: got {got:?}, want {w:?}"
                );
            }
            assert!(m.peek(&nid(to), want.0, &mut buf).is_none(), "step {step}: peek past the end of member {to}");
        }
    }
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Case {
    #[ephyra(gen = gens::pick_from(vec![40u64, 1, 0, 200, u64::MAX]))]
    age: u64,
    #[ephyra(gen = gens::pick_from(vec![0u64, 1 << 40, u64::MAX - 3000]))]
    start: u64,
    #[ephyra(gen = gens::vec(ephyra::any::<Op>()).len(0..=120))]
    ops: Vec<Op>,
}

/// A small ring (600 bytes, so at most 548 body bytes) and fewer slots than members: the quota, the wrap of the
/// ring and `NoSlot` are reached often.
#[ephyra::test(gen = ephyra::any::<Case>(), tests = 3000)]
fn mailbox_matches_the_model_small_ring(c: Case) {
    run::<4, 600>(c.age, c.start, &c.ops);
}

/// A ring that takes one full packet (1452 bytes) and little else, with two slots for six members.
#[ephyra::test(gen = ephyra::any::<Case>(), tests = 3000)]
fn mailbox_matches_the_model_packet_ring(c: Case) {
    run::<2, 1600>(c.age, c.start, &c.ops);
}

/// A single slot and a ring that is not a multiple of anything: headers and bodies straddle the end of the ring.
#[ephyra::test(gen = ephyra::any::<Case>(), tests = 3000)]
fn mailbox_matches_the_model_one_slot(c: Case) {
    run::<1, 377>(c.age, c.start, &c.ops);
}
