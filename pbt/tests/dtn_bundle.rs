//! `pinc-dtn`: the reception of a sealed bundle, fed range proofs in any order, sizes and overlaps, resumed, finished
//! from parity and opened; and the signed head decoded from hostile bytes.
//!
//! Where the expected behaviour comes from (`crates/pinc-dtn/src/bundle.rs`, `held.rs`, `head.rs`, and
//! `pinc_dag::ranges`):
//! - `Receiving::feed`: "Verify the proof `stream` for `symbols` (end exclusive) and keep every symbol that
//!   verifies", with "[`DtnError::Tree`] if the stream does not verify against the root, is short or has trailing
//!   bytes (symbols verified before the fault are kept); [`DtnError::ReceptionFull`] if the held set is full";
//! - `Receiving`: "a [`VerifiedRanges`] (the [`Reception`] alias) holds at most its cap of disjoint intervals, and an
//!   arrival that would need more is refused with [`DtnError::ReceptionFull`]"; `VerifiedRanges`: "an insert that
//!   would need more than `N` disjoint intervals fails with [`CapacityError`] and changes nothing";
//! - `Receiving::next_missing`: "The first run of unheld symbols at or after symbol `from`";
//! - `Receiving::is_decodable`: "Whether every block holds at least `k` of its symbols, so [`Receiving::finish`] can
//!   succeed"; `Receiving::finish`: "Recover every missing symbol from any `k` of its block ... Afterwards the buffer
//!   is the complete sealed bundle", "[`DtnError::Incomplete`] if a block holds fewer than `k` symbols", "a held
//!   symbol is never written over";
//! - `Receiving::resume` ("Continue a reception from state the caller kept") and `BlockHeld::new` ("or the buffer of
//!   an earlier set of the same layout to continue it");
//! - `Receiving::open`: "Open every data slice ... and return the payload length";
//! - `SignedHead::decode`: "Decode and validate the structure", and the universal rules (no panic; what decodes
//!   encodes back to the same bytes; a head that verifies is the one the source signed).
//!
//! The existing suites (`tests/dtn_seal.rs`, `tests/dtn_held.rs`) feed whole bundles or fixed patterns; these
//! properties drive arbitrary feed plans against a model of the held set, with the interval cap, the resume and the
//! block-held set compared to the same model.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]

use std::ops::{ControlFlow, Range};

use ephyra::prelude::*;
use ephyra::{check_generator, check_shrinker};
use pinc_crypto::{IdentityAlg, Keypair, Provider, Secret, Software};
use pinc_dtn::DtnError;
use pinc_dtn::bundle::{Outgoing, Plan, Reception, Receiving, seal_bundle, serve, serve_len};
use pinc_dtn::head::{Erasure, SignedHead};
use pinc_dtn::held::{BlockHeld, held_len};
use pinc_dtn::hlc::Hlc;
use pinc_dtn::layout::SliceLayout;
use pinc_dtn::seal::{RecipientKeys, SealSeeds, decapsulate};

const NOW: u64 = 2_000;

fn fill(seed: u64, len: usize) -> Vec<u8> {
    let mut x = seed;
    (0..len)
        .map(|_| {
            x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = x;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (z ^ (z >> 31)) as u8
        })
        .collect()
}

fn keypair(seed: u64) -> Keypair {
    Keypair::from_seed(IdentityAlg::Ed25519, &fill(seed, IdentityAlg::Ed25519.seed_len())).unwrap()
}

struct Recipient {
    keys: RecipientKeys,
    dk: <Software as Provider>::KemDecapsKey,
    xs: <Software as Provider>::X25519Secret,
}

fn recipient(seed: u64) -> Recipient {
    let p = Software;
    let id = keypair(seed);
    let (dk, ek) = p.kem_keygen(&fill(seed + 1, 32).try_into().unwrap(), &fill(seed + 2, 32).try_into().unwrap());
    let xs = p.x25519_secret(&fill(seed + 3, 32).try_into().unwrap());
    let keys = RecipientKeys {
        node: id.node_id(),
        epoch: 1,
        kem_ek: p.kem_encaps_key_bytes(&ek),
        x25519: p.x25519_public(&xs),
    };
    Recipient { keys, dk, xs }
}

/// A sealed bundle with everything a relay holds.
struct Sealed {
    signed: SignedHead,
    layout: SliceLayout,
    sealed: Vec<u8>,
    outboard: Vec<u8>,
    payload: Vec<u8>,
    to: Recipient,
}

impl Sealed {
    fn proof(&self, symbols: &Range<u64>) -> Vec<u8> {
        let mut out = vec![0; serve_len(&self.layout, symbols).unwrap()];
        assert_eq!(
            serve(&self.layout, &self.sealed, &self.outboard, symbols, &mut out).unwrap(),
            out.len()
        );
        out
    }

    fn symbol(&self, s: u64) -> &[u8] {
        let g = self.layout.slice_len() as usize;
        &self.sealed[s as usize * g..(s as usize + 1) * g]
    }
}

/// The bundle shape and the feed plan. Feeds are raw `(start, len)` pairs reduced modulo the bundle's symbols when
/// run, so every shrink of the shape keeps every plan valid.
#[derive(Clone, Debug)]
struct Case {
    k: u8,
    m: u8,
    log: u8,
    len: u64,
    seed: u64,
    /// The interval cap of the `Reception`.
    w: u8,
    feeds: Vec<(u64, u64)>,
}

impl Case {
    fn layout(&self) -> SliceLayout {
        SliceLayout::new(self.k, self.m, self.log, self.len).unwrap()
    }

    fn seal(&self) -> Sealed {
        let layout = self.layout();
        let sender = keypair(1);
        let to = recipient(10);
        let seeds = SealSeeds {
            eph_x25519: Secret::new(fill(self.seed, 32).try_into().unwrap()),
            kem_m: Secret::new(fill(self.seed + 1, 32).try_into().unwrap()),
        };
        let plan = Plan {
            created: Hlc::new(1_000, 0),
            lifetime_ms: 60_000,
            copies: 8,
            erasure: Erasure { k: self.k, m: self.m },
            slice_log: self.log,
        };
        let payload = fill(self.seed ^ 0x5555, self.len as usize);
        let mut sealed = vec![0xaa; layout.total_len() as usize];
        let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
        let out = Outgoing {
            recipient: &to.keys,
            plan,
            seeds: &seeds,
        };
        let signed = seal_bundle(&Software, &sender, &out, &payload, &mut sealed, &mut outboard).unwrap();
        Sealed {
            signed,
            layout,
            sealed,
            outboard,
            payload,
            to,
        }
    }

    /// The feeds as symbol ranges of this layout, each non-empty.
    fn ranges(&self) -> Vec<Range<u64>> {
        let total = self.layout().total_symbols();
        self.feeds
            .iter()
            .map(|&(s, l)| {
                let s = s % total;
                s..(s + 1 + l % (total - s))
            })
            .collect()
    }
}

/// Draw a feed plan aimed at the decodable boundary: random runs, or per block a random choice of `k - 1`, `k` or
/// `k + 1` single symbols, or whole blocks; shuffled, with repeats.
fn draw_feeds(g: &mut Source, layout: &SliceLayout) -> Vec<(u64, u64)> {
    let total = layout.total_symbols();
    let mut feeds = Vec::new();
    match g.int(0u8..=3) {
        0 => {
            for _ in 0..g.int(0usize..=12) {
                feeds.push((g.int(0..=total - 1), g.int(0u64..=6)));
            }
        },
        1 | 2 => {
            for b in 0..layout.blocks() {
                let (start, n, k) = (layout.block_start(b), layout.block_n(b), layout.block_k(b));
                let want = (k as i64 + g.int(-1i64..=1)).clamp(0, n as i64) as usize;
                let mut idx: Vec<u64> = (0..n as u64).collect();
                for i in 0..want {
                    let j = i + g.index(n - i);
                    idx.swap(i, j);
                    feeds.push((start + idx[i], 0));
                }
            }
        },
        _ => feeds.push((0, total)),
    }
    for i in (1..feeds.len()).rev() {
        let j = g.index(i + 1);
        feeds.swap(i, j);
    }
    if !feeds.is_empty() && g.bool_with(0.2) {
        let r = feeds[g.index(feeds.len())];
        feeds.push(r);
    }
    feeds
}

fn draw_case(g: &mut Source) -> Case {
    let k = *g.weighted(&[(4, 1u8), (6, 2), (6, 3), (3, 5), (1, 16)]);
    let m = *g.weighted(&[(2, 0u8), (5, 1), (5, 2), (2, 4)]);
    let log = *g.weighted(&[(8, 0u8), (2, 1), (1, 4)]);
    let plain = (1024u64 << log) - 16;
    let data = g.int(1u64..=if log == 4 { 4 } else { 20 });
    let any = g.int(1..=plain);
    let len = (data - 1) * plain + *g.weighted(&[(3, 1u64), (3, plain), (4, any)]);
    let w = *g.weighted(&[(1, 1u8), (1, 2), (1, 3), (4, 255)]);
    let mut c = Case {
        k,
        m,
        log,
        len,
        seed: g.int(0u64..=u64::MAX / 2),
        w,
        feeds: Vec::new(),
    };
    c.feeds = draw_feeds(g, &c.layout());
    c
}

fn shrink_case(c: &Case, visit: &mut dyn FnMut(Case) -> ControlFlow<()>) -> ControlFlow<()> {
    for i in 0..c.feeds.len() {
        let mut feeds = c.feeds.clone();
        feeds.remove(i);
        visit(Case { feeds, ..c.clone() })?;
    }
    if c.len > 1 {
        visit(Case { len: c.len / 2, ..c.clone() })?;
        visit(Case { len: c.len - 1, ..c.clone() })?;
    }
    if c.k > 1 {
        visit(Case { k: c.k - 1, ..c.clone() })?;
    }
    if c.m > 0 {
        visit(Case { m: c.m - 1, ..c.clone() })?;
    }
    if c.log > 0 {
        let len = c.len.min(20 * 1008);
        visit(Case { log: 0, len, ..c.clone() })?;
    }
    if c.w < 255 {
        visit(Case { w: 255, ..c.clone() })?;
    }
    for i in 0..c.feeds.len() {
        let (s, l) = c.feeds[i];
        if l > 0 {
            let mut feeds = c.feeds.clone();
            feeds[i] = (s, 0);
            visit(Case { feeds, ..c.clone() })?;
        }
    }
    ControlFlow::Continue(())
}

fn cases() -> ephyra::BoxGen<Case> {
    (|g: &mut Source| draw_case(g)).with_shrink(shrink_case).boxed()
}

/// The held set as one flag per symbol, with the interval cap of `VerifiedRanges` (`None`: no cap).
struct Model {
    held: Vec<bool>,
    cap: Option<usize>,
}

impl Model {
    fn runs(held: &[bool]) -> usize {
        (0..held.len()).filter(|&s| held[s] && (s == 0 || !held[s - 1])).count()
    }

    /// Insert one symbol; `false` when the cap refuses it (and nothing changes).
    fn insert(&mut self, s: u64) -> bool {
        let was = self.held[s as usize];
        self.held[s as usize] = true;
        if self.cap.is_some_and(|w| Self::runs(&self.held) > w) {
            self.held[s as usize] = was;
            return false;
        }
        true
    }

    fn feed(&mut self, r: &Range<u64>) -> bool {
        r.clone().fold(true, |ok, s| self.insert(s) & ok)
    }

    fn next_missing(&self, from: u64) -> Option<Range<u64>> {
        let n = self.held.len() as u64;
        let a = (from..n).find(|&s| !self.held[s as usize])?;
        let b = (a..n).find(|&s| self.held[s as usize]).unwrap_or(n);
        Some(a..b)
    }

    fn decodable(&self, layout: &SliceLayout) -> bool {
        (0..layout.blocks()).all(|b| {
            let start = layout.block_start(b) as usize;
            self.held[start..start + layout.block_n(b)].iter().filter(|h| **h).count() >= layout.block_k(b)
        })
    }
}

/// Check every held symbol against the model and the sealed bytes, and every unheld one against the model.
fn check_held<H: pinc_dtn::held::HeldSet>(rx: &Receiving<'_, H>, model: &Model, s: &Sealed, step: usize) {
    let g = s.layout.slice_len() as usize;
    for sym in 0..s.layout.total_symbols() {
        assert_eq!(rx.holds(sym), model.held[sym as usize], "holds({sym}) after feed {step}");
        if rx.holds(sym) {
            assert!(
                rx.sealed()[sym as usize * g..(sym as usize + 1) * g] == *s.symbol(sym),
                "held symbol {sym} differs from the sealed one after feed {step}"
            );
        }
    }
    assert_eq!(rx.is_complete(), model.held.iter().all(|h| *h), "is_complete after feed {step}");
    assert_eq!(rx.is_decodable(), model.decodable(&s.layout), "is_decodable after feed {step}");
}

/// Finish and open, checked against the model: a decodable reception finishes to the sealed bundle and opens to the
/// payload; one that is not is `Incomplete` and keeps every held symbol as it was.
fn finish_and_open<H: pinc_dtn::held::HeldSet>(rx: &mut Receiving<'_, H>, model: &Model, s: &Sealed) {
    let mut ob = vec![0; s.layout.outboard_len().unwrap() as usize];
    let mut scratch = vec![0; rx.scratch_len().unwrap()];
    let decodable = model.decodable(&s.layout);
    let r = rx.finish(&mut ob, &mut scratch);
    if decodable {
        assert_eq!(r, Ok(()), "finish of a decodable reception");
        assert!(rx.is_complete(), "complete after finish");
        assert!(rx.sealed() == s.sealed.as_slice(), "the finished buffer is the sealed bundle");
        assert!(ob == s.outboard, "the rebuilt outboard is the sender's");
        let cipher = decapsulate(&Software, &s.to.keys, &s.to.dk, &s.to.xs, s.signed.head()).unwrap();
        let mut out = vec![0; s.layout.padded_len() as usize];
        let n = rx.open(&Software, &cipher, &mut out).unwrap();
        assert_eq!(n, s.payload.len(), "opened length");
        assert!(out[..n] == *s.payload, "opened payload");
    } else {
        assert_eq!(r, Err(DtnError::Incomplete), "finish of an undecodable reception");
        check_held(rx, model, s, usize::MAX);
    }
}

fn feed_result_ok(r: Result<(), DtnError>, accepted: bool, step: usize) {
    if accepted {
        assert_eq!(r, Ok(()), "feed {step}: every symbol fits the held set");
    } else {
        assert_eq!(r, Err(DtnError::ReceptionFull), "feed {step}: a symbol needs more intervals than the cap");
    }
}

/// Feeding honest proofs of any ranges, in any order and with overlaps, keeps exactly the symbols the interval cap
/// admits, reports `ReceptionFull` exactly when one is refused, answers `next_missing` as the model does, and
/// finishes and opens exactly when every block holds `k` symbols.
#[ephyra::test(gen = cases(), tests = 200)]
fn a_reception_holds_what_it_was_fed_and_finishes_exactly_when_decodable(c: Case) {
    let s = c.seal();
    let total = s.layout.total_symbols();
    let mut buf = vec![0; s.layout.total_len() as usize];
    let mut rx = Reception::<255>::new(&s.signed, &mut buf, NOW).unwrap();
    let mut model = Model {
        held: vec![false; total as usize],
        cap: Some(usize::from(c.w)),
    };
    // The cap of the reception under test is `w`; `Reception<255>` is the uncapped run for `w == 255`.
    let mut small = vec![0; s.layout.total_len() as usize];
    let mut rx_w = match c.w {
        1 => Some(Box::new(Reception::<1>::new(&s.signed, &mut small, NOW).unwrap()) as Box<dyn Fed + '_>),
        2 => Some(Box::new(Reception::<2>::new(&s.signed, &mut small, NOW).unwrap()) as Box<dyn Fed + '_>),
        3 => Some(Box::new(Reception::<3>::new(&s.signed, &mut small, NOW).unwrap()) as Box<dyn Fed + '_>),
        _ => None,
    };
    let mut full = Model {
        held: vec![false; total as usize],
        cap: None,
    };
    for (i, r) in c.ranges().iter().enumerate() {
        let proof = s.proof(r);
        feed_result_ok(rx.feed(r.clone(), &proof), full.feed(r), i);
        check_held(&rx, &full, &s, i);
        for from in 0..=total + 1 {
            assert_eq!(rx.next_missing(from), full.next_missing(from), "next_missing({from}) after feed {i}");
        }
        if let Some(w) = rx_w.as_mut() {
            let accepted = model.feed(r);
            feed_result_ok(w.feed(r.clone(), &proof), accepted, i);
            for sym in 0..total {
                assert_eq!(w.holds(sym), model.held[sym as usize], "capped holds({sym}) after feed {i}");
            }
            for from in 0..=total + 1 {
                assert_eq!(w.next_missing(from), model.next_missing(from), "capped next_missing({from}) after feed {i}");
            }
        }
    }
    ephyra::cover(full.decodable(&s.layout), "decodable");
    ephyra::cover(!full.decodable(&s.layout), "not decodable");
    ephyra::cover(c.w < 255 && model.held != full.held, "the cap refused a symbol");
    finish_and_open(&mut rx, &full, &s);
}

/// The calls of a capped reception the property uses, over every cap.
trait Fed {
    fn feed(&mut self, r: Range<u64>, proof: &[u8]) -> Result<(), DtnError>;
    fn holds(&self, s: u64) -> bool;
    fn next_missing(&self, from: u64) -> Option<Range<u64>>;
}

impl<const W: usize> Fed for Reception<'_, W> {
    fn feed(&mut self, r: Range<u64>, proof: &[u8]) -> Result<(), DtnError> {
        Receiving::feed(self, r, proof)
    }
    fn holds(&self, s: u64) -> bool {
        Receiving::holds(self, s)
    }
    fn next_missing(&self, from: u64) -> Option<Range<u64>> {
        Receiving::next_missing(self, from)
    }
}

/// A reception cut after any feed and continued with `resume` from the kept buffer and held set, as a `Reception`
/// and as a `BlockHeld` kept in its own buffer, ends exactly as the uncut run: the same held symbols after every
/// feed, the same finish, the same payload.
#[ephyra::test(gen = (cases(), gens::int(0usize..=16)), tests = 150)]
fn a_reception_resumed_after_any_feed_ends_as_the_uncut_one(c: Case, cut: usize) {
    let s = c.seal();
    let total = s.layout.total_symbols();
    let ranges = c.ranges();
    let cut = cut.min(ranges.len());
    let mut model = Model {
        held: vec![false; total as usize],
        cap: None,
    };
    let mut buf = vec![0; s.layout.total_len() as usize];
    let mut bbuf = vec![0; s.layout.total_len() as usize];
    let mut hbuf = vec![0; held_len(&s.layout).unwrap()];
    let have = {
        let mut rx = Reception::<255>::new(&s.signed, &mut buf, NOW).unwrap();
        let mut bx = Receiving::resume(&s.signed, &mut bbuf, BlockHeld::new(&s.layout, &mut hbuf[..]).unwrap(), NOW)
            .unwrap();
        for (i, r) in ranges[..cut].iter().enumerate() {
            let proof = s.proof(r);
            model.feed(r);
            assert_eq!(rx.feed(r.clone(), &proof), Ok(()), "feed {i} before the cut");
            assert_eq!(bx.feed(r.clone(), &proof), Ok(()), "block-held feed {i} before the cut");
            check_held(&rx, &model, &s, i);
            check_held(&bx, &model, &s, i);
        }
        rx.have().clone()
    };
    let mut rx = Reception::<255>::resume(&s.signed, &mut buf, have, NOW).unwrap();
    let mut bx =
        Receiving::resume(&s.signed, &mut bbuf, BlockHeld::new(&s.layout, &mut hbuf[..]).unwrap(), NOW).unwrap();
    check_held(&rx, &model, &s, cut);
    check_held(&bx, &model, &s, cut);
    for (i, r) in ranges[cut..].iter().enumerate() {
        let proof = s.proof(r);
        model.feed(r);
        assert_eq!(rx.feed(r.clone(), &proof), Ok(()), "feed {} after the cut", cut + i);
        assert_eq!(bx.feed(r.clone(), &proof), Ok(()), "block-held feed {} after the cut", cut + i);
        check_held(&rx, &model, &s, cut + i);
        check_held(&bx, &model, &s, cut + i);
    }
    finish_and_open(&mut rx, &model, &s);
    finish_and_open(&mut bx, &model, &s);
}

/// One way a relay can spoil a proof stream.
#[derive(Clone, Copy, Debug)]
enum Spoil {
    /// Flip bits of the byte at this index (modulo the length).
    Flip(usize, u8),
    /// Keep only this many bytes (modulo the length).
    Cut(usize),
    /// Append one byte.
    Append(u8),
    /// Send the proof of another range of the same bundle.
    Other(u64, u64),
}

/// A spoiled proof stream is refused with `Tree`, every symbol held afterwards is the sealed one, and the reception
/// still finishes and opens once the honest proof of everything arrives.
#[ephyra::test(gen = (cases(), gens::int(0usize..=16), spoils()), tests = 200)]
fn a_spoiled_proof_is_refused_and_never_puts_a_wrong_byte_in_a_held_symbol(c: Case, at: usize, spoil: Spoil) {
    let s = c.seal();
    let total = s.layout.total_symbols();
    let mut ranges = c.ranges();
    if ranges.is_empty() {
        ranges.push(0..total);
    }
    let at = at % ranges.len();
    let mut model = Model {
        held: vec![false; total as usize],
        cap: None,
    };
    let mut buf = vec![0; s.layout.total_len() as usize];
    let mut rx = Reception::<255>::new(&s.signed, &mut buf, NOW).unwrap();
    for (i, r) in ranges.iter().enumerate() {
        let mut proof = s.proof(r);
        if i != at {
            model.feed(r);
            assert_eq!(rx.feed(r.clone(), &proof), Ok(()), "honest feed {i}");
            check_held(&rx, &model, &s, i);
            continue;
        }
        let honest = proof.clone();
        match spoil {
            Spoil::Flip(x, bits) => {
                let x = x % proof.len();
                proof[x] ^= bits.max(1);
            },
            Spoil::Cut(x) => proof.truncate(x % proof.len()),
            Spoil::Append(b) => proof.push(b),
            Spoil::Other(a, l) => {
                let a = a % total;
                proof = s.proof(&(a..a + 1 + l % (total - a)));
            },
        }
        if proof == honest {
            model.feed(r);
            assert_eq!(rx.feed(r.clone(), &proof), Ok(()), "unchanged feed {i}");
            continue;
        }
        let res = rx.feed(r.clone(), &proof);
        assert!(matches!(res, Err(DtnError::Tree(_))), "spoiled feed {i} gave {res:?}");
        // Symbols verified before the fault are kept: the model takes whatever the reception now holds, after
        // checking every held symbol is the sealed one and none was lost.
        let g = s.layout.slice_len() as usize;
        for sym in 0..total {
            if model.held[sym as usize] {
                assert!(rx.holds(sym), "symbol {sym} held before the spoiled feed was lost");
            }
            if rx.holds(sym) {
                assert!(r.contains(&sym) || model.held[sym as usize], "symbol {sym} outside the fed range became held");
                assert!(
                    rx.sealed()[sym as usize * g..(sym as usize + 1) * g] == *s.symbol(sym),
                    "held symbol {sym} differs from the sealed one after the spoiled feed"
                );
                model.held[sym as usize] = true;
            }
        }
    }
    let all = 0..total;
    model.feed(&all);
    assert_eq!(rx.feed(all.clone(), &s.proof(&all)), Ok(()), "the honest proof of everything");
    finish_and_open(&mut rx, &model, &s);
}

fn spoils() -> ephyra::BoxGen<Spoil> {
    (|g: &mut Source| match g.int(0u8..=3) {
        0 => Spoil::Flip(g.int(0usize..=1 << 20), g.int(1u8..=255)),
        1 => Spoil::Cut(g.int(0usize..=1 << 20)),
        2 => Spoil::Append(g.int(0u8..=255)),
        _ => Spoil::Other(g.int(0u64..=64), g.int(0u64..=8)),
    })
    .boxed()
}

fn signed_head(g: &mut Source) -> (Vec<u8>, SignedHead) {
    let c = Case {
        k: g.int(1u8..=8),
        m: g.int(0u8..=4),
        log: 0,
        len: g.int(1u64..=3000),
        seed: g.int(0u64..=1000),
        w: 255,
        feeds: Vec::new(),
    };
    let s = c.seal();
    let mut out = vec![0; s.signed.encoded_len()];
    assert_eq!(s.signed.encode(&mut out).unwrap(), out.len());
    (out, s.signed)
}

/// Whatever bytes arrive as a signed head: decoding never panics, what decodes encodes back to the same bytes, and a
/// head that verifies is the head the source signed.
#[ephyra::test(gen = (|g: &mut Source| {
    let (valid, signed) = signed_head(g);
    let mut bytes = valid;
    for _ in 0..g.int(1u8..=3) {
        bytes = pinc_pbt::mangle(g, &bytes);
    }
    (bytes, signed)
}).boxed(), tests = 300)]
fn a_hostile_signed_head_decodes_to_itself_or_fails(input: (Vec<u8>, SignedHead)) {
    let (bytes, original) = input;
    let Ok(h) = SignedHead::decode(&bytes) else {
        return;
    };
    let mut out = vec![0; h.encoded_len()];
    let n = h.encode(&mut out).unwrap();
    assert!(out[..n] == *bytes, "a decoded head encodes to other bytes");
    if h.verify().is_ok() {
        assert_eq!(h.head(), original.head(), "a head that verifies differs from the signed one");
    }
    let layout = h.head().layout().unwrap();
    if layout.total_len() <= 1 << 20 {
        let mut buf = vec![0; layout.total_len() as usize];
        let r = Reception::<8>::new(&h, &mut buf, NOW).map(|_| ());
        assert_eq!(r.is_ok(), h.verify().is_ok() && !h.head().is_expired(NOW), "a reception starts exactly for a valid head");
    }
}

fn case_ok(c: &Case) -> bool {
    SliceLayout::new(c.k, c.m, c.log, c.len).is_ok() && c.ranges().iter().all(|r| r.start < r.end)
}

fn case_size(c: &Case) -> u64 {
    c.feeds.iter().map(|f| 1 + f.1).sum::<u64>() + c.len + u64::from(c.k) + u64::from(c.m) + u64::from(c.log) + u64::from(255 - c.w)
}

#[test]
fn the_case_generator_builds_valid_layouts_and_plans_and_shrinks_within_them() {
    check_generator(&Config::default().tests(200), cases(), case_ok).assert_passed();
    check_shrinker(&Config::default().tests(100), cases(), case_ok, case_size).assert_passed();
}
