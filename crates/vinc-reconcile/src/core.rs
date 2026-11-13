//! The shared engine of the initiator and the responder: message building, part processing, the leaf rules.
//!
//! Invariants: the set is never held; every range, fingerprint and item is re-read from the [`ItemIndex`] when it is
//! needed. All buffers are allocated in `new` from the [`Limits`] and only reused afterwards: bounds and items are
//! checked against `max_item` before they are copied. A part is processed and answered in the order it arrives, so
//! the output depends only on the input messages and the index.
//!
//! A reply holds as many parts as fit the message limit. A part that would pass it is rolled back, and it and the
//! parts after it stay in a frame (their bytes and the bound they continue from). Frames are resumed after newer
//! input, depth first, so the frames held are the depth of the range tree, at most [`MAX_NEST`], each at most one
//! message. A leaf or a split that cannot fit even an empty message is narrowed instead (see [`leaf_ok`] and
//! [`split_fit`]). The reply says by `more` that frames are left.

#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    reason = "a, b, lo, hi, p, q are the positions and items of the range rules, named as in their statement"
)]

use alloc::vec;
use alloc::vec::Vec;
use core::mem;

use vinc_wire::{Reader, varint};

use crate::error::{Error, Reason};
use crate::hash::{FP_LEN, Fingerprint, ID_LEN, item_id};
use crate::index::ItemIndex;
use crate::limits::Limits;
use crate::wire::{
    ALEAF, BLEAF, Items, SPLIT, common_prefix, count, frame_body, frame_header, put_bound, put_parts, put_varint,
    read_bound, tag,
};

/// The most suspended messages a side holds: the range tree is about sixteen levels deep at 2^64 items, and a frame
/// is pushed by at most one message per level, so a valid exchange stays far below this.
pub(crate) const MAX_NEST: usize = 64;

/// The tail of a message that did not fit the reply: its unread parts and the bound they continue from.
#[derive(Debug, Default)]
struct Frame {
    buf: Vec<u8>,
    off: usize,
    left: usize,
    last: Vec<u8>,
}

/// One side of the reported difference: length-prefixed items back to back.
#[derive(Debug, Default)]
pub(crate) struct Arena {
    pub(crate) data: Vec<u8>,
    pub(crate) n: usize,
}

/// Read item `i` into `buf` and return its length.
fn read<I: ItemIndex>(idx: &I, i: usize, buf: &mut [u8]) -> Result<usize, Error<I::Error>> {
    let n = idx.read(i, buf).map_err(Error::Index)?;
    if n > buf.len() { Err(Error::BadIndex) } else { Ok(n) }
}

fn rank<I: ItemIndex>(idx: &I, bound: &[u8]) -> Result<usize, Error<I::Error>> {
    if bound.is_empty() {
        Ok(0)
    } else {
        idx.rank(bound).map_err(Error::Index)
    }
}

/// The message body under construction.
struct Out {
    body: Vec<u8>,
    /// Items staged before the count that precedes them is known.
    stage: Vec<u8>,
    /// The previous bound written in this message.
    last: Vec<u8>,
    /// `last` as it was at the mark.
    snap: Vec<u8>,
    cap: usize,
}

impl Out {
    /// Start a message. The snapshot goes too: a rollback to the start of a message that took no mark restores the
    /// last bound from it, and must not read what an earlier message left.
    fn reset(&mut self) {
        self.body.clear();
        self.stage.clear();
        self.last.clear();
        self.snap.clear();
    }

    /// Remember the end of the message, to undo a part that does not fit.
    fn mark(&mut self) -> usize {
        self.snap.clear();
        self.snap.extend_from_slice(&self.last);
        self.body.len()
    }

    /// Drop everything written since `mark`.
    fn rollback(&mut self, mark: usize) {
        self.body.truncate(mark);
        self.stage.clear();
        self.last.clear();
        self.last.extend_from_slice(&self.snap);
    }

    /// A part's tag and bounds; `hi` is `None` for infinity.
    fn head<E>(&mut self, kind: u8, lo: &[u8], hi: Option<&[u8]>) -> Result<(), Error<E>> {
        self.body.push(if hi.is_none() { kind | tag::INF } else { kind });
        put_bound(&mut self.body, &mut self.last, lo)?;
        if let Some(hi) = hi {
            put_bound(&mut self.body, &mut self.last, hi)?;
        }
        Ok(())
    }

    /// An item as `venc(len) item` onto `stage`.
    fn stage_item<E>(&mut self, item: &[u8]) -> Result<(), Error<E>> {
        put_varint(&mut self.stage, item.len())?;
        self.stage.extend_from_slice(item);
        Ok(())
    }
}

/// Scratch buffers for items and bounds.
struct Scratch {
    p: Vec<u8>,
    q: Vec<u8>,
    l: Vec<u8>,
    r: Vec<u8>,
}

/// The bounds of the part being processed, decoded in place.
struct Bounds {
    lo: Vec<u8>,
    hi: Vec<u8>,
    inf: bool,
    last: Vec<u8>,
    /// `last` as it was before the part being processed.
    snap: Vec<u8>,
}

impl Bounds {
    fn read(&mut self, r: &mut Reader<'_>, inf: bool, max: usize) -> Result<(), Reason> {
        read_bound(&mut self.last, r, max)?;
        self.lo.clear();
        self.lo.extend_from_slice(&self.last);
        self.inf = inf;
        if !inf {
            read_bound(&mut self.last, r, max)?;
            self.hi.clear();
            self.hi.extend_from_slice(&self.last);
        }
        Ok(())
    }

    fn hi(&self) -> Option<&[u8]> {
        if self.inf { None } else { Some(&self.hi) }
    }
}

/// Split `a..b` (within `lo..hi`) into `fan` fingerprint parts; returns the part count.
fn split<I: ItemIndex>(
    out: &mut Out,
    sc: &mut Scratch,
    idx: &I,
    lo: &[u8],
    hi: Option<&[u8]>,
    (a, b, fan): (usize, usize, usize),
) -> Result<usize, Error<I::Error>> {
    let step = (b - a).div_ceil(fan).max(1);
    sc.l.clear();
    sc.l.extend_from_slice(lo);
    let (mut x, mut cnt) = (a, 0);
    while x < b {
        let y = b.min(x + step);
        if y < b {
            let pl = read(idx, y - 1, &mut sc.p)?;
            let ql = read(idx, y, &mut sc.q)?;
            let (p, q) = (sc.p.get(..pl).unwrap_or_default(), sc.q.get(..ql).unwrap_or_default());
            let sep = q.get(..common_prefix(p, q) + 1).ok_or(Error::BadIndex)?;
            sc.r.clear();
            sc.r.extend_from_slice(sep);
            out.head(tag::FP, &sc.l, Some(&sc.r))?;
        } else {
            out.head(tag::FP, &sc.l, hi)?;
        }
        out.body
            .extend_from_slice(&idx.fingerprint(x, y).map_err(Error::Index)?.to_bytes());
        cnt += 1;
        mem::swap(&mut sc.l, &mut sc.r);
        x = y;
    }
    Ok(cnt)
}

/// [`split`] into [`SPLIT`] parts, or into fewer when the separators are so long that the parts pass the message
/// limit on their own. `mark` is the length of the message before the part: a split that passes the limit after
/// something else was written is left to the caller to roll back.
fn split_fit<I: ItemIndex>(
    out: &mut Out,
    sc: &mut Scratch,
    idx: &I,
    (lo, hi): (&[u8], Option<&[u8]>),
    (a, b): (usize, usize),
    mark: usize,
) -> Result<usize, Error<I::Error>> {
    let mut fan = SPLIT;
    loop {
        let cnt = split(out, sc, idx, lo, hi, (a, b, fan))?;
        if out.body.len() <= out.cap || mark > 0 || fan <= 2 {
            return Ok(cnt);
        }
        out.rollback(mark);
        fan /= 2;
    }
}

/// The encoded size of a bound, at most.
fn bound_len(len: usize) -> usize {
    1 + varint::encoded_len(len as u64) + len
}

/// Whether a leaf part for `a..b` fits a message of its own: the ids (`items` false) or the items, with the reply's
/// extras no larger than the items. A range of at most one item is always a leaf, as it cannot be cut further.
fn leaf_ok<I: ItemIndex>(
    sc: &mut Scratch,
    idx: &I,
    cap: usize,
    (lo, hi): (&[u8], Option<&[u8]>),
    (a, b, items): (usize, usize, bool),
) -> Result<bool, Error<I::Error>> {
    if b - a <= 1 {
        return Ok(true);
    }
    let mut size = 1 + bound_len(lo.len()) + hi.map_or(0, |h| bound_len(h.len())) + 2 * varint::MAX_LEN + ALEAF / 8;
    if items {
        for j in a..b {
            size += varint::MAX_LEN + read(idx, j, &mut sc.p)?;
        }
    } else {
        size += (b - a) * ID_LEN;
    }
    Ok(size <= cap)
}

/// An ids part for `a..b`.
fn ids_part<I: ItemIndex>(
    out: &mut Out,
    sc: &mut Scratch,
    idx: &I,
    lo: &[u8],
    hi: Option<&[u8]>,
    a: usize,
    b: usize,
) -> Result<(), Error<I::Error>> {
    out.head(tag::IDS, lo, hi)?;
    put_varint(&mut out.body, b - a)?;
    for j in a..b {
        let n = read(idx, j, &mut sc.p)?;
        out.body.extend_from_slice(&item_id(sc.p.get(..n).unwrap_or_default()));
    }
    Ok(())
}

/// A part of kind `kind` (full or cold) carrying the items `a..b`.
fn items_part<I: ItemIndex>(
    out: &mut Out,
    sc: &mut Scratch,
    idx: &I,
    kind: u8,
    lo: &[u8],
    hi: Option<&[u8]>,
    (a, b): (usize, usize),
) -> Result<(), Error<I::Error>> {
    out.head(kind, lo, hi)?;
    put_varint(&mut out.body, b - a)?;
    for j in a..b {
        let n = read(idx, j, &mut sc.p)?;
        put_varint(&mut out.body, n)?;
        out.body.extend_from_slice(sc.p.get(..n).unwrap_or_default());
    }
    Ok(())
}

/// How one item of a merge relates to the two sides.
enum Cmp<'x> {
    /// Both sides have the item; the index is the position in the peer's list.
    Both(usize),
    /// Only the peer has it.
    Theirs(&'x [u8]),
    /// Only we have it.
    Mine(&'x [u8]),
}

/// Merge our items `a..b` with the peer's ascending list, calling `f` for each item of the union in order.
fn merge<I: ItemIndex>(
    idx: &I,
    sc: &mut Scratch,
    a: usize,
    b: usize,
    theirs: &mut Items<'_, '_>,
    mut f: impl FnMut(Cmp<'_>) -> Result<(), Error<I::Error>>,
) -> Result<(), Error<I::Error>> {
    let (mut j, mut k) = (a, 0);
    let mut mine: Option<usize> = None;
    let mut prev: Option<usize> = None;
    let mut next = theirs.next_item()?;
    loop {
        if mine.is_none() && j < b {
            mine = Some(read(idx, j, &mut sc.p)?);
        }
        let m = mine.map(|n| sc.p.get(..n).unwrap_or_default());
        match (m, next) {
            (None, None) => return Ok(()),
            (Some(m), None) => {
                f(Cmp::Mine(m))?;
                j += 1;
                mine = None;
            }
            (m, Some(t)) => {
                match m.map(|m| m.cmp(t)) {
                    Some(core::cmp::Ordering::Less) => {
                        f(Cmp::Mine(m.unwrap_or_default()))?;
                        j += 1;
                        mine = None;
                        continue;
                    }
                    Some(core::cmp::Ordering::Equal) => {
                        f(Cmp::Both(k))?;
                        j += 1;
                        mine = None;
                    }
                    _ => f(Cmp::Theirs(t))?,
                }
                if let Some(pl) = prev
                    && sc.r.get(..pl).unwrap_or_default() >= t
                {
                    return Err(Reason::Item.into());
                }
                sc.r.clear();
                sc.r.extend_from_slice(t);
                prev = Some(t.len());
                k += 1;
                next = theirs.next_item()?;
            }
        }
    }
}

/// Append `item` to `arena` unless the report would pass `max`.
fn push<E>(arena: &mut Arena, other: usize, max: usize, item: &[u8]) -> Result<(), Error<E>> {
    if arena.data.len() + other + item.len() + varint::MAX_LEN > max {
        return Err(Error::ReportTooLarge);
    }
    put_varint(&mut arena.data, item.len())?;
    arena.data.extend_from_slice(item);
    arena.n += 1;
    Ok(())
}

/// Where processing a message stopped: the parts left, and the offset of the first of them.
struct Stop {
    left: usize,
    at: usize,
}

/// What processing one message left to the caller.
#[derive(Debug, Default)]
pub(crate) struct Answer {
    /// The parts written to the reply.
    pub(crate) cnt: usize,
    /// A cold chunk was received.
    pub(crate) cold: bool,
    /// The received cold chunk was the last.
    pub(crate) cold_end: bool,
    /// The responder refused the final check.
    pub(crate) miss: bool,
}

/// The engine of one session side.
pub(crate) struct Core {
    pub(crate) lim: Limits,
    pub(crate) n: usize,
    pub(crate) init: bool,
    pub(crate) exact: bool,
    /// A leaf part was sent, so the result rests on ids or items and wants the final check.
    pub(crate) leafed: bool,
    pub(crate) rounds: u32,
    pub(crate) cold_at: usize,
    frames: Vec<Frame>,
    top: usize,
    bounds: Bounds,
    out: Out,
    sc: Scratch,
    hdr: Vec<u8>,
    pub(crate) here: Arena,
    pub(crate) there: Arena,
}

impl Core {
    pub(crate) fn new(lim: Limits, init: bool) -> Self {
        let m = lim.max_item;
        let buf = || Vec::with_capacity(m);
        Self {
            lim,
            n: 0,
            init,
            exact: false,
            leafed: false,
            rounds: 0,
            cold_at: 0,
            frames: Vec::new(),
            top: 0,
            bounds: Bounds {
                lo: buf(),
                hi: buf(),
                inf: true,
                last: buf(),
                snap: buf(),
            },
            out: Out {
                body: Vec::new(),
                stage: Vec::new(),
                last: buf(),
                snap: buf(),
                cap: lim.cap(),
            },
            sc: Scratch {
                p: vec![0; m],
                q: vec![0; m],
                l: buf(),
                r: buf(),
            },
            hdr: Vec::with_capacity(m + 2 * varint::MAX_LEN),
            here: Arena::default(),
            there: Arena::default(),
        }
    }

    /// Forget the previous session.
    pub(crate) fn clear(&mut self) {
        self.exact = false;
        self.leafed = false;
        self.rounds = 0;
        self.cold_at = 0;
        self.top = 0;
        self.here.data.clear();
        self.here.n = 0;
        self.there.data.clear();
        self.there.n = 0;
    }

    /// Count a round against the limit.
    pub(crate) fn round<E>(&mut self) -> Result<(), Error<E>> {
        self.rounds += 1;
        if self.rounds > self.lim.max_rounds {
            Err(Error::TooManyRounds)
        } else {
            Ok(())
        }
    }

    /// The longest message body: the parts up to the message limit, plus what frames them (two bounds, the part
    /// count, and in the first message the set reference and the item count).
    fn frame_cap(&self) -> usize {
        self.out.cap + 2 * self.lim.max_item + 4 * varint::MAX_LEN
    }

    /// The body of a received message.
    pub(crate) fn body<'m, E>(&self, msg: &'m [u8]) -> Result<&'m [u8], Error<E>> {
        let body = frame_body(msg)?;
        if body.len() > self.frame_cap() {
            Err(Error::MessageTooLarge)
        } else {
            Ok(body)
        }
    }

    /// Frame `hdr`, the part count and the built body into `out`.
    fn finish<E>(&mut self, out: &mut Vec<u8>, with_header: bool, cnt: usize, more: bool) -> Result<(), Error<E>> {
        out.clear();
        out.extend_from_slice(&[0; 3]);
        if with_header {
            out.extend_from_slice(&self.hdr);
        }
        put_parts(out, cnt, more)?;
        out.extend_from_slice(&self.out.body);
        let head = frame_header(out.len() - 3).ok_or(Error::MessageTooLarge)?;
        if out.len() - 3 > self.frame_cap() {
            return Err(Error::MessageTooLarge);
        }
        out.get_mut(..3).ok_or(Error::MessageTooLarge)?.copy_from_slice(&head);
        Ok(())
    }

    /// The empty message: it ends the exchange, or tells a peer that holds more to go on.
    pub(crate) fn end_msg<E>(&mut self, out: &mut Vec<u8>) -> Result<(), Error<E>> {
        self.out.reset();
        self.finish(out, false, 0, false)
    }

    /// The root parts of the initiator: one leaf for a small set, else a 16-way split.
    fn root<I: ItemIndex>(&mut self, idx: &I) -> Result<usize, Error<I::Error>> {
        self.out.reset();
        let (out, sc, n) = (&mut self.out, &mut self.sc, self.n);
        if n <= ALEAF && leaf_ok(sc, idx, out.cap, (&[], None), (0, n, self.exact))? {
            self.leafed = true;
            if self.exact {
                items_part(out, sc, idx, tag::FULL, &[], None, (0, n))?;
            } else {
                ids_part(out, sc, idx, &[], None, 0, n)?;
            }
            Ok(1)
        } else {
            split_fit(out, sc, idx, (&[], None), (0, n), 0)
        }
    }

    /// The first message of the initiator, for the set named `set_ref`.
    pub(crate) fn start<I: ItemIndex>(
        &mut self,
        idx: &I,
        set_ref: &[u8],
        out: &mut Vec<u8>,
    ) -> Result<(), Error<I::Error>> {
        if set_ref.len() > self.lim.max_item {
            return Err(Error::ItemTooLarge);
        }
        self.clear();
        self.n = idx.count().map_err(Error::Index)?;
        self.hdr.clear();
        put_varint(&mut self.hdr, set_ref.len())?;
        self.hdr.extend_from_slice(set_ref);
        put_varint(&mut self.hdr, self.n)?;
        let cnt = self.root(idx)?;
        self.finish(out, true, cnt, false)
    }

    /// Restart the reconciliation from the root with items in place of ids, after the final check disagreed.
    pub(crate) fn restart_exact<I: ItemIndex>(&mut self, idx: &I, out: &mut Vec<u8>) -> Result<(), Error<I::Error>> {
        self.exact = true;
        self.leafed = false;
        self.top = 0;
        self.here.data.clear();
        self.here.n = 0;
        self.there.data.clear();
        self.there.n = 0;
        let cnt = self.root(idx)?;
        self.finish(out, false, cnt, false)
    }

    /// The final check: the fingerprint the responder's whole set must have if the reported difference is exact.
    pub(crate) fn check_msg<I: ItemIndex>(&mut self, idx: &I, out: &mut Vec<u8>) -> Result<(), Error<I::Error>> {
        let mut fp = idx.fingerprint(0, self.n).map_err(Error::Index)?;
        for arena in [&self.here, &self.there] {
            let mut rest = arena.data.as_slice();
            while let Ok((len, used)) = varint::decode(rest) {
                let item = usize::try_from(len).ok().and_then(|l| rest.get(used..used + l));
                let Some(item) = item else { break };
                fp ^= Fingerprint::of_item(item);
                rest = rest.get(used + item.len()..).unwrap_or_default();
            }
        }
        self.out.reset();
        self.out.head(tag::CHECK, &[], None)?;
        self.out.body.extend_from_slice(&fp.to_bytes());
        self.finish(out, false, 1, false)
    }

    /// Begin streaming the whole list from its first item.
    pub(crate) fn begin_cold(&mut self) {
        self.cold_at = 0;
        self.sc.l.clear();
    }

    /// Whether the responder streams its whole list, given the initiator's item count and the responder's.
    pub(crate) fn is_cold(na: u64, nb: usize) -> bool {
        nb <= ALEAF || na.saturating_mul(crate::wire::COLD_RATIO) < nb as u64
    }

    /// The next chunk of the whole list, as a cold part; returns whether it was the last.
    pub(crate) fn cold_chunk<I: ItemIndex>(&mut self, idx: &I, out: &mut Vec<u8>) -> Result<bool, Error<I::Error>> {
        let (n, i) = (self.n, self.cold_at);
        let budget = self.out.cap.min(1 << 20);
        // The part's own bytes besides the items: the count, the lower bound, and an upper bound that is a prefix of
        // an item at most one byte longer than the longest in the chunk.
        let fixed = 2 * varint::MAX_LEN + bound_len(self.sc.l.len());
        self.out.reset();
        let (mut j, mut longest) = (i, 0);
        while j < n {
            let len = read(idx, j, &mut self.sc.p)?;
            longest = longest.max(len);
            if j > i && self.out.stage.len() + len + varint::MAX_LEN + fixed + bound_len(longest + 1) > budget {
                break;
            }
            let item = self.sc.p.get(..len).unwrap_or_default();
            self.out.stage_item(item)?;
            j += 1;
        }
        let last = j >= n;
        if last {
            self.out.head(tag::COLD, &self.sc.l, None)?;
        } else {
            let pl = read(idx, j - 1, &mut self.sc.p)?;
            let ql = read(idx, j, &mut self.sc.q)?;
            let (p, q) = (
                self.sc.p.get(..pl).unwrap_or_default(),
                self.sc.q.get(..ql).unwrap_or_default(),
            );
            let sep = q.get(..common_prefix(p, q) + 1).ok_or(Error::BadIndex)?;
            self.sc.r.clear();
            self.sc.r.extend_from_slice(sep);
            self.out.head(tag::COLD, &self.sc.l, Some(&self.sc.r))?;
        }
        mem::swap(&mut self.sc.l, &mut self.sc.r);
        put_varint(&mut self.out.body, j - i)?;
        let stage = mem::take(&mut self.out.stage);
        self.out.body.extend_from_slice(&stage);
        self.out.stage = stage;
        self.cold_at = j;
        self.finish(out, false, 1, false)?;
        Ok(last)
    }

    /// Process the `nparts` parts of the message `body`, read by `r`, and build the reply parts; parts that do not fit
    /// the reply are kept in a frame and resumed in a later turn, after the newer input.
    pub(crate) fn turn<I: ItemIndex>(
        &mut self,
        idx: &I,
        body: &[u8],
        r: &mut Reader<'_>,
        nparts: usize,
    ) -> Result<Answer, Error<I::Error>> {
        self.out.reset();
        self.bounds.last.clear();
        let mut ans = Answer::default();
        let stop = self.answer(idx, r, nparts, &mut ans)?;
        if stop.left > 0 {
            self.push_frame(body.get(stop.at..).unwrap_or_default(), stop.left)?;
        } else if !r.is_empty() {
            return Err(Reason::Frame.into());
        }
        while self.top > 0 && self.out.body.len() < self.out.cap {
            if !self.resume(idx, &mut ans)? {
                break;
            }
        }
        Ok(ans)
    }

    /// Whether parts of received messages are still held, so that the reply is not the whole answer.
    pub(crate) const fn holds(&self) -> bool {
        self.top > 0
    }

    fn push_frame<E>(&mut self, rest: &[u8], left: usize) -> Result<(), Error<E>> {
        if self.top >= MAX_NEST {
            return Err(Error::TooManyRounds);
        }
        if self.top == self.frames.len() {
            self.frames.push(Frame::default());
        }
        let f = self.frames.get_mut(self.top).ok_or(Reason::State)?;
        f.buf.clear();
        f.buf.extend_from_slice(rest);
        f.off = 0;
        f.left = left;
        f.last.clear();
        f.last.extend_from_slice(&self.bounds.last);
        self.top += 1;
        Ok(())
    }

    /// Continue the newest frame until it is done or the reply is full; returns whether it advanced.
    fn resume<I: ItemIndex>(&mut self, idx: &I, ans: &mut Answer) -> Result<bool, Error<I::Error>> {
        let slot = self.top - 1;
        let mut f = mem::take(self.frames.get_mut(slot).ok_or(Reason::State)?);
        self.bounds.last.clear();
        self.bounds.last.extend_from_slice(&f.last);
        let mut r = Reader::new(f.buf.get(f.off..).unwrap_or_default());
        let res = self.answer(idx, &mut r, f.left, ans);
        let done = r.is_empty();
        let res = match res {
            Ok(stop) if stop.left == 0 && !done => Err(Reason::Frame.into()),
            Ok(stop) if stop.left == 0 => {
                self.top = slot;
                Ok(true)
            }
            Ok(stop) => {
                let advanced = stop.left < f.left;
                f.off += stop.at;
                f.left = stop.left;
                f.last.clear();
                f.last.extend_from_slice(&self.bounds.last);
                Ok(advanced)
            }
            Err(e) => Err(e),
        };
        if let Some(s) = self.frames.get_mut(slot) {
            *s = f;
        }
        res
    }

    /// Process parts from `r` into the reply until one does not fit; the parts from there on are left unprocessed.
    #[allow(clippy::too_many_lines, reason = "one match over the part kinds, each arm a rule")]
    fn answer<I: ItemIndex>(
        &mut self,
        idx: &I,
        r: &mut Reader<'_>,
        nparts: usize,
        ans: &mut Answer,
    ) -> Result<Stop, Error<I::Error>> {
        let Self {
            lim,
            n,
            init,
            exact,
            leafed,
            bounds,
            out,
            sc,
            here,
            there,
            ..
        } = self;
        let (n, init, max_item) = (*n, *init, lim.max_item);
        for i in 0..nparts {
            let (at, cnt0, mark) = (r.position(), ans.cnt, out.mark());
            bounds.snap.clear();
            bounds.snap.extend_from_slice(&bounds.last);
            let t = r.read_u8().map_err(|_| Reason::Truncated)?;
            let kind = t & !tag::INF;
            bounds.read(r, t & tag::INF != 0, max_item)?;
            let a = rank(idx, &bounds.lo)?;
            let b = if bounds.inf { n } else { rank(idx, &bounds.hi)? };
            if b < a {
                return Err(Reason::Bound.into());
            }
            let (lo, hi) = (bounds.lo.as_slice(), bounds.hi());
            match kind {
                tag::FP => {
                    let fp = Fingerprint::from_bytes(r.read_array::<FP_LEN>().map_err(|_| Reason::Truncated)?);
                    if idx.fingerprint(a, b).map_err(Error::Index)? != fp {
                        let items = !init || *exact;
                        let leaf = if init { ALEAF } else { BLEAF };
                        if b - a <= leaf && leaf_ok(sc, idx, out.cap, (lo, hi), (a, b, items))? {
                            if init {
                                *leafed = true;
                            }
                            if items {
                                items_part(out, sc, idx, tag::FULL, lo, hi, (a, b))?;
                            } else {
                                ids_part(out, sc, idx, lo, hi, a, b)?;
                            }
                            ans.cnt += 1;
                        } else {
                            ans.cnt += split_fit(out, sc, idx, (lo, hi), (a, b), mark)?;
                        }
                    }
                }
                tag::IDS if !init => {
                    let c = count(r)?;
                    if c > ALEAF {
                        return Err(Reason::Count.into());
                    }
                    let ids = r.read_bytes(c * ID_LEN).map_err(|_| Reason::Truncated)?;
                    if b - a > ALEAF || !leaf_ok(sc, idx, out.cap, (lo, hi), (a, b, true))? {
                        // Too much of ours to list as extras: narrow the range and let the peer ask again.
                        ans.cnt += split_fit(out, sc, idx, (lo, hi), (a, b), mark)?;
                    } else {
                        let mut seen = [0u8; ALEAF / 8];
                        let mut extra = 0usize;
                        for j in a..b {
                            let len = read(idx, j, &mut sc.p)?;
                            let item = sc.p.get(..len).unwrap_or_default();
                            let id = item_id(item);
                            if let Some(k) = ids.as_chunks::<ID_LEN>().0.iter().rposition(|x| *x == id) {
                                if let Some(byte) = seen.get_mut(k >> 3) {
                                    *byte |= 1 << (k & 7);
                                }
                            } else {
                                out.stage_item(item)?;
                                extra += 1;
                            }
                        }
                        reply(out, lo, hi, c, &seen, extra)?;
                        ans.cnt += 1;
                    }
                }
                tag::FULL if !init => {
                    let mut theirs = Items::read(r, max_item)?;
                    let c = theirs.left();
                    if c > ALEAF {
                        return Err(Reason::Count.into());
                    }
                    if b - a > ALEAF || !leaf_ok(sc, idx, out.cap, (lo, hi), (a, b, true))? {
                        while theirs.next_item()?.is_some() {}
                        ans.cnt += split_fit(out, sc, idx, (lo, hi), (a, b), mark)?;
                    } else {
                        let mut seen = [0u8; ALEAF / 8];
                        let mut extra = 0usize;
                        merge(idx, sc, a, b, &mut theirs, |m| match m {
                            Cmp::Both(k) => {
                                if let Some(byte) = seen.get_mut(k >> 3) {
                                    *byte |= 1 << (k & 7);
                                }
                                Ok(())
                            }
                            Cmp::Theirs(_) => Ok(()),
                            Cmp::Mine(item) => {
                                extra += 1;
                                out.stage_item(item)
                            }
                        })?;
                        reply(out, lo, hi, c, &seen, extra)?;
                        ans.cnt += 1;
                    }
                }
                tag::FULL | tag::COLD if init => {
                    let mut theirs = Items::read(r, max_item)?;
                    let cap = lim.max_report;
                    merge(idx, sc, a, b, &mut theirs, |m| match m {
                        Cmp::Both(_) => Ok(()),
                        Cmp::Theirs(item) => push(here, there.data.len(), cap, item),
                        Cmp::Mine(item) => push(there, here.data.len(), cap, item),
                    })?;
                    if kind == tag::COLD {
                        ans.cold = true;
                        ans.cold_end = bounds.inf;
                    }
                }
                tag::REPLY if init => {
                    let c = count(r)?;
                    if c != b - a || c > ALEAF {
                        return Err(Reason::Count.into());
                    }
                    let seen = r.read_bytes(c.div_ceil(8)).map_err(|_| Reason::Truncated)?;
                    // The bits past the count are zero, so the bitmap has one encoding.
                    if c % 8 != 0 && seen.last().is_some_and(|byte| byte >> (c % 8) != 0) {
                        return Err(Reason::Count.into());
                    }
                    for j in 0..c {
                        let bit = seen.get(j >> 3).is_some_and(|byte| byte >> (j & 7) & 1 == 1);
                        if !bit {
                            let len = read(idx, a + j, &mut sc.p)?;
                            push(
                                there,
                                here.data.len(),
                                lim.max_report,
                                sc.p.get(..len).unwrap_or_default(),
                            )?;
                        }
                    }
                    let mut extras = Items::read(r, max_item)?;
                    while let Some(item) = extras.next_item()? {
                        push(here, there.data.len(), lim.max_report, item)?;
                    }
                }
                tag::CHECK if !init => {
                    let fp = Fingerprint::from_bytes(r.read_array::<FP_LEN>().map_err(|_| Reason::Truncated)?);
                    if !lo.is_empty() || !bounds.inf {
                        return Err(Reason::Bound.into());
                    }
                    if idx.fingerprint(0, n).map_err(Error::Index)? != fp {
                        out.head(tag::MISS, &[], None)?;
                        ans.cnt += 1;
                    }
                }
                tag::MISS if init => {
                    if !lo.is_empty() || !bounds.inf {
                        return Err(Reason::Bound.into());
                    }
                    ans.miss = true;
                }
                _ => return Err(Reason::Tag.into()),
            }
            if out.body.len() > out.cap {
                if mark == 0 {
                    return Err(Error::MessageTooLarge);
                }
                out.rollback(mark);
                mem::swap(&mut bounds.last, &mut bounds.snap);
                ans.cnt = cnt0;
                return Ok(Stop { left: nparts - i, at });
            }
        }
        Ok(Stop { left: 0, at: 0 })
    }

    /// Frame the reply built by [`turn`](Self::turn).
    pub(crate) fn reply<E>(&mut self, out: &mut Vec<u8>, cnt: usize, more: bool) -> Result<(), Error<E>> {
        self.finish(out, false, cnt, more)
    }
}

/// A reply part: `venc(c)`, the bitmap of the asker's items we have, then the staged extra items.
fn reply<E>(out: &mut Out, lo: &[u8], hi: Option<&[u8]>, c: usize, seen: &[u8], extra: usize) -> Result<(), Error<E>> {
    out.head(tag::REPLY, lo, hi)?;
    put_varint(&mut out.body, c)?;
    out.body
        .extend_from_slice(seen.get(..c.div_ceil(8)).unwrap_or_default());
    put_varint(&mut out.body, extra)?;
    let stage = mem::take(&mut out.stage);
    out.body.extend_from_slice(&stage);
    out.stage = stage;
    out.stage.clear();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_rollback_to_the_start_of_a_message_reads_nothing_an_earlier_message_left() {
        let mut out = Out {
            body: Vec::new(),
            stage: Vec::new(),
            last: Vec::new(),
            snap: Vec::new(),
            cap: 64,
        };
        // An earlier message wrote a bound and marked its end.
        out.last.extend_from_slice(b"earlier");
        let _ = out.mark();
        // The next message starts and rolls back to its start without a mark of its own, as the root's split does.
        out.reset();
        out.body.extend_from_slice(b"part");
        out.rollback(0);
        assert_eq!(out.body, [] as [u8; 0]);
        assert_eq!(
            out.last,
            [] as [u8; 0],
            "the last bound came back from the earlier message"
        );
    }
}
