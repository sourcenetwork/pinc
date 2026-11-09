//! The shared engine of the initiator and the responder: message building, part processing, the leaf rules.
//!
//! Invariants: the set is never held; every range, fingerprint and item is re-read from the [`ItemIndex`] when it is
//! needed. All buffers are allocated in `new` from the [`Limits`] and only reused afterwards: bounds and items are
//! checked against `max_item` before they are copied, the message against the message limit as it grows. A part is
//! processed and answered in the order it arrives, so the output depends only on the input messages and the index.

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
    ALEAF, BLEAF, Items, SPLIT, common_prefix, count, frame_body, frame_header, put_bound, put_varint, read_bound, tag,
};

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
    cap: usize,
}

impl Out {
    fn reset(&mut self) {
        self.body.clear();
        self.stage.clear();
        self.last.clear();
    }

    fn check<E>(&self) -> Result<(), Error<E>> {
        if self.body.len() + self.stage.len() > self.cap {
            Err(Error::MessageTooLarge)
        } else {
            Ok(())
        }
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
        self.check()
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

/// Split `a..b` (within `lo..hi`) into [`SPLIT`] fingerprint parts; returns the part count.
fn split<I: ItemIndex>(
    out: &mut Out,
    sc: &mut Scratch,
    idx: &I,
    lo: &[u8],
    hi: Option<&[u8]>,
    a: usize,
    b: usize,
) -> Result<usize, Error<I::Error>> {
    let step = (b - a).div_ceil(SPLIT).max(1);
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
        out.check()?;
        mem::swap(&mut sc.l, &mut sc.r);
        x = y;
    }
    Ok(cnt)
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
    out.check()
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
        out.check()?;
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
                    && sc.q.get(..pl).unwrap_or_default() >= t
                {
                    return Err(Reason::Item.into());
                }
                sc.q.clear();
                sc.q.extend_from_slice(t);
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
            bounds: Bounds {
                lo: buf(),
                hi: buf(),
                inf: true,
                last: buf(),
            },
            out: Out {
                body: Vec::new(),
                stage: Vec::new(),
                last: buf(),
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
    fn finish<E>(&mut self, out: &mut Vec<u8>, with_header: bool, cnt: usize) -> Result<(), Error<E>> {
        out.clear();
        out.extend_from_slice(&[0; 3]);
        if with_header {
            out.extend_from_slice(&self.hdr);
        }
        put_varint(out, cnt)?;
        out.extend_from_slice(&self.out.body);
        let head = frame_header(out.len() - 3).ok_or(Error::MessageTooLarge)?;
        if out.len() - 3 > self.frame_cap() {
            return Err(Error::MessageTooLarge);
        }
        out.get_mut(..3).ok_or(Error::MessageTooLarge)?.copy_from_slice(&head);
        Ok(())
    }

    /// The message that ends the exchange.
    pub(crate) fn end_msg<E>(&mut self, out: &mut Vec<u8>) -> Result<(), Error<E>> {
        self.out.reset();
        self.finish(out, false, 0)
    }

    /// The root parts of the initiator: one leaf for a small set, else a 16-way split.
    fn root<I: ItemIndex>(&mut self, idx: &I) -> Result<usize, Error<I::Error>> {
        self.out.reset();
        let (out, sc, n) = (&mut self.out, &mut self.sc, self.n);
        if n <= ALEAF {
            self.leafed = true;
            if self.exact {
                items_part(out, sc, idx, tag::FULL, &[], None, (0, n))?;
            } else {
                ids_part(out, sc, idx, &[], None, 0, n)?;
            }
            Ok(1)
        } else {
            split(out, sc, idx, &[], None, 0, n)
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
        self.finish(out, true, cnt)
    }

    /// Restart the reconciliation from the root with items in place of ids, after the final check disagreed.
    pub(crate) fn restart_exact<I: ItemIndex>(&mut self, idx: &I, out: &mut Vec<u8>) -> Result<(), Error<I::Error>> {
        self.exact = true;
        self.leafed = false;
        self.here.data.clear();
        self.here.n = 0;
        self.there.data.clear();
        self.there.n = 0;
        let cnt = self.root(idx)?;
        self.finish(out, false, cnt)
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
        self.finish(out, false, 1)
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
        self.out.reset();
        let mut j = i;
        while j < n {
            let len = read(idx, j, &mut self.sc.p)?;
            if j > i && self.out.stage.len() + len + varint::MAX_LEN > budget {
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
        self.finish(out, false, 1)?;
        Ok(last)
    }

    /// Process the `nparts` parts of one message and build the reply parts.
    #[allow(clippy::too_many_lines, reason = "one match over the part kinds, each arm a rule")]
    pub(crate) fn answer<I: ItemIndex>(
        &mut self,
        idx: &I,
        r: &mut Reader<'_>,
        nparts: usize,
    ) -> Result<Answer, Error<I::Error>> {
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
        out.reset();
        bounds.last.clear();
        let mut ans = Answer::default();
        for _ in 0..nparts {
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
                    if idx.fingerprint(a, b).map_err(Error::Index)? == fp {
                        continue;
                    }
                    if init && b - a <= ALEAF {
                        *leafed = true;
                        if *exact {
                            items_part(out, sc, idx, tag::FULL, lo, hi, (a, b))?;
                        } else {
                            ids_part(out, sc, idx, lo, hi, a, b)?;
                        }
                        ans.cnt += 1;
                    } else if !init && b - a <= BLEAF {
                        items_part(out, sc, idx, tag::FULL, lo, hi, (a, b))?;
                        ans.cnt += 1;
                    } else {
                        ans.cnt += split(out, sc, idx, lo, hi, a, b)?;
                    }
                }
                tag::IDS if !init => {
                    let c = count(r)?;
                    if c > ALEAF {
                        return Err(Reason::Count.into());
                    }
                    let ids = r.read_bytes(c * ID_LEN).map_err(|_| Reason::Truncated)?;
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
                tag::FULL if !init => {
                    let mut theirs = Items::read(r, max_item)?;
                    let c = theirs.left();
                    if c > ALEAF {
                        return Err(Reason::Count.into());
                    }
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
            out.check()?;
        }
        Ok(ans)
    }

    /// Frame the reply built by [`answer`](Self::answer).
    pub(crate) fn reply<E>(&mut self, out: &mut Vec<u8>, cnt: usize) -> Result<(), Error<E>> {
        self.finish(out, false, cnt)
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
    out.check()
}
