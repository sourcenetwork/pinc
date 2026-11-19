//! The geometry of a response stream, in closed form.
//!
//! A response to a request of up to 255 ranges is, per range, a sequence of GROUP frames: a 16-byte header, the
//! parent pairs the previous group leaves open, then the group bytes. Which stream offset holds which byte of which
//! frame is a pure function of the value length and the ranges, so the server re-reads any byte of a response from
//! the store (no buffering) and the receiver places out-of-order bytes without parsing. Both ends call [`Plan`].
//!
//! # Invariants
//!
//! - The pair count and the position of every frame come from `O(depth)` tree arithmetic over the BLAKE3 tree of
//!   `pinc-dag`, never from walking the groups, so a multi-GiB range costs no more than a small one. The tests check
//!   it against `pinc_dag::tree::encode_range` byte for byte.
//! - Frame starts are strictly increasing, so a stream offset locates its frame by binary search.
//! - Every sum is checked; a plan whose response would pass 2^62 - 1 bytes is refused, so no offset overflows.

use pinc_dag::tree::{Layout, PARENT_LEN, TreeError};

use crate::knobs::{GROUP, GROUP_LOG, MAX_REQ_RANGES};
use crate::span::Span;
use crate::wire::GROUP_HDR;

/// The largest stream offset (2^62 - 1), as in the transport.
const MAX_STREAM: u64 = (1 << 62) - 1;
/// The most tree levels any value has (groups are under 2^54).
const DEPTH: usize = 64;

/// Why a plan was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlanError {
    /// A range runs past the end of the value.
    OutOfBounds,
    /// More than [`MAX_REQ_RANGES`] ranges.
    TooManyRanges,
    /// The response would be longer than a stream can be.
    TooLong,
}

/// The groups in the left subtree of a node of `count >= 2` groups.
const fn left_groups(count: u64) -> u64 {
    match count.checked_sub(1) {
        Some(m) if m > 0 => 1 << m.ilog2(),
        _ => 0,
    }
}

/// The parents of the subtree `[lo, hi)` that intersect the groups `[a, b)`.
fn parents_in(lo: u64, hi: u64, a: u64, b: u64) -> u64 {
    if hi - lo < 2 || b <= lo || hi <= a {
        return 0;
    }
    if a <= lo && hi <= b {
        return hi - lo - 1;
    }
    let mid = lo + left_groups(hi - lo);
    1 + parents_in(lo, mid, a, b) + parents_in(mid, hi, a, b)
}

/// The parents of the subtree `[lo, hi)` that intersect the groups from `s` on.
fn parents_in_suffix(mut lo: u64, mut hi: u64, s: u64) -> u64 {
    let mut sum = 0;
    while hi - lo >= 2 && s < hi {
        if s <= lo {
            return sum + hi - lo - 1;
        }
        let mid = lo + left_groups(hi - lo);
        sum += 1;
        if s < mid {
            sum += hi - mid - 1;
            hi = mid;
        } else {
            lo = mid;
        }
    }
    sum
}

/// The parents, among those intersecting `[a, b)`, that come before the data of group `x` in pre-order.
fn parents_before(n: u64, a: u64, x: u64) -> u64 {
    let (mut lo, mut hi, mut sum) = (0, n, 0);
    while hi - lo >= 2 {
        sum += 1;
        let mid = lo + left_groups(hi - lo);
        if x < mid {
            hi = mid;
        } else {
            sum += parents_in_suffix(lo, mid, a);
            lo = mid;
        }
    }
    sum
}

/// A node on the path from the root to a group.
#[derive(Debug, Clone, Copy, Default)]
struct PathNode {
    lo: u64,
    idx: u64,
}

/// The parent nodes above group `x`, root first; returns how many.
fn path(n: u64, x: u64, out: &mut [PathNode; DEPTH]) -> usize {
    let (mut lo, mut hi, mut idx, mut len) = (0, n, 0, 0);
    while hi - lo >= 2 {
        if let Some(slot) = out.get_mut(len) {
            *slot = PathNode { lo, idx };
            len += 1;
        }
        let left = left_groups(hi - lo);
        let mid = lo + left;
        if x < mid {
            idx += 1;
            hi = mid;
        } else {
            idx += left;
            lo = mid;
        }
    }
    len
}

#[derive(Debug, Clone, Copy, Default)]
struct PlanRange {
    first: u64,
    last: u64,
    start: u64,
}

/// One GROUP frame of a response: where it starts and what it holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Frame {
    /// The index of the range in the plan.
    pub range: usize,
    /// The index of the group within the range.
    pub k: u64,
    /// The stream offset of the header.
    pub start: u64,
    /// The value offset of the group.
    pub off: u64,
    /// The group bytes.
    pub dlen: u32,
    /// The proof bytes.
    pub plen: u32,
    /// Whether the proof continues the previous group of the range.
    pub follows: bool,
}

impl Frame {
    /// The stream offset where the proof starts.
    pub const fn proof_start(&self) -> u64 {
        self.start + GROUP_HDR as u64
    }

    /// The stream offset where the group bytes start.
    pub const fn data_start(&self) -> u64 {
        self.start + GROUP_HDR as u64 + self.plen as u64
    }

    /// The stream offset just past the frame.
    pub const fn end(&self) -> u64 {
        self.data_start() + self.dlen as u64
    }
}

/// The layout of the response to a request: the value geometry and the stream position of every frame.
#[derive(Debug, Clone)]
pub struct Plan {
    layout: Layout,
    count: usize,
    ranges: [PlanRange; MAX_REQ_RANGES],
    total: u64,
}

impl Plan {
    /// The plan for the response to `spans` of a value of `len` bytes. Each span is rounded out to whole groups;
    /// an empty span adds nothing.
    ///
    /// # Errors
    /// [`PlanError`] for a span past the value, too many spans, or a response over 2^62 - 1 bytes.
    pub fn new(len: u64, spans: &[Span]) -> Result<Self, PlanError> {
        if spans.len() > MAX_REQ_RANGES {
            return Err(PlanError::TooManyRanges);
        }
        let layout = Layout::new(len, GROUP_LOG).map_err(|_: TreeError| PlanError::OutOfBounds)?;
        let n = layout.groups();
        let mut plan = Self {
            layout,
            count: 0,
            ranges: [PlanRange::default(); MAX_REQ_RANGES],
            total: 0,
        };
        for s in spans.iter().filter(|s| s.len > 0) {
            let end = s
                .off
                .checked_add(s.len)
                .filter(|&e| e <= len)
                .ok_or(PlanError::OutOfBounds)?;
            let (first, last) = (s.off / GROUP, end.div_ceil(GROUP));
            let data = end.div_ceil(GROUP).saturating_mul(GROUP).min(len) - first * GROUP;
            let size = (last - first)
                .checked_mul(GROUP_HDR as u64)
                .and_then(|h| h.checked_add(data))
                .and_then(|d| d.checked_add(parents_in(0, n, first, last).checked_mul(PARENT_LEN as u64)?))
                .ok_or(PlanError::TooLong)?;
            let total = plan
                .total
                .checked_add(size)
                .filter(|&t| t <= MAX_STREAM)
                .ok_or(PlanError::TooLong)?;
            if let Some(slot) = plan.ranges.get_mut(plan.count) {
                *slot = PlanRange {
                    first,
                    last,
                    start: plan.total,
                };
                plan.count += 1;
            }
            plan.total = total;
        }
        Ok(plan)
    }

    /// The value length.
    pub const fn value_len(&self) -> u64 {
        self.layout.value_len()
    }

    /// The length of the whole response in bytes.
    pub const fn total(&self) -> u64 {
        self.total
    }

    /// The number of non-empty ranges.
    pub const fn ranges(&self) -> usize {
        self.count
    }

    /// The value byte span range `i` covers after rounding to groups.
    pub fn range_span(&self, i: usize) -> Option<Span> {
        let r = self.ranges.get(..self.count)?.get(i)?;
        let off = r.first * GROUP;
        Some(Span {
            off,
            len: r.last.saturating_mul(GROUP).min(self.layout.value_len()) - off,
        })
    }

    /// The groups range `i` holds.
    pub fn range_groups(&self, i: usize) -> Option<u64> {
        let r = self.ranges.get(..self.count)?.get(i)?;
        Some(r.last - r.first)
    }

    fn frame_start(&self, r: &PlanRange, k: u64) -> u64 {
        if k == 0 {
            return r.start;
        }
        let n = self.layout.groups();
        let data = ((r.first + k) * GROUP).min(self.layout.value_len()) - r.first * GROUP;
        r.start + k * GROUP_HDR as u64 + data + PARENT_LEN as u64 * parents_before(n, r.first, r.first + k - 1)
    }

    /// The frame `k` of range `i`.
    #[allow(
        clippy::many_single_char_names,
        reason = "the tree arithmetic uses the names of its derivation"
    )]
    pub fn frame(&self, i: usize, k: u64) -> Option<Frame> {
        let r = self.ranges.get(..self.count)?.get(i)?;
        let x = r.first.checked_add(k).filter(|&x| x < r.last)?;
        let n = self.layout.groups();
        let before = parents_before(n, r.first, x);
        let prev = if k == 0 { 0 } else { parents_before(n, r.first, x - 1) };
        Some(Frame {
            range: i,
            k,
            start: self.frame_start(r, k),
            off: x * GROUP,
            dlen: u32::try_from(self.layout.group_size(x)).ok()?,
            plen: u32::try_from((before - prev) * PARENT_LEN as u64).ok()?,
            follows: k > 0,
        })
    }

    /// The frame that holds stream offset `at`, if the response reaches it.
    pub fn locate(&self, at: u64) -> Option<Frame> {
        if at >= self.total {
            return None;
        }
        let ranges = self.ranges.get(..self.count)?;
        let i = ranges.partition_point(|r| r.start <= at).checked_sub(1)?;
        let r = ranges.get(i)?;
        let (mut lo, mut hi) = (0, r.last - r.first - 1);
        while lo < hi {
            let mid = lo + (hi - lo).div_ceil(2);
            if self.frame_start(r, mid) <= at {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        self.frame(i, lo).filter(|f| at < f.end())
    }

    /// The frame that carries the group at value offset `off` (a multiple of the group size), from the first range
    /// that holds it.
    pub fn frame_of_group(&self, off: u64) -> Option<Frame> {
        if !off.is_multiple_of(GROUP) {
            return None;
        }
        let g = off / GROUP;
        let (i, r) = self
            .ranges
            .get(..self.count)?
            .iter()
            .enumerate()
            .find(|(_, r)| r.first <= g && g < r.last)?;
        self.frame(i, g - r.first)
    }

    /// The outboard byte offset of the `j`-th pair of the proof of `frame`.
    pub fn proof_pair(&self, frame: &Frame, j: u64) -> Option<u64> {
        let r = self.ranges.get(..self.count)?.get(frame.range)?;
        let x = r.first + frame.k;
        let mut nodes = [PathNode::default(); DEPTH];
        let len = path(self.layout.groups(), x, &mut nodes);
        let live = nodes.get(..len)?;
        let at = usize::try_from(j).ok()?;
        let node = if frame.follows {
            live.iter().filter(|p| p.lo == x).nth(at)?
        } else {
            live.get(at)?
        };
        node.idx.checked_mul(PARENT_LEN as u64)
    }
}

/// The parent pairs the range encoding of the groups `[a, b)` of a value with `n` groups holds.
pub fn range_pairs(n: u64, a: u64, b: u64) -> u64 {
    parents_in(0, n, a, b)
}
