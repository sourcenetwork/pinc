//! The response source: a stream's bytes derived from the store at the moment a packet is built.
//!
//! GHOST_FLIGHT. A response is never buffered. [`ValueSource`] is the transport's `StreamSource` for one request:
//! given a stream offset it rebuilds the bytes there, so a packet build and a retransmission both read the store
//! again. A header comes from the [`Plan`], a proof pair from the store's outboard, group bytes from the store's value.
//!
//! # Invariants
//!
//! - Nothing is allocated and nothing is held but a window of at most [`SERVE_BATCH`] frame descriptors (the serve
//!   batch): the frames around the last read, refilled by one `O(depth log n)` lookup when a read leaves the window.
//! - `read_at` returns fewer bytes than asked only at the end of the response or when the store no longer has the
//!   bytes; the transport turns the latter into a data-unavailable error and a reset.
//! - The bytes at an offset are a pure function of the plan and the store, so a retransmission equals the original.

use vinc_transport::stream::StreamSource;

use crate::knobs::SERVE_BATCH;
use crate::plan::{Frame, Plan};
use crate::store::ValueRead;
use crate::wire::{GROUP_HDR, GroupHeader};

/// A response stream's source over a read-only store handle.
#[derive(Debug, Clone)]
pub struct ValueSource<H: ValueRead> {
    store: H,
    root: [u8; 32],
    plan: Plan,
    window: [Option<Frame>; SERVE_BATCH],
}

impl<H: ValueRead> ValueSource<H> {
    /// A source of the response `plan` for the value `root` in `store`.
    pub const fn new(store: H, root: [u8; 32], plan: Plan) -> Self {
        Self {
            store,
            root,
            plan,
            window: [None; SERVE_BATCH],
        }
    }

    /// The plan of the response.
    pub const fn plan(&self) -> &Plan {
        &self.plan
    }

    fn cached(&self, at: u64) -> Option<Frame> {
        self.window
            .iter()
            .flatten()
            .find(|f| f.start <= at && at < f.end())
            .copied()
    }

    /// The frame holding `at`, refilling the window of up to [`SERVE_BATCH`] frames from it when it is outside.
    fn frame_at(&mut self, at: u64) -> Option<Frame> {
        if let Some(f) = self.cached(at) {
            return Some(f);
        }
        let first = self.plan.locate(at)?;
        self.window = [None; SERVE_BATCH];
        for (slot, k) in self.window.iter_mut().zip(first.k..) {
            *slot = self.plan.frame(first.range, k);
            if slot.is_none() {
                break;
            }
        }
        Some(first)
    }

    /// Fill `dst` from the part of `f` at stream offset `at`; returns the bytes written and the bytes the part held
    /// for it (fewer written than held means the store no longer has them).
    fn fill(&self, f: &Frame, at: u64, dst: &mut [u8]) -> (usize, usize) {
        let rel = at - f.start;
        if at < f.proof_start() {
            let hdr = GroupHeader {
                off: f.off,
                len: f.dlen,
                plen: u16::try_from(f.plen).unwrap_or(u16::MAX),
                follows: f.follows,
            }
            .encode();
            let from = usize::try_from(rel).unwrap_or(GROUP_HDR);
            let src = hdr.get(from..).unwrap_or_default();
            let n = src.len().min(dst.len());
            return (copy(dst, src.get(..n).unwrap_or_default()), n);
        }
        if at < f.data_start() {
            let into = at - f.proof_start();
            let (pair, within) = (into / 64, into % 64);
            let room = usize::try_from(64 - within).unwrap_or(0).min(dst.len());
            let (Some(base), Some(out)) = (self.plan.proof_pair(f, pair), dst.get_mut(..room)) else {
                return (0, room);
            };
            return (self.store.read_outboard(&self.root, base + within, out), room);
        }
        let into = at - f.data_start();
        let left = u64::from(f.dlen) - into;
        let room = usize::try_from(left).map_or(dst.len(), |l| l.min(dst.len()));
        let Some(out) = dst.get_mut(..room) else {
            return (0, room);
        };
        (self.store.read_at(&self.root, f.off + into, out), room)
    }
}

fn copy(dst: &mut [u8], src: &[u8]) -> usize {
    dst.get_mut(..src.len()).map_or(0, |d| {
        d.copy_from_slice(src);
        src.len()
    })
}

impl<H: ValueRead> StreamSource for ValueSource<H> {
    fn read_at(&mut self, offset: u64, dst: &mut [u8]) -> usize {
        let (mut at, mut done) = (offset, 0usize);
        while done < dst.len() {
            let Some(f) = self.frame_at(at) else { break };
            let Some(rest) = dst.get_mut(done..) else { break };
            let (n, wanted) = self.fill(&f, at, rest);
            done += n;
            at += n as u64;
            if n < wanted {
                break;
            }
        }
        done
    }
}
