//! WRITE_THROUGH on the receiving side: out-of-order groups verified against range proofs.
//!
//! When bytes of a response arrive beyond a hole, the session holds them and tells the fetch ([`super::In::Ahead`]).
//! The fetch asks the server for range proofs over the region (`PROOF_REQ`), keeps the proofs that arrive (`PROOF`),
//! and as soon as a whole group and a proof covering it are both present it hashes the group where it sits, checks
//! it against the root through the proof's parent pairs, writes it to the store and announces it. When the in-order
//! parse later reaches that group it finds it in the store and skips it without hashing.
//!
//! Invariants: a proof is accepted only if it fits the value (length, group log, whole groups, the exact pair count
//! of its range); a group is written only if it verified, and a failed attempt changes nothing (the in-order parse
//! will judge the bytes). The proof cache is a ring of [`WT_KEEP`] entries for the whole fetch.

use pinc_dag::tree::{Layout, PARENT_LEN, RangeEncoder, Step};
use pinc_transport::frame::ext;
use pinc_transport::stream::StreamId;

use super::{Env, Fetch, State};
use crate::knobs::{GROUP, GROUP_LOG, WT_AHEAD, WT_KEEP, WT_MAX_K, WT_PMAX};
use crate::plan::{Frame, range_pairs};
use crate::session::Session;
use crate::store::ValueStore;
use crate::trace::{LiarWhy, Out, Trace};
use crate::verify::GroupVerifier;
use crate::wire::{PROOF_BODY_MAX, ProofFrame, ProofReq};

/// A kept range proof.
#[derive(Debug, Clone)]
struct ProofEntry {
    stream: StreamId,
    start: u64,
    wn: u64,
    len: usize,
    pairs: [u8; WT_PMAX],
}

/// The ring of range proofs a fetch keeps.
#[derive(Debug, Clone)]
pub(super) struct ProofCache {
    entries: [Option<ProofEntry>; WT_KEEP],
    next: usize,
}

impl ProofCache {
    pub(super) fn new() -> Self {
        Self {
            entries: core::array::from_fn(|_| None),
            next: 0,
        }
    }

    fn insert(&mut self, e: ProofEntry) {
        let same = self
            .entries
            .iter()
            .position(|x| x.as_ref().is_some_and(|x| x.stream == e.stream && x.start == e.start));
        let at = same.unwrap_or_else(|| {
            let n = self.next;
            self.next = (n + 1) % WT_KEEP;
            n
        });
        if let Some(slot) = self.entries.get_mut(at) {
            *slot = Some(e);
        }
    }

    fn covering(&self, stream: StreamId, gs: u64, ge: u64) -> Option<&ProofEntry> {
        self.entries
            .iter()
            .flatten()
            .find(|e| e.stream == stream && e.start <= gs && ge <= e.start + e.wn)
    }
}

impl Fetch {
    /// Bytes arrived beyond a hole of request stream `stream`.
    pub(super) fn on_ahead<E: Env>(&mut self, io: &mut E, now: u64, stream: StreamId, offset: u64, len: u64) {
        let Some(si) = self.rx_index(stream) else { return };
        let Some(rx) = self.rx.get(si).and_then(Option::as_ref) else {
            return;
        };
        if offset < rx.pos {
            return;
        }
        let stop = offset.saturating_add(len);
        let (mut frames, mut vend) = ([None::<Frame>; 8], 0u64);
        let mut at = offset;
        for slot in &mut frames {
            let Some(f) = rx.plan.locate(at) else { break };
            if f.data_start() < stop {
                vend = vend.max(f.off + (stop - f.data_start()).min(u64::from(f.dlen)));
            }
            at = f.end();
            *slot = Some(f);
            if at >= stop {
                break;
            }
        }
        let (vnext, preq) = (rx.next_off(), rx.preq_to);
        if vend > preq {
            let from = preq.max(vnext);
            let upto = vend + WT_AHEAD;
            let mut buf = [0u8; 32];
            let sent = ProofReq {
                sid: stream,
                from,
                upto,
            }
            .encode(&mut buf)
            .ok()
            .and_then(|n| buf.get(..n))
            .is_some_and(|b| io.split().0.send_ext(stream, ext::PROOF_REQ, b));
            if sent && let Some(r) = self.rx.get_mut(si).and_then(Option::as_mut) {
                r.preq_to = upto;
            }
        }
        for f in frames.into_iter().flatten() {
            self.try_ahead(io, now, si, &f);
        }
    }

    /// An extension frame arrived: a range proof is kept and tried against the groups it covers.
    pub(super) fn on_ext<E: Env>(&mut self, io: &mut E, now: u64, ty: u64, body: &[u8]) {
        if ty != ext::PROOF || body.len() > PROOF_BODY_MAX {
            return;
        }
        let Ok(pf) = ProofFrame::parse(body) else { return };
        let Some(si) = self.rx_index(pf.sid) else { return };
        let end = pf.start.saturating_add(u64::from(pf.wn));
        let (a, b) = (pf.start / GROUP, end.div_ceil(GROUP));
        let layout = Layout::new(self.length, GROUP_LOG);
        let fits = u32::from(pf.glog) == GROUP_LOG
            && pf.ln == self.length
            && pf.wn > 0
            && pf.start % GROUP == 0
            && u64::from(pf.wn) <= WT_MAX_K * GROUP
            && end <= self.length
            && layout.is_ok_and(|l| pf.proof.len() as u64 == range_pairs(l.groups(), a, b) * PARENT_LEN as u64);
        if !fits {
            io.split().2.trace(now, Trace::ProofRejected { stream: pf.sid });
            let pi = self.rx.get(si).and_then(Option::as_ref).map(|r| r.provider);
            if let Some(pi) = pi {
                self.evict(io, now, pi, LiarWhy::Protocol);
            }
            return;
        }
        let mut pairs = [0u8; WT_PMAX];
        if let Some(d) = pairs.get_mut(..pf.proof.len()) {
            d.copy_from_slice(pf.proof);
        }
        self.proofs.insert(ProofEntry {
            stream: pf.sid,
            start: pf.start,
            wn: u64::from(pf.wn),
            len: pf.proof.len(),
            pairs,
        });
        for g in a..b {
            if self.state != State::Running {
                return;
            }
            let frame = self
                .rx
                .get(si)
                .and_then(Option::as_ref)
                .and_then(|r| r.plan.frame_of_group(g * GROUP));
            if let Some(f) = frame {
                self.try_ahead(io, now, si, &f);
            }
        }
    }

    /// Verify the group of `f` out of order if its bytes and a covering proof are both here; write it through.
    fn try_ahead<E: Env>(&mut self, io: &mut E, now: u64, si: usize, f: &Frame) {
        let Some(rx) = self.rx.get(si).and_then(Option::as_ref) else {
            return;
        };
        let (stream, pi, pos) = (rx.stream, rx.provider, rx.pos);
        let (gs, ge) = (f.off, f.off + u64::from(f.dlen));
        if f.start < pos {
            return;
        }
        let (se, st, _) = io.split();
        if st
            .verified_from(&self.root, gs)
            .is_some_and(|v| v.start <= gs && v.end >= ge)
        {
            return;
        }
        let Some(entry) = self.proofs.covering(stream, gs, ge) else {
            return;
        };
        if !se.has(stream, f.data_start(), u64::from(f.dlen)) {
            return;
        }
        let Ok(mut ver) = GroupVerifier::new(self.root, self.length, GROUP_LOG, &(gs..ge)) else {
            return;
        };
        let fed = Self::feed_pairs(&mut ver, self.length, entry, gs..ge);
        let mut matched = false;
        let mut left = u64::from(f.dlen);
        if fed {
            se.visit(stream, f.data_start(), |piece| {
                let n = usize::try_from(left).map_or(piece.len(), |l| l.min(piece.len()));
                let Some(head) = piece.get(..n).filter(|h| !h.is_empty()) else {
                    return 0;
                };
                match ver.feed(head) {
                    Ok(r) => {
                        left -= r.consumed as u64;
                        matched = r.group.is_some();
                        r.consumed
                    }
                    Err(_) => 0,
                }
            });
        }
        if !(fed && matched && left == 0) {
            // The proof and the bytes both came from this provider, and together they do not hash to the root.
            io.split().2.trace(now, Trace::ProofRejected { stream });
            self.evict(io, now, pi, LiarWhy::Hash);
            return;
        }
        if self.store_group(io, stream, gs, u64::from(f.dlen), f.data_start()) {
            self.group_verified(io, now, pi, gs, u64::from(f.dlen), true, true);
        } else {
            self.state = State::Done;
            self.drop_all_streams(io);
            io.split()
                .2
                .event(now, crate::trace::Event::Failed(crate::trace::FailReason::Store));
        }
    }

    /// Feed the parent pairs that lead to the group `range` out of the proof `entry` into `ver`, in order.
    fn feed_pairs(ver: &mut GroupVerifier, len: u64, entry: &ProofEntry, range: core::ops::Range<u64>) -> bool {
        let Ok(layout) = Layout::new(len, GROUP_LOG) else {
            return false;
        };
        let (Ok(own), Ok(frame)) = (
            RangeEncoder::new(layout, &range),
            RangeEncoder::new(layout, &(entry.start..entry.start + entry.wn)),
        ) else {
            return false;
        };
        let mut frame_pairs = frame.filter_map(|s| match s {
            Ok(Step::Parent { outboard_offset }) => Some(outboard_offset),
            _ => None,
        });
        let mut rank = 0usize;
        for step in own {
            let Ok(Step::Parent { outboard_offset: want }) = step else {
                continue;
            };
            loop {
                let Some(have) = frame_pairs.next() else { return false };
                rank += 1;
                if have != want {
                    continue;
                }
                let at = (rank - 1) * PARENT_LEN;
                let Some(pair) = entry.pairs.get(..entry.len).and_then(|p| p.get(at..at + PARENT_LEN)) else {
                    return false;
                };
                if ver.feed(pair).is_err() {
                    return false;
                }
                break;
            }
        }
        true
    }
}
