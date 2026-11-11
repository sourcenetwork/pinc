//! Scheduling: the stripe queue, per-provider targets, the end-game steal, requests and liar eviction.
//!
//! DEADLINE_STRIPE, ARRIVAL_CURVE, TAIL_SHRINK, STEAL and LIAR_EVICT of the reference design, on the fixed tables of
//! [`Fetch`]. Every cut of work is a whole number of groups, so a byte range is never asked of two providers for the
//! sake of a split. Providers are visited in slot order, which is the order the fetch named them.

use super::{ASSIGN, Env, Fetch, MAX_STREAMS, State};
use crate::knobs::{
    GROUP, MAX_REQ_RANGES, MIN_TARGET_GROUPS, MS, OPEN_RETRY, RATE_HORIZON, RATE_WARMUP, STEAL_ETA_MS,
    STEAL_ETA_STALLED_MS, STEAL_IDLE, STEAL_MIN, STRIPE_CHUNK, TGT_MAX, TGT0, URGENCY, code,
};
use crate::plan::Plan;
use crate::session::{Outbound, Session};
use crate::span::{RangeList, Span, holes};
use crate::store::ValueStore;
use crate::trace::{Event, FailReason, LiarWhy, Out, Trace};
use crate::wire::{REQ_MAX, Req};

use super::rx::Rx;

impl Fetch {
    /// Divide the missing bytes among the providers and send the first requests.
    pub(super) fn begin<E: Env>(&mut self, io: &mut E, now: u64, need: &RangeList<{ super::WANT }>) {
        let n = self.nprov;
        if self.striped {
            self.queue.extend(need);
            for p in self.provs.iter_mut().take(n) {
                p.in_assign = true;
            }
            for pi in 0..n {
                self.top_up(io, now, pi);
            }
            return;
        }
        let shares = need.split::<{ crate::knobs::MAX_PROVIDERS }>(n);
        for (pi, share) in shares.iter().enumerate() {
            if share.is_empty() {
                continue;
            }
            if let Some(p) = self.provs.get_mut(pi) {
                p.in_assign = true;
                p.assign.extend(share);
            }
            self.request(io, now, pi, None);
        }
    }

    /// The verified delivery rate of provider `pi` in bytes per millisecond; 0 before 500 ms of samples.
    pub(super) fn prate(&self, pi: usize, now: u64) -> u64 {
        let Some(pt) = self.provs.get(pi).and_then(|p| p.pt.map(|t| (t, p.pb))) else {
            return 0;
        };
        if now.saturating_sub(pt.0) < RATE_WARMUP {
            return 0;
        }
        pt.1 / (now.saturating_sub(pt.0) / MS).max(1)
    }

    /// The outstanding target of provider `pi` (ARRIVAL_CURVE).
    fn target(&self, pi: usize, now: u64) -> u64 {
        let Some(p) = self.provs.get(pi) else { return TGT0 };
        match p.pt {
            Some(pt) if now.saturating_sub(pt) >= RATE_WARMUP => {
                let ms = (now.saturating_sub(pt) / MS).max(1);
                (MIN_TARGET_GROUPS * GROUP).max(TGT_MAX.min(p.pb.saturating_mul(RATE_HORIZON) / ms))
            }
            _ => TGT0,
        }
    }

    fn assigned_count(&self) -> u64 {
        self.provs.iter().filter(|p| p.in_assign).count() as u64
    }

    /// Pop up to `size` bytes from the front of the queue, skipping verified bytes, cut at group boundaries.
    fn take_chunk<St: ValueStore>(&mut self, st: &St, size: u64) -> RangeList<ASSIGN> {
        let mut out = RangeList::new();
        let mut got = 0u64;
        while got < size {
            let Some(s) = self.queue.pop_front() else { break };
            let room = size - got;
            let take = if s.len <= room {
                s.len
            } else {
                Self::group_floor(room).min(s.len)
            };
            if take < s.len {
                self.queue.push_front(Span {
                    off: s.off + take,
                    len: s.len - take,
                });
            }
            holes(st, &self.root, Span { off: s.off, len: take }, |h| {
                out.push(h);
                got += h.len;
            });
        }
        out
    }

    /// DEADLINE_STRIPE: keep provider `pi`'s outstanding work at its target from the offset-ordered queue.
    pub(super) fn top_up<E: Env>(&mut self, io: &mut E, now: u64, pi: usize) {
        if !self.striped || self.state != State::Running {
            return;
        }
        let root = self.root;
        let (_, st, _) = io.split();
        let Some(p) = self.provs.get_mut(pi).filter(|p| p.in_assign) else {
            return;
        };
        p.assign.retain_missing(&*st, &root);
        let (outstanding, conn, id) = (p.assign.total(), p.conn, p.id);
        let tgt = self.target(pi, now);
        if outstanding >= tgt / 2 {
            return;
        }
        let mut want = tgt - outstanding;
        if !self.queue.is_empty() {
            // TAIL_SHRINK: near the end a top-up takes at most a 1/(2k) share of what is left.
            let k = self.assigned_count().max(1);
            let mut left = 0u64;
            for s in self.queue.as_slice() {
                left = left.saturating_add(s.len);
                if left >= 4 * STRIPE_CHUNK * k {
                    break;
                }
            }
            want = want.min((MIN_TARGET_GROUPS * GROUP).max(left / (2 * k)));
        }
        let mut new = if self.queue.is_empty() {
            RangeList::new()
        } else {
            self.take_chunk(&*st, want)
        };
        if new.is_empty() && outstanding == 0 && conn {
            new = self.steal(io, now, pi);
        }
        if new.is_empty() {
            return;
        }
        if let Some(p) = self.provs.get_mut(pi) {
            p.assign.extend(&new);
            // vertexia: the idle clock of a provider that had nothing starts when it is given work, so work just
            // handed over is not stolen back at once; the reference design leaves the stale time of its last granule.
            if outstanding == 0 {
                p.lp = Some(now);
            }
        }
        io.split().2.trace(
            now,
            Trace::TopUp {
                provider: id,
                bytes: new.total(),
                target: tgt,
            },
        );
        self.request(io, now, pi, Some(&new));
    }

    /// STEAL: an idle provider takes the tail of the provider that would finish last, or all of a stalled one.
    fn steal<E: Env>(&mut self, io: &mut E, now: u64, pi: usize) -> RangeList<ASSIGN> {
        let root = self.root;
        let mut best: Option<(usize, u64, u64)> = None;
        for qi in 0..self.nprov {
            if qi == pi {
                continue;
            }
            let rq = self.prate(qi, now);
            let (_, st, _) = io.split();
            let Some(q) = self.provs.get_mut(qi).filter(|q| q.in_assign) else {
                continue;
            };
            q.assign.retain_missing(&*st, &root);
            let m = q.assign.total();
            let idle = now.saturating_sub(q.lp.unwrap_or(self.t0)) >= STEAL_IDLE;
            // vertexia: a provider idle for STEAL_IDLE is robbed whatever it still holds; the reference STEAL_MIN
            // floor would leave the last 256 KiB of a dead provider unfetched forever.
            if m == 0 || (m < STEAL_MIN && !idle) {
                continue;
            }
            let eta = if idle {
                STEAL_ETA_STALLED_MS
            } else if let Some(eta) = m.checked_div(rq) {
                eta
            } else {
                continue;
            };
            if eta >= STEAL_ETA_MS && best.is_none_or(|(_, _, b)| eta > b) {
                best = Some((qi, m, eta));
            }
        }
        let Some((bi, bm, eta)) = best else {
            if self.tw <= now {
                self.tw = now + STEAL_IDLE / 2;
            }
            return RangeList::new();
        };
        let rq = if eta < STEAL_ETA_STALLED_MS {
            self.prate(bi, now)
        } else {
            0
        };
        let rp = match self.prate(pi, now) {
            0 => rq,
            r => r,
        };
        let keep = bm.saturating_mul(rq).checked_div(rq.saturating_add(rp)).unwrap_or(0);
        let keep = keep.div_ceil(GROUP) * GROUP;
        let mut tail: RangeList<ASSIGN> = RangeList::new();
        let mut head: RangeList<ASSIGN> = RangeList::new();
        let mut acc = 0u64;
        if let Some(b) = self.provs.get(bi) {
            for s in b.assign.as_slice() {
                if acc >= keep {
                    tail.push(*s);
                } else if acc + s.len <= keep {
                    head.push(*s);
                } else {
                    head.push(Span {
                        off: s.off,
                        len: keep - acc,
                    });
                    tail.push(Span {
                        off: s.off + keep - acc,
                        len: s.len - (keep - acc),
                    });
                }
                acc += s.len;
            }
        }
        if tail.is_empty() {
            // Rounding `keep` up to a group can leave nothing to move (a thief far slower than the victim); the
            // victim's streams are then left alone, and the steal is looked at again later.
            if self.tw <= now {
                self.tw = now + STEAL_IDLE / 2;
            }
            return RangeList::new();
        }
        let (from, to) = (self.provs.get(bi).map(|p| p.id), self.provs.get(pi).map(|p| p.id));
        if let Some(b) = self.provs.get_mut(bi) {
            b.assign.clear();
            b.assign.extend(&head);
        }
        let (se, _, out) = io.split();
        for slot in &mut self.rx {
            if let Some(r) = slot.as_ref().filter(|r| r.provider == bi) {
                se.reset(r.stream, code::STOLEN);
                *slot = None;
            }
        }
        if let (Some(from), Some(to)) = (from, to) {
            out.trace(
                now,
                Trace::Steal {
                    from,
                    to,
                    bytes: tail.total(),
                },
            );
        }
        self.request(io, now, bi, None);
        tail
    }

    /// Ask provider `pi` for `only`, or for everything it holds if `None`, dialling first if it has no session.
    pub(super) fn request<E: Env>(&mut self, io: &mut E, now: u64, pi: usize, only: Option<&RangeList<ASSIGN>>) {
        let (se, st, _) = io.split();
        let Some(p) = self.provs.get_mut(pi) else { return };
        if !p.conn && se.is_connected(p.id) {
            // The sessions belong to the layer, not to a fetch: one an earlier fetch dialed serves this one too.
            p.conn = true;
            p.dialing = false;
        }
        if !p.conn {
            if !p.dialing {
                p.dialing = true;
                se.dial(p.id);
                let id = p.id;
                io.split().2.trace(now, Trace::Dial(id));
            }
            return;
        }
        let need = only.unwrap_or(&p.assign).missing(&*st, &self.root);
        for chunk in need.as_slice().chunks(MAX_REQ_RANGES) {
            if !self.open_request(io, now, pi, chunk) {
                if let Some(p) = self.provs.get_mut(pi) {
                    p.retry = Some(now + OPEN_RETRY);
                }
                return;
            }
        }
    }

    /// Open a stream to provider `pi` and send a request for `ranges`; false if it could not be sent.
    fn open_request<E: Env>(&mut self, io: &mut E, now: u64, pi: usize, ranges: &[Span]) -> bool {
        let Some(slot) = self.rx.iter().position(Option::is_none).filter(|&i| i < MAX_STREAMS) else {
            return false;
        };
        let Some(id) = self.provs.get(pi).map(|p| p.id) else {
            return false;
        };
        let (se, _, out) = io.split();
        let Ok(plan) = Plan::new(self.length, ranges) else {
            return false;
        };
        let Ok(stream) = se.open_stream(id, URGENCY) else {
            return false;
        };
        let mut buf = [0u8; REQ_MAX];
        let sent = Req::encode(&self.root, ranges, &mut buf)
            .ok()
            .and_then(|n| buf.get(..n))
            .is_some_and(|b| se.write(stream, b, true));
        if !sent {
            se.reset(stream, code::PROTOCOL);
            return false;
        }
        if self.lastb == 0 && self.treq == 0 {
            self.treq = now;
        }
        out.trace(
            now,
            Trace::Requested {
                provider: id,
                stream,
                ranges: u8::try_from(ranges.len()).unwrap_or(u8::MAX),
                bytes: ranges.iter().map(|s| s.len).sum(),
            },
        );
        if let Some(s) = self.rx.get_mut(slot) {
            *s = Some(Rx::new(pi, stream, plan, &self.root));
        }
        true
    }

    /// LIAR_EVICT: provider `pi` sent bytes that failed verification. It is never asked again; its share goes back to
    /// the queue (striped) or is split over the remaining providers.
    pub(super) fn evict<E: Env>(&mut self, io: &mut E, now: u64, pi: usize, why: LiarWhy) {
        let (se, st, out) = io.split();
        let Some(id) = self.provs.get(pi).map(|p| p.id) else {
            return;
        };
        out.trace(now, Trace::Liar { provider: id, why });
        for slot in &mut self.rx {
            if let Some(r) = slot.as_ref().filter(|r| r.provider == pi) {
                se.reset(r.stream, code::LIAR);
                *slot = None;
            }
        }
        let share = self.provs.get_mut(pi).map(|p| {
            p.in_provs = false;
            p.in_assign = false;
            p.retry = None;
            p.lp = None;
            p.pt = None;
            p.pb = 0;
            core::mem::take(&mut p.assign)
        });
        if !self.provs.iter().any(|p| p.in_assign) {
            for p in &mut self.provs {
                p.in_assign = p.in_provs;
            }
        }
        if !self.provs.iter().any(|p| p.in_assign) {
            self.state = State::Done;
            self.drop_all_streams(io);
            io.split().2.event(now, Event::Failed(FailReason::EveryProviderLied));
            return;
        }
        let miss = share.unwrap_or_default().missing(&*st, &self.root);
        let rest = self.rest_providers();
        if self.striped {
            for s in miss.as_slice().iter().rev() {
                self.queue.push_front(*s);
            }
            for r in rest {
                if self.state == State::Running {
                    self.top_up(io, now, r);
                }
            }
            return;
        }
        let shares = miss.split::<{ crate::knobs::MAX_PROVIDERS }>(rest.len().max(1));
        for (r, sh) in rest.into_iter().zip(shares.iter()) {
            if sh.is_empty() {
                continue;
            }
            if let Some(p) = self.provs.get_mut(r) {
                p.assign.extend(sh);
            }
            self.request(io, now, r, Some(sh));
        }
    }

    /// The indices of the providers that hold a share, in slot order.
    fn rest_providers(&self) -> heapless_idx::Idx {
        let mut idx = heapless_idx::Idx::new();
        for (i, p) in self.provs.iter().enumerate() {
            if p.in_assign {
                idx.push(i);
            }
        }
        idx
    }

    /// Reset every request stream still open (the fetch ended).
    pub(super) fn drop_all_streams<E: Env>(&mut self, io: &mut E) {
        let (se, _, _) = io.split();
        for slot in &mut self.rx {
            if let Some(r) = slot.take() {
                se.reset(r.stream, code::CANCELLED);
            }
        }
    }
}

/// A tiny fixed list of provider indices.
mod heapless_idx {
    use crate::knobs::MAX_PROVIDERS;

    #[derive(Debug, Clone, Copy)]
    pub(super) struct Idx {
        items: [usize; MAX_PROVIDERS],
        len: usize,
    }

    impl Idx {
        pub(super) const fn new() -> Self {
            Self {
                items: [0; MAX_PROVIDERS],
                len: 0,
            }
        }

        pub(super) fn push(&mut self, i: usize) {
            if let Some(s) = self.items.get_mut(self.len) {
                *s = i;
                self.len += 1;
            }
        }

        pub(super) const fn len(&self) -> usize {
            self.len
        }
    }

    impl IntoIterator for Idx {
        type Item = usize;
        type IntoIter = core::iter::Take<core::array::IntoIter<usize, MAX_PROVIDERS>>;
        fn into_iter(self) -> Self::IntoIter {
            self.items.into_iter().take(self.len)
        }
    }
}

#[cfg(test)]
mod tests;
