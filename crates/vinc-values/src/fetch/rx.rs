//! The receive state of one request stream: framing and verification of the response, byte by byte.
//!
//! [`Rx::pump`] consumes the pieces the session holds for the stream, in order, without copying them: the 16-byte
//! GROUP header goes through a 16-byte stash, the proof pairs and the group bytes go straight into the
//! [`GroupVerifier`]. It stops after every completed frame so the fetcher can write the group to the store and release
//! the pieces. Anything that does not match the request (a wrong offset, a wrong length, a proof that does not fit the
//! tree, a hash mismatch, bytes after the last range) is reported as the provider's fault.
//!
//! Invariants: `pos` is the absolute stream offset of the first byte not yet fed; the verifier is at an item boundary
//! whenever the phase is `Header`; a group is reported matched only when its hash matched, and is reported unmatched
//! (skipped, not hashed) only when the store already verified exactly its bytes.

use vinc_transport::stream::StreamId;

use crate::knobs::{GROUP, GROUP_LOG};
use crate::plan::Plan;
use crate::store::ValueStore;
use crate::trace::LiarWhy;
use crate::verify::{GroupVerifier, Item};
use crate::wire::{GROUP_HDR, GroupHeader};

#[derive(Debug, Clone, Copy)]
enum Phase {
    Header,
    Proof { left: u32 },
    Data { left: u32, skip: bool },
}

/// What a [`Rx::pump`] call found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Pump {
    /// All the bytes given were consumed.
    More,
    /// A frame completed.
    Frame {
        /// The group's value offset.
        off: u64,
        /// The group's length.
        len: u64,
        /// The stream offset of the group bytes.
        data_start: u64,
        /// True if the group hashed correctly and is yet to be stored; false if it was skipped as already stored.
        matched: bool,
    },
    /// The provider broke the rules.
    Bad(LiarWhy),
}

/// The state of one request stream.
#[derive(Debug, Clone)]
pub(super) struct Rx {
    pub(super) provider: usize,
    pub(super) stream: StreamId,
    pub(super) plan: Plan,
    /// The absolute stream offset of the first byte not yet fed to the parser.
    pub(super) pos: u64,
    /// The highest value offset range proofs were asked for.
    pub(super) preq_to: u64,
    ver: Option<GroupVerifier>,
    range: usize,
    k: u64,
    phase: Phase,
    hdr: [u8; GROUP_HDR],
    hdr_n: usize,
    cur: Option<GroupHeader>,
    data_start: u64,
}

impl Rx {
    pub(super) fn new(provider: usize, stream: StreamId, plan: Plan, root: &[u8; 32]) -> Self {
        let mut rx = Self {
            provider,
            stream,
            plan,
            pos: 0,
            preq_to: 0,
            ver: None,
            range: 0,
            k: 0,
            phase: Phase::Header,
            hdr: [0; GROUP_HDR],
            hdr_n: 0,
            cur: None,
            data_start: 0,
        };
        rx.ver = rx.verifier_for(0, root);
        rx
    }

    fn verifier_for(&self, range: usize, root: &[u8; 32]) -> Option<GroupVerifier> {
        let span = self.plan.range_span(range)?;
        GroupVerifier::new(*root, self.plan.value_len(), GROUP_LOG, &(span.off..span.end())).ok()
    }

    /// The value offset of the next in-order group.
    pub(super) fn next_off(&self) -> u64 {
        self.plan
            .range_span(self.range)
            .map_or(u64::MAX, |s| s.off + self.k * GROUP)
    }

    /// Feed `piece`; returns the bytes taken and what was found. Stops after the first completed frame or fault.
    pub(super) fn pump<St: ValueStore>(&mut self, st: &St, root: &[u8; 32], piece: &[u8]) -> (usize, Pump) {
        let mut i = 0;
        while i < piece.len() {
            let Some(rest) = piece.get(i..) else { break };
            let step = match self.phase {
                Phase::Header => self.header(rest, st, root),
                Phase::Proof { left } => self.proof(left, rest, st, root),
                Phase::Data { left, skip } => self.data(left, skip, rest, root),
            };
            match step {
                Ok((n, None)) => i += n,
                Ok((n, Some(done))) => return (i + n, done),
                Err(why) => return (i, Pump::Bad(why)),
            }
        }
        (i, Pump::More)
    }

    fn header<St: ValueStore>(
        &mut self,
        rest: &[u8],
        st: &St,
        root: &[u8; 32],
    ) -> Result<(usize, Option<Pump>), LiarWhy> {
        if self.ver.is_none() {
            return Err(LiarWhy::Protocol);
        }
        let take = rest.len().min(GROUP_HDR - self.hdr_n);
        let dst = self
            .hdr
            .get_mut(self.hdr_n..self.hdr_n + take)
            .ok_or(LiarWhy::Protocol)?;
        dst.copy_from_slice(rest.get(..take).ok_or(LiarWhy::Protocol)?);
        self.hdr_n += take;
        self.pos += take as u64;
        if self.hdr_n < GROUP_HDR {
            return Ok((take, None));
        }
        let h = GroupHeader::parse(&self.hdr).map_err(|_| LiarWhy::Protocol)?;
        let span = self.plan.range_span(self.range).ok_or(LiarWhy::Protocol)?;
        let off = span.off + self.k * GROUP;
        let want = (span.end() - off).min(GROUP);
        if h.off != off || u64::from(h.len) != want || h.follows != (self.k > 0) {
            return Err(LiarWhy::Protocol);
        }
        self.cur = Some(h);
        self.phase = Phase::Proof {
            left: u32::from(h.plen),
        };
        if h.plen == 0 {
            self.enter_data(st, root)?;
        }
        Ok((take, None))
    }

    fn proof<St: ValueStore>(
        &mut self,
        left: u32,
        rest: &[u8],
        st: &St,
        root: &[u8; 32],
    ) -> Result<(usize, Option<Pump>), LiarWhy> {
        let ver = self.ver.as_mut().ok_or(LiarWhy::Protocol)?;
        if ver.next_item() != Some(Item::Pair) {
            return Err(LiarWhy::Protocol);
        }
        let take = rest.len().min(usize::try_from(left).unwrap_or(usize::MAX));
        let fed = ver
            .feed(rest.get(..take).ok_or(LiarWhy::Protocol)?)
            .map_err(|_| LiarWhy::Hash)?;
        self.pos += fed.consumed as u64;
        let left = left - u32::try_from(fed.consumed).map_err(|_| LiarWhy::Protocol)?;
        self.phase = Phase::Proof { left };
        if left == 0 {
            self.enter_data(st, root)?;
        }
        Ok((fed.consumed, None))
    }

    /// The proof is fully fed: the verifier must now wait for exactly this frame's group.
    fn enter_data<St: ValueStore>(&mut self, st: &St, root: &[u8; 32]) -> Result<(), LiarWhy> {
        let h = self.cur.ok_or(LiarWhy::Protocol)?;
        let ver = self.ver.as_mut().ok_or(LiarWhy::Protocol)?;
        let want = Item::Group {
            offset: h.off,
            len: u64::from(h.len),
        };
        if ver.next_item() != Some(want) || !ver.at_boundary() {
            return Err(LiarWhy::Protocol);
        }
        let stored = st
            .verified_from(root, h.off)
            .is_some_and(|v| v.start <= h.off && v.end >= h.off + u64::from(h.len));
        if stored {
            ver.skip_group().map_err(|_| LiarWhy::Protocol)?;
        }
        self.data_start = self.pos;
        self.phase = Phase::Data {
            left: h.len,
            skip: stored,
        };
        Ok(())
    }

    fn data(&mut self, left: u32, skip: bool, rest: &[u8], root: &[u8; 32]) -> Result<(usize, Option<Pump>), LiarWhy> {
        let take = rest.len().min(usize::try_from(left).unwrap_or(usize::MAX));
        if !skip {
            let ver = self.ver.as_mut().ok_or(LiarWhy::Protocol)?;
            let fed = ver
                .feed(rest.get(..take).ok_or(LiarWhy::Protocol)?)
                .map_err(|_| LiarWhy::Hash)?;
            if fed.consumed != take {
                return Err(LiarWhy::Protocol);
            }
        }
        self.pos += take as u64;
        let left = left - u32::try_from(take).map_err(|_| LiarWhy::Protocol)?;
        if left > 0 {
            self.phase = Phase::Data { left, skip };
            return Ok((take, None));
        }
        let h = self.cur.take().ok_or(LiarWhy::Protocol)?;
        self.phase = Phase::Header;
        self.hdr_n = 0;
        self.k += 1;
        if Some(self.k) == self.plan.range_groups(self.range) {
            self.range += 1;
            self.k = 0;
            self.ver = self.verifier_for(self.range, root);
        }
        Ok((
            take,
            Some(Pump::Frame {
                off: h.off,
                len: u64::from(h.len),
                data_start: self.data_start,
                matched: !skip,
            }),
        ))
    }
}
