//! Replay floors: how a restarted member tells messages it already delivered from messages it never saw.
//!
//! A hub remembers the newest timestamp it ever sent to each member (`REPLAY_FLOOR`) and, per origin, the newest of
//! each origin's messages (`ORIGIN_FLOOR`), and reports them in the FLOOR frame when the member attaches. A member
//! gathers the floors of every hub for up to [`FLOOR_WAIT`]. Until it has them, a message cannot be told apart from
//! one the previous life already delivered, so it is held (`FLOOR_HOLD`). A floor reported by the hubs decides, never
//! the local clock (`FLOOR_AUTH`), and an origin is judged only against its own floor. A member believes the floors
//! of its hubs (a hub that reports a floor ahead of every clock silences a restarted member until the floor passes),
//! and a malformed FLOOR frame is refused whole. A node no hub ever sent to
//! skips the local-clock rule (`FRESH_KEEP`).
//!
//! Invariants: every table is bounded and a full one only makes the hub report a conservative floor (the present
//! time, no per-origin list); held messages are at most [`FHOLD_MAX`]; a held message is offered again exactly once,
//! when the floors are known or the wait ran out.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use pinc_membership::{Nanos, NodeId};
use pinc_wire::hlc::Hlc;

use crate::consts::{FHOLD_MAX, FLOOR_WAIT, ORIGIN_MAX, TABLE_MAX};
use crate::event::{HoldWhy, Reject, Trace};
use crate::host::Host;
use crate::node::{Held, Topics};
use crate::wire::{TS_LEN, get_ts, put_ts};

/// The marker that follows the history byte of a FLOOR body: no per-origin list.
const NO_LIST: u8 = 0;
/// The marker of a per-origin list: `1 n (origin8 ts12)*n`.
const LIST: u8 = 1;
/// The bytes of one entry of the per-origin list.
const ENTRY_LEN: usize = 8 + TS_LEN;

/// The first eight bytes of a node id: the key of a per-origin floor.
pub(crate) type OriginKey = [u8; 8];

pub(crate) fn origin_key(origin: &NodeId) -> OriginKey {
    origin.first_chunk::<8>().copied().unwrap_or([0; 8])
}

/// What a hub has sent to each member: the newest timestamp overall and per origin.
#[derive(Debug, Default)]
pub(crate) struct SentFloors {
    maxsent: BTreeMap<NodeId, Hlc>,
    ms_over: bool,
    osent: BTreeMap<NodeId, BTreeMap<OriginKey, Hlc>>,
    o_over: bool,
    /// The newest timestamp noted for any member: a full table reports a floor not below it.
    top: Hlc,
}

impl SentFloors {
    /// Record that a message of `origin` published at `ts` went to `p`.
    pub(crate) fn note(&mut self, p: &NodeId, ts: Hlc, origin: &NodeId) {
        self.top = self.top.max(ts);
        if !self.o_over {
            if !self.osent.contains_key(p) && self.osent.len() >= TABLE_MAX {
                self.o_over = true;
            } else {
                let d = self.osent.entry(*p).or_default();
                let o = origin_key(origin);
                if d.contains_key(&o) || d.len() < ORIGIN_MAX {
                    let v = d.entry(o).or_insert(ts);
                    *v = (*v).max(ts);
                } else {
                    self.o_over = true;
                }
            }
        }
        if self.maxsent.contains_key(p) || self.maxsent.len() < TABLE_MAX {
            let v = self.maxsent.entry(*p).or_insert(ts);
            *v = (*v).max(ts);
        } else {
            self.ms_over = true;
        }
    }

    /// Write the FLOOR body for `peer`: `floor12 hist1 [1 n (origin8 ts12)*n | 0]`.
    fn write(&self, peer: &NodeId, present: Hlc, born: Hlc, out: &mut Vec<u8>) {
        let known = self.maxsent.get(peer);
        let floor = if self.ms_over {
            // The hub's clock does not follow an origin stamped far ahead of it, so the present alone could fall
            // below a timestamp the hub already sent.
            present.max(self.top)
        } else {
            known.copied().unwrap_or_default().max(born)
        };
        put_ts(out, floor);
        out.push(u8::from(self.ms_over || known.is_some()));
        if self.o_over || self.ms_over {
            out.push(NO_LIST);
            return;
        }
        let empty = BTreeMap::new();
        let d = self.osent.get(peer).unwrap_or(&empty);
        out.push(LIST);
        out.push(u8::try_from(d.len()).unwrap_or(u8::MAX));
        for (o, ts) in d.iter().take(ORIGIN_MAX) {
            out.extend_from_slice(o);
            put_ts(out, *ts);
        }
    }
}

/// The floor, the history flag and the per-origin list of a FLOOR frame.
type ParsedFloor = (Hlc, bool, Option<BTreeMap<OriginKey, Hlc>>);

/// A FLOOR frame's floor, its history flag and its per-origin list, if the frame is exactly one that
/// [`SentFloors::write`] writes behind an empty topic: the timestamp, a history byte of 0 or 1, then a bare no-list
/// marker, or the list with exactly its count of ascending entries (at most [`ORIGIN_MAX`]), and nothing after.
/// Anything else is `None`, so a frame is taken only if it re-encodes to the same bytes.
fn parse_floor(topic: &[u8], rest: &[u8]) -> Option<ParsedFloor> {
    if !topic.is_empty() {
        return None;
    }
    let f = get_ts(rest)?;
    let (&hist, list) = rest.get(TS_LEN..)?.split_first()?;
    if hist > 1 {
        return None;
    }
    let od = match list {
        [NO_LIST] => None,
        [LIST, n, entries @ ..] if usize::from(*n) <= ORIGIN_MAX && entries.len() == usize::from(*n) * ENTRY_LEN => {
            let keys = entries
                .as_chunks::<ENTRY_LEN>()
                .0
                .iter()
                .filter_map(|e| e.first_chunk::<8>());
            if !keys.is_sorted_by(|a, b| a < b) {
                return None;
            }
            entries
                .as_chunks::<ENTRY_LEN>()
                .0
                .iter()
                .map(|e| Some((*e.first_chunk::<8>()?, get_ts(e.get(8..)?)?)))
                .collect::<Option<BTreeMap<_, _>>>()
        }
        _ => return None,
    };
    Some((f, hist == 1, od))
}

/// Where the floor gathering stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Phase {
    /// A hub never gathers.
    Never,
    /// Waiting for the hubs' floors.
    Gathering,
    /// Done.
    Done,
}

/// A member's view of the hub floors.
#[derive(Debug)]
pub(crate) struct Gather {
    pub(crate) phase: Phase,
    fl: BTreeMap<NodeId, Hlc>,
    ofl: BTreeMap<NodeId, Option<BTreeMap<OriginKey, Hlc>>>,
    /// No hub ever sent to this node id.
    pub(crate) nohist: bool,
    fhist: bool,
    /// Messages published at or before this were delivered by an earlier life.
    pub(crate) rfloor: Option<Hlc>,
    pub(crate) ofloor: Option<BTreeMap<OriginKey, Hlc>>,
    pub(crate) fhold: Vec<Held>,
}

impl Gather {
    pub(crate) fn new(is_hub: bool) -> Self {
        Self {
            phase: if is_hub { Phase::Never } else { Phase::Gathering },
            fl: BTreeMap::new(),
            ofl: BTreeMap::new(),
            nohist: false,
            fhist: false,
            rfloor: None,
            ofloor: None,
            fhold: Vec::new(),
        }
    }

    pub(crate) fn gathering(&self) -> bool {
        self.phase == Phase::Gathering
    }
}

impl Topics {
    /// Write the body of the FLOOR frame for a member that has just attached; returns its length (0 for a node that
    /// is not a hub).
    pub fn floor(&mut self, member: &NodeId, out: &mut [u8]) -> usize {
        if !self.is_hub {
            return 0;
        }
        let mut body = self.take_buf();
        self.sent
            .write(member, self.hlc, Hlc::new(self.born_wall, 0), &mut body);
        let n = body.len().min(out.len());
        if let (Some(d), Some(s)) = (out.get_mut(..n), body.get(..n)) {
            d.copy_from_slice(s);
        }
        self.give_buf(body);
        n
    }

    /// A FLOOR frame from `from`: taken only if it is exactly a frame [`Topics::floor`] writes (see [`parse_floor`]),
    /// otherwise refused whole, counted and traced as a frame that did not parse, with nothing recorded for the hub.
    pub(crate) fn on_floor<H: Host>(&mut self, h: &mut H, now: Nanos, from: &NodeId, topic: &[u8], rest: &[u8]) {
        if !self.is_boot(from) || !self.gather.gathering() {
            return;
        }
        let Some((f, hist, od)) = parse_floor(topic, rest) else {
            self.note_reject([0; 8], Reject::BadHead);
            return;
        };
        if hist {
            self.gather.fhist = true;
        }
        self.gather.fl.insert(*from, f);
        self.gather.ofl.insert(*from, od);
        self.trace(|| Trace::FloorReported { hub: *from });
        self.floor_check(h, now);
    }

    /// Settle the floors if every hub reported or the wait ran out, then offer the messages held for them.
    pub(crate) fn floor_check<H: Host>(&mut self, h: &mut H, now: Nanos) {
        if !self.gather.gathering() {
            return;
        }
        self.floor_settle(h, now);
        if !self.gather.gathering() && !self.gather.fhold.is_empty() {
            let held = core::mem::take(&mut self.gather.fhold);
            for e in held {
                self.offer_held(h, now, e);
            }
        }
    }

    fn floor_settle<H: Host>(&mut self, h: &mut H, now: Nanos) {
        if now.saturating_sub(self.born) > FLOOR_WAIT {
            self.gather.phase = Phase::Done;
            self.trace(|| Trace::FloorDone { used: false });
            return;
        }
        if self.hubs.iter().any(|x| !self.gather.fl.contains_key(x)) {
            return;
        }
        self.gather.phase = Phase::Done;
        self.trace(|| Trace::FloorDone { used: true });
        if self.hubs.is_empty() {
            return;
        }
        if !self.gather.fhist {
            self.gather.nohist = true;
        }
        let f = self
            .hubs
            .iter()
            .filter_map(|x| self.gather.fl.get(x))
            .copied()
            .max()
            .unwrap_or_default();
        if self
            .hubs
            .iter()
            .all(|x| matches!(self.gather.ofl.get(x), Some(Some(_))))
        {
            let mut of: BTreeMap<OriginKey, Hlc> = BTreeMap::new();
            for m in self.hubs.iter().filter_map(|x| self.gather.ofl.get(x)).flatten() {
                for (o, v) in m {
                    let e = of.entry(*o).or_insert(*v);
                    *e = (*e).max(*v);
                }
            }
            self.gather.ofloor = Some(of);
        }
        if self.gather.fhist {
            self.gather.rfloor = Some(f);
            self.replay_subscriptions(h, f.wall);
        }
    }

    /// Hold a message until the floors are known, unless it is already held. Returns whether it was taken.
    pub(crate) fn hold_for_floor(
        &mut self,
        mid: [u8; 8],
        origin: &NodeId,
        hop: &NodeId,
        ts: Hlc,
        topic: &[u8],
        body: &[u8],
    ) {
        if self.gather.fhold.len() >= FHOLD_MAX || self.gather.fhold.iter().any(|x| x.mid == mid) {
            return;
        }
        let mut data = self.take_buf();
        if !Self::pack(&mut data, topic, body) {
            self.give_buf(data);
            return;
        }
        self.gather.fhold.push(Held {
            mid,
            origin: *origin,
            hop: *hop,
            ts,
            data,
        });
        self.trace(|| Trace::Held {
            mid,
            why: HoldWhy::Floor,
        });
    }

    /// Whether a message of `origin` stamped `ts` is older than what this node already delivered.
    pub(crate) fn is_old(&self, origin: &NodeId, ts: Hlc) -> bool {
        let g = &self.gather;
        if let Some(of) = &g.ofloor {
            return of.get(&origin_key(origin)).is_some_and(|f| ts <= *f);
        }
        if g.rfloor.is_some_and(|f| ts <= f) {
            return true;
        }
        g.rfloor.is_none() && !g.nohist && ts.wall.saturating_add(crate::consts::OLD_SLACK_MS) < self.born_wall
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing)]
mod tests {
    use alloc::vec;

    use super::*;

    /// A full table reports a floor at or above every timestamp it noted, even one stamped far ahead of the hub's own
    /// clock (which the clock does not follow).
    #[test]
    fn a_full_table_reports_a_floor_not_below_any_noted_timestamp() {
        let mut s = SentFloors::default();
        let origin = [9u8; 32];
        for i in 0..=TABLE_MAX {
            let mut p = [0u8; 32];
            p[..8].copy_from_slice(&(i as u64).to_be_bytes());
            s.note(&p, Hlc::new(1, 0), &origin);
        }
        let ahead = Hlc::new(5_000_000, 3);
        let peer = [7u8; 32];
        s.note(&peer, ahead, &origin);
        assert!(s.ms_over && s.o_over);
        let mut out = Vec::new();
        s.write(&peer, Hlc::new(10, 0), Hlc::new(0, 0), &mut out);
        assert!(get_ts(&out).unwrap() >= ahead);
        assert_eq!(out.get(TS_LEN + 1), Some(&0), "a bare marker, no origin list");
    }

    fn ts_bytes(ts: Hlc) -> Vec<u8> {
        let mut v = Vec::new();
        put_ts(&mut v, ts);
        v
    }

    fn entry(k: u8, wall: u64) -> Vec<u8> {
        let mut v = vec![k; 8];
        put_ts(&mut v, Hlc::new(wall, 0));
        v
    }

    fn body(hist: u8, tail: &[u8]) -> Vec<u8> {
        let mut v = ts_bytes(Hlc::new(5, 1));
        v.push(hist);
        v.extend_from_slice(tail);
        v
    }

    #[test]
    fn every_form_the_encoder_writes_is_taken() {
        let peer = [7u8; 32];
        let mut s = SentFloors::default();
        let mut out = Vec::new();
        s.write(&peer, Hlc::new(10, 0), Hlc::new(3, 0), &mut out);
        let (f, hist, od) = parse_floor(&[], &out).unwrap();
        assert_eq!((f, hist), (Hlc::new(3, 0), false));
        assert_eq!(od, Some(BTreeMap::new()), "an empty list is a list");
        s.note(&peer, Hlc::new(8, 2), &[1u8; 32]);
        s.note(&peer, Hlc::new(9, 0), &[2u8; 32]);
        out.clear();
        s.write(&peer, Hlc::new(10, 0), Hlc::new(3, 0), &mut out);
        let (f, hist, od) = parse_floor(&[], &out).unwrap();
        assert_eq!((f, hist), (Hlc::new(9, 0), true));
        assert_eq!(od.unwrap().len(), 2);
        s.ms_over = true;
        out.clear();
        s.write(&peer, Hlc::new(10, 0), Hlc::new(3, 0), &mut out);
        let (_, hist, od) = parse_floor(&[], &out).unwrap();
        assert!(hist && od.is_none(), "a bare no-list marker");
    }

    #[test]
    fn a_frame_without_a_marker_is_refused() {
        // the encoder always writes the marker: a frame that ends after the history byte is none of its frames
        assert!(parse_floor(&[], &body(0, &[])).is_none());
        assert!(parse_floor(&[], &body(1, &[])).is_none());
        assert_eq!(
            parse_floor(&[], &body(1, &[NO_LIST])),
            Some((Hlc::new(5, 1), true, None))
        );
    }

    #[test]
    fn a_frame_the_encoder_never_writes_is_refused() {
        let two = [entry(1, 4), entry(2, 5)].concat();
        let list = |n: u8, entries: &[u8]| [&[LIST, n][..], entries].concat();
        assert!(parse_floor(&[], &body(1, &list(2, &two))).is_some());
        // a non-empty topic
        assert!(parse_floor(&[0], &body(1, &[NO_LIST])).is_none());
        assert!(parse_floor(b"t", &body(1, &[])).is_none());
        // a history byte of 2
        assert!(parse_floor(&[], &body(2, &[NO_LIST])).is_none());
        // a list with fewer entries than its count, or more
        assert!(parse_floor(&[], &body(1, &list(3, &two))).is_none());
        assert!(parse_floor(&[], &body(1, &list(1, &two))).is_none());
        // a list with trailing bytes, or trailing bytes without a list
        assert!(parse_floor(&[], &body(1, &[list(2, &two), vec![0]].concat())).is_none());
        assert!(parse_floor(&[], &body(1, &[NO_LIST, 0])).is_none());
        assert!(parse_floor(&[], &body(1, &[2])).is_none());
        assert!(parse_floor(&[], &body(1, &[LIST])).is_none());
        // a count the encoder never writes, entries out of order, repeated
        let big = vec![0u8; (ORIGIN_MAX + 1) * ENTRY_LEN];
        assert!(parse_floor(&[], &body(1, &list(u8::try_from(ORIGIN_MAX + 1).unwrap(), &big))).is_none());
        let back = [entry(2, 4), entry(1, 5)].concat();
        assert!(parse_floor(&[], &body(1, &list(2, &back))).is_none());
        let twice = [entry(1, 4), entry(1, 5)].concat();
        assert!(parse_floor(&[], &body(1, &list(2, &twice))).is_none());
        // a truncated timestamp, or none
        assert!(parse_floor(&[], &ts_bytes(Hlc::new(5, 1))).is_none());
        assert!(parse_floor(&[], &ts_bytes(Hlc::new(5, 1))[..11]).is_none());
        assert!(parse_floor(&[], &[]).is_none());
    }
}
