//! Replay floors: how a restarted member tells messages it already delivered from messages it never saw.
//!
//! A hub remembers the newest timestamp it ever sent to each member (`REPLAY_FLOOR`) and, per origin, the newest of
//! each origin's messages (`ORIGIN_FLOOR`), and reports them in the FLOOR frame when the member attaches. A member
//! gathers the floors of every hub for up to [`FLOOR_WAIT`]. Until it has them, a message cannot be told apart from
//! one the previous life already delivered, so it is held (`FLOOR_HOLD`). A floor reported by the hubs decides, never
//! the local clock (`FLOOR_AUTH`), and an origin is judged only against its own floor. A node no hub ever sent to
//! skips the local-clock rule (`FRESH_KEEP`).
//!
//! Invariants: every table is bounded and a full one only makes the hub report a conservative floor (the present
//! time, no per-origin list); held messages are at most [`FHOLD_MAX`]; a held message is offered again exactly once,
//! when the floors are known or the wait ran out.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use vinc_membership::{Nanos, NodeId};
use vinc_wire::hlc::Hlc;

use crate::consts::{FHOLD_MAX, FLOOR_WAIT, ORIGIN_MAX, TABLE_MAX};
use crate::event::{HoldWhy, Trace};
use crate::host::Host;
use crate::node::{Held, Topics};
use crate::wire::{TS_LEN, get_ts, put_ts};

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
}

impl SentFloors {
    /// Record that a message of `origin` published at `ts` went to `p`.
    pub(crate) fn note(&mut self, p: &NodeId, ts: Hlc, origin: &NodeId) {
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
            present
        } else {
            known.copied().unwrap_or_default().max(born)
        };
        put_ts(out, floor);
        out.push(u8::from(self.ms_over || known.is_some()));
        if self.o_over || self.ms_over {
            out.push(0);
            return;
        }
        let empty = BTreeMap::new();
        let d = self.osent.get(peer).unwrap_or(&empty);
        out.push(1);
        out.push(u8::try_from(d.len()).unwrap_or(u8::MAX));
        for (o, ts) in d.iter().take(ORIGIN_MAX) {
            out.extend_from_slice(o);
            put_ts(out, *ts);
        }
    }
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

    /// A FLOOR frame from `from`.
    pub(crate) fn on_floor<H: Host>(&mut self, h: &mut H, now: Nanos, from: &NodeId, rest: &[u8]) {
        if !self.is_boot(from) || !self.gather.gathering() {
            return;
        }
        let Some(f) = get_ts(rest) else { return };
        let Some(&hist) = rest.get(TS_LEN) else { return };
        if hist == 1 {
            self.gather.fhist = true;
        }
        let list = rest.get(TS_LEN + 1..).unwrap_or_default();
        let mut od = None;
        if let [1, n, entries @ ..] = list
            && entries.len() >= usize::from(*n) * (8 + TS_LEN)
        {
            let mut m = BTreeMap::new();
            for e in entries.as_chunks::<{ 8 + TS_LEN }>().0.iter().take(usize::from(*n)) {
                if let (Some(k), Some(ts)) = (e.first_chunk::<8>(), e.get(8..).and_then(get_ts)) {
                    m.insert(*k, ts);
                }
            }
            od = Some(m);
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
    pub(crate) fn hold_for_floor(&mut self, mid: [u8; 8], origin: &NodeId, ts: Hlc, topic: &[u8], body: &[u8]) {
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
