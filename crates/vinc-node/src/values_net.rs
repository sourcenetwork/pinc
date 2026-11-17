//! The tables of the values layer: its streams, found by a node-wide number or by session and stream, and the provider
//! table that numbers the peers the layer talks to.
//!
//! Invariants: every table is bounded by [`TABLE_MAX`]. A provider number is a slot of the provider table and means one
//! peer for as long as any holder (a running fetch, a stream of the layer) holds a use of it; the last use given back
//! frees the slot, and a free slot is reused before the table grows, so the table is bounded by the providers in use,
//! not by the node's history. A stream gives back its use of its provider at the one place it is forgotten
//! ([`Net::drop_stream`]), a fetch at the one place it ends ([`Net::end_fetch`]).

use alloc::collections::{BTreeMap, VecDeque};
use alloc::vec::Vec;

use vinc_core::SessionId;
use vinc_membership::NodeId;
use vinc_transport::stream::StreamId;
use vinc_values::session::Provider;

use crate::config::TABLE_MAX;
use crate::values_frames::AHEAD_RUNS;
use crate::values_provide::Provided;
use crate::values_types::ValuesError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Owner {
    Fetch(u32),
    Serve,
}

/// A stream of the values protocol and the bytes the value layer has not released.
#[derive(Debug)]
pub(crate) struct VStream {
    pub(crate) session: SessionId,
    pub(crate) stream: StreamId,
    pub(crate) owner: Owner,
    /// The provider number of the stream's peer; the stream holds one use of it.
    prov: Provider,
    /// The absolute stream offset up to which the layer released the bytes.
    pub(crate) base: u64,
    /// The end of the contiguous bytes last reported to the fetch.
    pub(crate) seen: u64,
    /// The runs of bytes beyond a hole last reported to the fetch.
    pub(crate) ahead: [(u64, u64); AHEAD_RUNS],
    /// A consume found the end arrived and every byte consumed (the endpoint may forget the stream at that moment).
    pub(crate) ended: bool,
    pub(crate) announced: bool,
    /// For a served response: what the server was last told about its sending.
    pub(crate) pace: Pace,
}

/// What the server was last told of a response it serves.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Pace {
    pub(crate) sent: u64,
    pub(crate) lost: Option<u64>,
}

/// A used slot of the provider table: the peer and how many holders use its number.
#[derive(Debug, Clone, Copy)]
struct Slot {
    peer: NodeId,
    uses: u32,
}

/// The streams of the layer, found by a node-wide number (the value layer's stream handle) or by session and stream,
/// and the provider table.
#[derive(Debug, Default)]
pub(crate) struct Net {
    pub(crate) streams: BTreeMap<u64, VStream>,
    pub(crate) by_real: BTreeMap<(SessionId, StreamId), u64>,
    next: u64,
    /// The provider table: a provider number is an index; `None` is a free slot.
    provs: Vec<Option<Slot>>,
    /// The providers each running fetch holds, given back when it ends.
    held: BTreeMap<u32, Vec<Provider>>,
    /// Fetches refused because the provider table was full.
    refused: u64,
    pub(crate) served: VecDeque<u64>,
    pub(crate) provided: Provided,
}

/// The id for a new fetch after `last`: not 0 (the server's trace tag) and not the id of a fetch for which `running`
/// is true. At most as many steps as there are running fetches plus two.
pub(crate) fn next_fetch_id(last: u32, running: impl Fn(u32) -> bool) -> u32 {
    let mut id = last;
    loop {
        id = id.wrapping_add(1);
        if id != 0 && !running(id) {
            return id;
        }
    }
}

impl Net {
    fn slot_of(&self, peer: &NodeId) -> Option<usize> {
        self.provs.iter().position(|s| s.is_some_and(|s| s.peer == *peer))
    }

    /// The provider number of `peer`, with one more use taken, or `None` if the table is full: [`TABLE_MAX`] peers
    /// are in use and `peer` is not one of them. The number of a peer already in use is the one it has; otherwise the
    /// first free slot is taken, and the table grows only when none is free. The table never holds more than the
    /// providers in use (each use is given back by [`Net::release`]) and a scan finds a peer or a free slot in at most
    /// [`TABLE_MAX`] steps.
    pub(crate) fn acquire(&mut self, peer: &NodeId) -> Option<Provider> {
        let i = match self
            .slot_of(peer)
            .or_else(|| self.provs.iter().position(Option::is_none))
        {
            Some(i) => i,
            None if self.provs.len() < TABLE_MAX => {
                self.provs.push(None);
                self.provs.len() - 1
            }
            None => return None,
        };
        let number = u32::try_from(i).ok()?;
        let slot = self.provs.get_mut(i)?;
        let uses = slot.map_or(0, |s| s.uses);
        *slot = Some(Slot {
            peer: *peer,
            uses: uses.saturating_add(1),
        });
        Some(Provider(number))
    }

    /// The number of `peer` if it is in use, without taking a use.
    pub(crate) fn lookup(&self, peer: &NodeId) -> Option<Provider> {
        self.slot_of(peer).and_then(|i| u32::try_from(i).ok()).map(Provider)
    }

    /// The peer of a number in use.
    pub(crate) fn peer_of(&self, p: Provider) -> Option<NodeId> {
        self.provs.get(p.0 as usize)?.as_ref().map(|s| s.peer)
    }

    /// Take one more use of a number already in use; `None` if the number is free.
    fn hold(&mut self, p: Provider) -> Option<Provider> {
        let s = self.provs.get_mut(p.0 as usize)?.as_mut()?;
        s.uses = s.uses.saturating_add(1);
        Some(p)
    }

    /// Give back one use of `p`. The last use frees the slot, and the free slots at the end leave the table.
    pub(crate) fn release(&mut self, p: Provider) {
        let Some(slot) = self.provs.get_mut(p.0 as usize) else {
            return;
        };
        if let Some(s) = slot.as_mut() {
            s.uses = s.uses.saturating_sub(1);
            if s.uses == 0 {
                *slot = None;
            }
        }
        while self.provs.last().is_some_and(Option::is_none) {
            self.provs.pop();
        }
    }

    pub(crate) fn release_all(&mut self, ps: &[Provider]) {
        for p in ps {
            self.release(*p);
        }
    }

    /// How many providers are in use.
    pub(crate) fn in_use(&self) -> usize {
        self.provs.iter().flatten().count()
    }

    /// How many fetches the provider table refused.
    pub(crate) const fn refused(&self) -> u64 {
        self.refused
    }

    /// Take a use of every peer of a fetch, or of none: when the table is full the uses already taken are given back,
    /// the refusal is counted and the error says so.
    pub(crate) fn acquire_all(&mut self, peers: &[NodeId]) -> Result<Vec<Provider>, ValuesError> {
        let mut got = Vec::with_capacity(peers.len());
        for peer in peers {
            let Some(p) = self.acquire(peer) else {
                self.release_all(&got);
                self.refused = self.refused.saturating_add(1);
                return Err(ValuesError::Providers);
            };
            got.push(p);
        }
        Ok(got)
    }

    /// A fetch started and holds `provs`: they are given back by [`Net::end_fetch`]. The id is not one of a running
    /// fetch ([`next_fetch_id`]); were it, both lists would be kept and given back together, never one early.
    pub(crate) fn begin_fetch(&mut self, fetch: u32, provs: Vec<Provider>) {
        let held = self.held.entry(fetch).or_default();
        debug_assert!(held.is_empty(), "a fetch id was handed out while the fetch was running");
        held.extend(provs);
    }

    /// A fetch ended (finished, failed or cancelled): give back what it holds.
    pub(crate) fn end_fetch(&mut self, fetch: u32) {
        if let Some(provs) = self.held.remove(&fetch) {
            self.release_all(&provs);
        }
    }

    /// A stream of the peer `prov` stands for, which takes over one use of it. With the stream table full the use is
    /// given back and `None` returned.
    pub(crate) fn add(&mut self, session: SessionId, stream: StreamId, owner: Owner, prov: Provider) -> Option<u64> {
        if self.streams.len() >= TABLE_MAX {
            self.release(prov);
            return None;
        }
        self.next += 1;
        let lid = self.next;
        self.streams.insert(
            lid,
            VStream {
                session,
                stream,
                owner,
                prov,
                base: 0,
                seen: 0,
                ahead: [(0, 0); AHEAD_RUNS],
                ended: false,
                announced: false,
                pace: Pace::default(),
            },
        );
        self.by_real.insert((session, stream), lid);
        Some(lid)
    }

    /// Like [`Net::add`] for a stream of a provider that is in use and stays so: the stream takes a use of its own.
    pub(crate) fn add_for(
        &mut self,
        session: SessionId,
        stream: StreamId,
        owner: Owner,
        prov: Provider,
    ) -> Option<u64> {
        let prov = self.hold(prov)?;
        self.add(session, stream, owner, prov)
    }

    /// Forget a stream and give back its use of its provider.
    pub(crate) fn drop_stream(&mut self, lid: u64) -> Option<VStream> {
        let s = self.streams.remove(&lid)?;
        self.by_real.remove(&(s.session, s.stream));
        self.served.retain(|x| *x != lid);
        self.release(s.prov);
        Some(s)
    }

    pub(crate) fn of_session(&self, session: SessionId) -> Vec<u64> {
        self.streams
            .iter()
            .filter(|(_, s)| s.session == session)
            .map(|(lid, _)| *lid)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::unwrap_used,
        clippy::indexing_slicing,
        clippy::cast_possible_truncation,
        reason = "tests assert"
    )]

    use alloc::vec;
    use alloc::vec::Vec;

    use proptest::prelude::*;

    use super::*;

    fn peer(n: u32) -> NodeId {
        let mut id = [0u8; 32];
        id[..4].copy_from_slice(&n.to_le_bytes());
        id
    }

    #[test]
    fn fetching_in_turn_from_more_providers_than_the_table_holds_never_runs_out() {
        let mut net = Net::default();
        for n in 0..TABLE_MAX as u32 + 64 {
            let provs = net.acquire_all(&[peer(n)]).unwrap();
            net.begin_fetch(1, provs);
            net.end_fetch(1);
        }
        assert_eq!(net.in_use(), 0);
        assert!(net.provs.is_empty());
        assert_eq!(net.refused(), 0);
    }

    #[test]
    fn a_freed_slot_is_reused_before_the_table_grows_and_the_others_keep_their_numbers() {
        let mut net = Net::default();
        let a = net.acquire(&peer(1)).unwrap();
        let b = net.acquire(&peer(2)).unwrap();
        let c = net.acquire(&peer(3)).unwrap();
        net.release(a);
        let d = net.acquire(&peer(4)).unwrap();
        assert_eq!(d, a);
        assert_eq!(net.provs.len(), 3);
        assert_eq!(
            [net.peer_of(b), net.peer_of(c), net.peer_of(d)],
            [Some(peer(2)), Some(peer(3)), Some(peer(4))]
        );
        assert_eq!(net.acquire(&peer(2)), Some(b));
    }

    #[test]
    fn a_number_is_free_only_after_every_holder_gave_it_back() {
        let mut net = Net::default();
        let a = net.acquire(&peer(1)).unwrap();
        assert_eq!(net.acquire(&peer(1)), Some(a));
        net.release(a);
        assert_eq!(net.peer_of(a), Some(peer(1)));
        assert_eq!(net.lookup(&peer(1)), Some(a));
        net.release(a);
        assert_eq!(net.peer_of(a), None);
        assert_eq!(net.lookup(&peer(1)), None);
    }

    #[test]
    fn a_full_table_refuses_a_fetch_whole_and_counts_it() {
        let mut net = Net::default();
        let held: Vec<Provider> = (0..TABLE_MAX as u32).map(|n| net.acquire(&peer(n)).unwrap()).collect();
        assert_eq!(net.acquire_all(&[peer(TABLE_MAX as u32)]), Err(ValuesError::Providers));
        assert_eq!(net.refused(), 1);
        // A peer already in use goes first and takes a use; the refusal gives it back.
        assert_eq!(
            net.acquire_all(&[peer(0), peer(TABLE_MAX as u32 + 1)]),
            Err(ValuesError::Providers)
        );
        assert_eq!(net.refused(), 2);
        net.release(held[0]);
        assert_eq!(net.peer_of(held[0]), None, "the refusal left no use of the first peer");
        assert_eq!(net.in_use(), TABLE_MAX - 1);
        // One slot is free now: the same fetch is served and takes it.
        assert_eq!(net.acquire_all(&[peer(TABLE_MAX as u32)]).unwrap(), vec![held[0]]);
        assert_eq!(net.refused(), 2);
    }

    #[test]
    fn a_fetch_id_after_the_wrap_is_neither_zero_nor_one_that_is_running() {
        assert_eq!(next_fetch_id(7, |_| false), 8);
        assert_eq!(next_fetch_id(u32::MAX, |_| false), 1);
        assert_eq!(next_fetch_id(u32::MAX, |id| id == 1), 2);
        assert_eq!(next_fetch_id(u32::MAX - 1, |id| id == u32::MAX || id == 1), 2);
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "handed out while the fetch was running")]
    fn a_running_fetchs_id_is_never_begun_again() {
        let mut net = Net::default();
        let a = net.acquire(&peer(1)).unwrap();
        net.begin_fetch(1, vec![a]);
        let b = net.acquire(&peer(2)).unwrap();
        net.begin_fetch(1, vec![b]);
    }

    #[test]
    fn the_refusal_reads_as_the_provider_limit() {
        assert_eq!(
            alloc::format!("{}", ValuesError::Providers),
            "this node is at its provider limit"
        );
    }

    #[derive(Debug, Clone, Copy)]
    enum Op {
        Open(usize),
        Hold(usize),
        Close(usize),
    }

    fn ops() -> impl Strategy<Value = Vec<Op>> {
        prop::collection::vec(
            (0u8..3, 0usize..24).prop_map(|(k, i)| match k {
                0 => Op::Open(i),
                1 => Op::Hold(i),
                _ => Op::Close(i),
            }),
            0..300,
        )
    }

    proptest! {
        #[test]
        fn the_table_holds_exactly_the_peers_in_use_and_a_number_in_use_keeps_its_peer(ops in ops()) {
            let mut net = Net::default();
            // The holders in flight: the number each was given and the peer it was given for.
            let mut holders: Vec<(Provider, u32)> = Vec::new();
            for op in ops {
                match op {
                    Op::Open(i) => {
                        let n = u32::try_from(i).unwrap();
                        let p = net.acquire(&peer(n)).unwrap();
                        holders.push((p, n));
                    }
                    Op::Hold(i) => {
                        if let Some((p, n)) = holders.get(i % holders.len().max(1)).copied() {
                            prop_assert_eq!(net.hold(p), Some(p));
                            holders.push((p, n));
                        }
                    }
                    Op::Close(i) => {
                        if !holders.is_empty() {
                            let (p, _) = holders.swap_remove(i % holders.len());
                            net.release(p);
                        }
                    }
                }
                prop_assert!(net.in_use() <= holders.len());
                prop_assert!(net.provs.last().is_none_or(Option::is_some));
                let mut peers: Vec<u32> = holders.iter().map(|h| h.1).collect();
                peers.sort_unstable();
                peers.dedup();
                prop_assert_eq!(net.in_use(), peers.len(), "a peer nothing uses is in the table, or one in use is missing");
                for (p, n) in &holders {
                    prop_assert_eq!(net.peer_of(*p), Some(peer(*n)));
                    prop_assert_eq!(net.lookup(&peer(*n)), Some(*p));
                    let uses = holders.iter().filter(|h| h.0 == *p).count();
                    prop_assert_eq!(net.provs[p.0 as usize].map(|s| s.uses as usize), Some(uses));
                }
            }
            for (p, _) in holders {
                net.release(p);
            }
            prop_assert!(net.provs.is_empty());
        }
    }
}
