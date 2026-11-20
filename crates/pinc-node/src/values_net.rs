//! The tables of the values layer: its streams, found by a node-wide number or by session and stream, and the provider
//! table that numbers the peers the layer talks to.
//!
//! Invariants: every table is bounded by [`TABLE_MAX`]. A provider number is a slot of the provider table and means one
//! peer for as long as any holder (a running fetch, a stream of the layer) holds a use of it; the last use given back
//! frees the slot, and a free slot is reused before the table grows, so the table's length is the most providers in use
//! at once (it never shrinks), at most [`TABLE_MAX`], and not the node's history. Every use is given back in one of five places: [`Net::drop_stream`] for a stream's use
//! (the only way out of the stream tables), [`Net::add`] for the use handed to it when the stream table is full, the
//! rollback in [`Net::acquire_all`] for the uses taken for a fetch the table cannot hold whole, [`Net::end_fetch`] for
//! what a fetch holds when it finishes, fails or is cancelled, and [`Net::release_all`] for the start path of the node
//! when a fetch is refused or already done as it starts (a fetch that never entered the table of running fetches).

use alloc::collections::{BTreeMap, VecDeque};
use alloc::vec::Vec;

use pinc_core::SessionId;
use pinc_membership::NodeId;
use pinc_transport::stream::StreamId;
use pinc_values::session::Provider;

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
    session: SessionId,
    stream: StreamId,
    owner: Owner,
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

impl VStream {
    /// The endpoint's session of the stream.
    pub(crate) const fn session(&self) -> SessionId {
        self.session
    }

    /// The endpoint's id of the stream.
    pub(crate) const fn stream(&self) -> StreamId {
        self.stream
    }

    /// Who the stream belongs to: a fetch or the server.
    pub(crate) const fn owner(&self) -> Owner {
        self.owner
    }
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
    streams: BTreeMap<u64, VStream>,
    by_real: BTreeMap<(SessionId, StreamId), u64>,
    next: u64,
    /// The provider table: a provider number is an index; `None` is a free slot.
    provs: Vec<Option<Slot>>,
    /// The providers each running fetch holds, given back when it ends.
    held: BTreeMap<u32, Vec<Provider>>,
    /// Fetches refused because the provider table was full.
    refused: u64,
    served: VecDeque<u64>,
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
    /// first free slot is taken, and the table grows only when none is free. The table is never longer than the
    /// most providers in use at once (each use is given back by [`Net::release`]; free slots are reused, the table never
    /// shrinks) and a scan finds a peer or a free slot in at most
    /// [`TABLE_MAX`] steps.
    pub(crate) fn acquire(&mut self, peer: &NodeId) -> Option<Provider> {
        let mut free = None;
        let mut found = None;
        for (i, s) in self.provs.iter().enumerate() {
            match s {
                Some(s) if s.peer == *peer => {
                    found = Some(i);
                    break;
                }
                None if free.is_none() => free = Some(i),
                _ => {}
            }
        }
        let i = match found.or(free) {
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

    /// Give back one use of `p`. The last use frees the slot, and the free slots at the end leave the table. A
    /// give-back of a free number (a holder giving back twice) is caught where debug assertions are on; a give-back
    /// that takes a use from a number other holders still use is not.
    pub(crate) fn release(&mut self, p: Provider) {
        match self.provs.get_mut(p.0 as usize) {
            Some(slot @ Some(_)) => {
                if let Some(s) = slot.as_mut() {
                    s.uses = s.uses.saturating_sub(1);
                    if s.uses == 0 {
                        *slot = None;
                    }
                }
            }
            _ => debug_assert!(false, "a provider number was given back that is not in use"),
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
    /// fetch ([`next_fetch_id`] skips them), so no list is replaced; were it, a release build would drop the running
    /// fetch's list without giving it back, and its uses would stay taken.
    pub(crate) fn begin_fetch(&mut self, fetch: u32, provs: Vec<Provider>) {
        debug_assert!(
            !self.held.contains_key(&fetch),
            "a fetch id was handed out while the fetch was running"
        );
        self.held.insert(fetch, provs);
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

    /// The stream with the layer's number `lid`.
    pub(crate) fn stream(&self, lid: u64) -> Option<&VStream> {
        self.streams.get(&lid)
    }

    pub(crate) fn stream_mut(&mut self, lid: u64) -> Option<&mut VStream> {
        self.streams.get_mut(&lid)
    }

    /// The layer's number of the endpoint's stream `stream` of `session`.
    pub(crate) fn lid_of(&self, session: SessionId, stream: StreamId) -> Option<u64> {
        self.by_real.get(&(session, stream)).copied()
    }

    /// The streams `owner` holds.
    pub(crate) fn of_owner(&self, owner: Owner) -> Vec<u64> {
        self.streams
            .iter()
            .filter(|(_, s)| s.owner == owner)
            .map(|(lid, _)| *lid)
            .collect()
    }

    /// The served responses in the order they began.
    pub(crate) const fn served(&self) -> &VecDeque<u64> {
        &self.served
    }

    /// A response began on stream `lid`.
    pub(crate) fn serve_began(&mut self, lid: u64) {
        self.served.push_back(lid);
    }

    /// Stop tracking the served response on `lid`.
    pub(crate) fn served_forget(&mut self, lid: u64) {
        self.served.retain(|x| *x != lid);
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
    #[cfg(debug_assertions)]
    #[should_panic(expected = "given back that is not in use")]
    fn giving_back_a_number_twice_is_caught() {
        let mut net = Net::default();
        let a = net.acquire(&peer(1)).unwrap();
        net.release(a);
        net.release(a);
    }

    #[test]
    fn the_refusal_reads_as_the_provider_limit() {
        assert_eq!(
            alloc::format!("{}", ValuesError::Providers),
            "this node is at its provider limit; retry when a fetch has ended"
        );
    }

    #[test]
    fn a_stream_keeps_its_provider_after_the_fetch_ended_and_frees_it_when_dropped() {
        let mut net = Net::default();
        let provs = net.acquire_all(&[peer(1)]).unwrap();
        let p = provs[0];
        net.begin_fetch(1, provs);
        let lid = net.add_for(SessionId(1), 4, Owner::Fetch(1), p).unwrap();
        net.end_fetch(1);
        assert_eq!(net.peer_of(p), Some(peer(1)), "the stream still names its peer");
        assert_eq!(net.in_use(), 1);
        net.drop_stream(lid);
        assert_eq!(net.in_use(), 0);
        assert!(net.provs.is_empty());
    }

    #[test]
    fn a_full_stream_table_refuses_a_stream_and_gives_its_use_back() {
        let mut net = Net::default();
        for n in 0..TABLE_MAX as u64 {
            let p = net.acquire(&peer(0)).unwrap();
            assert!(net.add(SessionId(1), n, Owner::Serve, p).is_some());
        }
        let p = net.acquire(&peer(1)).unwrap();
        assert_eq!(net.add(SessionId(1), TABLE_MAX as u64, Owner::Serve, p), None);
        assert_eq!(net.peer_of(p), None, "the refused stream left no use of its peer");
        assert_eq!(net.in_use(), 1);
        let p = net.acquire(&peer(0)).unwrap();
        assert_eq!(net.add_for(SessionId(1), TABLE_MAX as u64, Owner::Serve, p), None);
        net.release(p);
        for lid in net.streams.keys().copied().collect::<Vec<_>>() {
            net.drop_stream(lid);
        }
        assert_eq!(net.in_use(), 0);
        assert!(net.provs.is_empty());
    }

    #[derive(Debug, Clone)]
    enum Op {
        Open(usize),
        Hold(usize),
        Close(usize),
        Begin(Vec<u32>),
        End(usize),
        Add(usize),
        AddFor(usize),
        Drop(usize),
    }

    fn ops() -> impl Strategy<Value = Vec<Op>> {
        prop::collection::vec(
            (0u8..8, 0usize..24, prop::collection::vec(0u32..24, 0..5)).prop_map(|(k, i, peers)| match k {
                0 => Op::Open(i),
                1 => Op::Hold(i),
                2 => Op::Close(i),
                3 => Op::Begin(peers),
                4 => Op::End(i),
                5 => Op::Add(i),
                6 => Op::AddFor(i),
                _ => Op::Drop(i),
            }),
            0..300,
        )
    }

    /// Every use a holder has in flight, as the number it was given and the peer it was given for.
    #[derive(Default)]
    struct Model {
        loose: Vec<(Provider, u32)>,
        streams: Vec<(u64, Provider, u32)>,
        fetches: Vec<(u32, Vec<(Provider, u32)>)>,
    }

    impl Model {
        fn all(&self) -> Vec<(Provider, u32)> {
            let streams = self.streams.iter().map(|s| (s.1, s.2));
            let fetches = self.fetches.iter().flat_map(|f| f.1.iter().copied());
            self.loose.iter().copied().chain(streams).chain(fetches).collect()
        }
    }

    proptest! {
        #[test]
        fn the_table_holds_exactly_the_peers_in_use_and_a_number_in_use_keeps_its_peer(ops in ops()) {
            let mut net = Net::default();
            let mut m = Model::default();
            let (mut next_fetch, mut next_stream) = (0u32, 0u64);
            for op in ops {
                match op {
                    Op::Open(i) => {
                        let n = u32::try_from(i).unwrap();
                        m.loose.push((net.acquire(&peer(n)).unwrap(), n));
                    }
                    Op::Hold(i) => {
                        if let Some((p, n)) = m.loose.get(i % m.loose.len().max(1)).copied() {
                            prop_assert_eq!(net.hold(p), Some(p));
                            m.loose.push((p, n));
                        }
                    }
                    Op::Close(i) => {
                        if !m.loose.is_empty() {
                            let (p, _) = m.loose.swap_remove(i % m.loose.len());
                            net.release(p);
                        }
                    }
                    Op::Begin(peers) => {
                        let ids: Vec<NodeId> = peers.iter().map(|n| peer(*n)).collect();
                        let got = net.acquire_all(&ids).unwrap();
                        next_fetch += 1;
                        net.begin_fetch(next_fetch, got.clone());
                        m.fetches.push((next_fetch, got.into_iter().zip(peers).collect()));
                    }
                    Op::End(i) => {
                        if !m.fetches.is_empty() {
                            let (id, _) = m.fetches.swap_remove(i % m.fetches.len());
                            net.end_fetch(id);
                        }
                    }
                    Op::Add(i) => {
                        if !m.loose.is_empty() {
                            let (p, n) = m.loose.swap_remove(i % m.loose.len());
                            next_stream += 1;
                            let lid = net.add(SessionId(1), next_stream, Owner::Serve, p).unwrap();
                            m.streams.push((lid, p, n));
                        }
                    }
                    Op::AddFor(i) => {
                        let all = m.all();
                        if !all.is_empty() {
                            let (p, n) = all[i % all.len()];
                            next_stream += 1;
                            let lid = net.add_for(SessionId(1), next_stream, Owner::Fetch(1), p).unwrap();
                            m.streams.push((lid, p, n));
                        }
                    }
                    Op::Drop(i) => {
                        if !m.streams.is_empty() {
                            let (lid, _, _) = m.streams.swap_remove(i % m.streams.len());
                            prop_assert!(net.drop_stream(lid).is_some());
                        }
                    }
                }
                let all = m.all();
                prop_assert!(net.in_use() <= all.len());
                prop_assert!(net.provs.last().is_none_or(Option::is_some));
                let mut peers: Vec<u32> = all.iter().map(|h| h.1).collect();
                peers.sort_unstable();
                peers.dedup();
                prop_assert_eq!(
                    net.in_use(),
                    peers.len(),
                    "a peer nothing uses is in the table, or one in use is missing"
                );
                prop_assert_eq!(net.streams.len(), m.streams.len());
                prop_assert_eq!(net.held.len(), m.fetches.len());
                for (p, n) in &all {
                    prop_assert_eq!(net.peer_of(*p), Some(peer(*n)));
                    prop_assert_eq!(net.lookup(&peer(*n)), Some(*p));
                    let uses = all.iter().filter(|h| h.0 == *p).count();
                    prop_assert_eq!(net.provs[p.0 as usize].map(|s| s.uses as usize), Some(uses));
                }
            }
            for (lid, _, _) in m.streams {
                net.drop_stream(lid);
            }
            for (id, _) in m.fetches {
                net.end_fetch(id);
            }
            for (p, _) in m.loose {
                net.release(p);
            }
            prop_assert!(net.provs.is_empty());
            prop_assert!(net.held.is_empty());
            prop_assert!(net.streams.is_empty());
            prop_assert!(net.by_real.is_empty());
        }
    }
}

#[cfg(feature = "trace")]
impl Net {
    /// Fills the provider, stream and held tables of `v` as they are (a probe of the trace feature).
    pub(crate) fn fill_view(&self, v: &mut crate::values_types::ValuesView) {
        v.provs = self.provs.iter().map(|s| s.map(|s| (s.peer, s.uses))).collect();
        v.streams = self
            .streams
            .iter()
            .map(|(lid, s)| {
                let owner = match s.owner() {
                    Owner::Fetch(f) => f,
                    Owner::Serve => 0,
                };
                (*lid, s.prov.0, owner, s.session())
            })
            .collect();
        v.held = self
            .held
            .iter()
            .map(|(f, ps)| (*f, ps.iter().map(|p| p.0).collect()))
            .collect();
    }
}

/// The tables of the values layer as the trace test of the proofs drives them (cargo feature `trace`): a real
/// `Net` whose provider and stream tables are filled, all but `window` slots and streams, by fillers that are never
/// given back, so what is left behaves as tables of `window`. Numbers and stream numbers are reported relative to the
/// first one past the fillers. The probe makes no decision of its own: each call is the call the node makes.
#[cfg(feature = "trace")]
pub mod probe {
    use alloc::vec::Vec;

    use pinc_core::SessionId;
    use pinc_values::session::Provider;

    use super::{Net, Owner};
    use crate::config::TABLE_MAX;

    /// The bound of both tables.
    pub const TABLE_MAX_PROBE: usize = TABLE_MAX;

    /// A `Net` with all but a window of its tables filled.
    #[derive(Debug)]
    pub struct NetProbe {
        net: Net,
        base: u32,
        lbase: u64,
        key: u64,
    }

    /// The window of the tables after a call.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct NetView {
        /// Slot `k` of the window (number `base + k`): `None` free, else the peer and its use count.
        pub provs: Vec<Option<([u8; 32], u32)>>,
        /// Every stream past the fillers: (relative stream number, relative provider number, owner: the fetch id,
        /// or 0 for the server).
        pub streams: Vec<(u64, u32, u32)>,
        /// Every running fetch with the relative numbers it holds, in order.
        pub held: Vec<(u32, Vec<u32>)>,
        /// Fetches refused by the provider table.
        pub refused: u64,
        /// The last stream number handed out, relative.
        pub next: u64,
    }

    /// The `j`-th filler peer: first byte 0xF0, so that no test peer collides.
    fn filler(j: usize) -> [u8; 32] {
        let mut id = [0u8; 32];
        id[0] = 0xF0;
        id[1] = u8::try_from(j & 0xFF).unwrap_or(0);
        id[2] = u8::try_from((j >> 8) & 0xFF).unwrap_or(0);
        id
    }

    impl NetProbe {
        /// Tables of `window` slots and streams (clamped to `1..TABLE_MAX`) behind fillers.
        pub fn new(window: usize) -> Self {
            let window = window.clamp(1, TABLE_MAX - 1);
            let fill = TABLE_MAX - window;
            let mut net = Net::default();
            for j in 0..fill {
                net.acquire(&filler(j));
            }
            let mut key = 0u64;
            for _ in 0..fill {
                net.add_for(SessionId(0), key, Owner::Serve, Provider(0));
                key += 1;
            }
            let lbase = net.next;
            Self {
                net,
                base: u32::try_from(fill).unwrap_or(u32::MAX),
                lbase,
                key,
            }
        }

        fn next_key(&mut self) -> u64 {
            self.key += 1;
            self.key
        }

        /// A fetch `fetch` of `peers`: the uses of all taken and the fetch begun, or none taken and the refusal
        /// counted.
        pub fn start(&mut self, fetch: u32, peers: &[[u8; 32]]) -> bool {
            match self.net.acquire_all(peers) {
                Ok(p) => {
                    self.net.begin_fetch(fetch, p);
                    true
                }
                Err(_) => false,
            }
        }

        /// A fetch done as it starts: the uses taken are given back at once.
        pub fn start_done(&mut self, peers: &[[u8; 32]]) -> bool {
            match self.net.acquire_all(peers) {
                Ok(p) => {
                    self.net.release_all(&p);
                    true
                }
                Err(_) => false,
            }
        }

        /// A fetch ended.
        pub fn end(&mut self, fetch: u32) {
            self.net.end_fetch(fetch);
        }

        /// A stream served for `peer`: its relative stream number, 0 for none.
        pub fn serve(&mut self, peer: &[u8; 32]) -> u64 {
            let Some(p) = self.net.acquire(peer) else {
                return 0;
            };
            let key = self.next_key();
            let lbase = self.lbase;
            self.net
                .add(SessionId(1), key, Owner::Serve, p)
                .map_or(0, |l| l.saturating_sub(lbase))
        }

        /// A stream of fetch `fetch` toward its `k`-th provider (from 1): its relative number, 0 for none.
        pub fn open(&mut self, fetch: u32, k: usize) -> u64 {
            let Some(p) = k
                .checked_sub(1)
                .and_then(|i| self.net.held.get(&fetch).and_then(|v| v.get(i)))
                .copied()
            else {
                return 0;
            };
            let key = self.next_key();
            let lbase = self.lbase;
            self.net
                .add_for(SessionId(2), key, Owner::Fetch(fetch), p)
                .map_or(0, |l| l.saturating_sub(lbase))
        }

        /// Drops the stream of relative number `lid`: whether there was one.
        pub fn drop(&mut self, lid: u64) -> bool {
            self.net.drop_stream(lid.saturating_add(self.lbase)).is_some()
        }

        /// The window of the tables.
        pub fn view(&self) -> NetView {
            let base = self.base;
            let provs = self
                .net
                .provs
                .iter()
                .skip(base as usize)
                .map(|s| s.map(|s| (s.peer, s.uses)))
                .collect();
            let streams = self
                .net
                .streams
                .iter()
                .filter(|(k, _)| **k > self.lbase)
                .map(|(k, s)| {
                    let owner = match s.owner() {
                        Owner::Fetch(f) => f,
                        Owner::Serve => 0,
                    };
                    (k.saturating_sub(self.lbase), s.prov.0.saturating_sub(base), owner)
                })
                .collect();
            let held = self
                .net
                .held
                .iter()
                .map(|(f, ps)| (*f, ps.iter().map(|p| p.0.saturating_sub(base)).collect()))
                .collect();
            NetView {
                provs,
                streams,
                held,
                refused: self.net.refused,
                next: self.net.next.saturating_sub(self.lbase),
            }
        }
    }

    /// `next_fetch_id` with the running fetches as a list.
    pub fn next_fetch_id(last: u32, running: &[u32]) -> u32 {
        super::next_fetch_id(last, |id| running.contains(&id))
    }
}
