//! Single-use resumption tickets and their two bounded stores.
//!
//! A ticket is a 16-byte id `tid` and a pre-shared key `psk = expand(resume, "ticket", tid, credit record)`, where
//! `resume` is the resumption secret of the session that issued it. The side that issues tickets keeps them in a
//! [`ServerTickets`] store; the side that dials with them keeps them in a [`ClientTickets`] store. Either side of a
//! session can issue: the responder issues to the initiator, and the initiator issues one to the responder, which
//! then holds it in its own [`ClientTickets`]. Invariants: a ticket is used at most once (the store removes it on
//! use, which is the replay defence for 0-RTT data); a [`ServerTickets`] store holds at most `N` tickets, evicting
//! expired tickets first and then the oldest; a [`ClientTickets`] store holds one ticket per peer, the newest
//! replacing the older, for at most `N` peers, evicting expired and then the oldest; `N = 0` is valid and stores
//! nothing, and then no ticket is handed out; a [`ServerTickets`] store has no way to read a pre-shared key out, list
//! its tickets or serialize, so it can be neither persisted nor exported (a store restored from an old snapshot
//! would allow replay; after a restart a client simply falls back to a full handshake). Only a [`ClientTickets`]
//! store exports, and its export is a secret the caller must seal before it is persisted. Expiry is in the
//! caller's nanoseconds.
// vertexia: linear scans over N slots, a hash index if the server store grows far beyond its 4000 default.

use pinc_crypto::{Aead, IdentityAlg, NodeId, Provider, Secret};
use pinc_wire::{Reader, WireError, Writer};

use crate::credit::{CREDIT_RECORD_LEN, CreditRecord};
use crate::error::Failure;
use crate::ids::{Alpn, MAX_ALPN_LEN, aead_from_tag, aead_tag};
use crate::schedule::ticket_psk;
use crate::session::{Env, Established};

/// The length of a ticket id.
pub const TID_LEN: usize = 16;
/// The most tickets in one batch.
pub const MAX_BATCH: usize = 4;
/// The most draws [`ServerTickets::issue_batch`] makes to find an unused ticket id.
pub const ID_ATTEMPTS: usize = 8;
/// The default lifetime of a ticket: 24 hours.
pub const DEFAULT_TICKET_LIFETIME_S: u32 = 86_400;
/// The default capacity of a [`ServerTickets`] store.
pub const DEFAULT_SERVER_TICKETS: usize = 4000;
/// The default capacity of a [`ClientTickets`] store: tickets of 48 peers.
pub const DEFAULT_CLIENT_TICKETS: usize = 48;
/// The version byte of an exported ticket state.
pub const EXPORT_VERSION: u8 = 1;
/// The most tickets an exported state holds: its count is one byte.
pub const MAX_EXPORT_TICKETS: usize = 255;
/// The longest exported entry: `alg(1) node(32) alpn_len(1) alpn tid(16) psk(32) aead(1) expiry(8) credit(6)`.
pub const MAX_EXPORT_ENTRY_LEN: usize = 1 + 32 + 1 + MAX_ALPN_LEN + TID_LEN + 32 + 1 + 8 + CREDIT_RECORD_LEN;

const NS_PER_S: u64 = 1_000_000_000;

fn expiry(now: u64, lifetime_s: u32) -> u64 {
    now.saturating_add(u64::from(lifetime_s).saturating_mul(NS_PER_S))
}

/// One issued ticket as it travels: the id and how long it is valid.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TicketEntry {
    /// The ticket id.
    pub tid: [u8; TID_LEN],
    /// The lifetime in seconds.
    pub lifetime_s: u32,
}

/// Up to [`MAX_BATCH`] tickets. Wire form: `count(1) <= 4`, then `count` entries of `tid(16) || lifetime_s(4)`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TicketBatch {
    len: u8,
    entries: [TicketEntry; MAX_BATCH],
}

impl TicketBatch {
    /// An empty batch.
    pub const fn new() -> Self {
        Self {
            len: 0,
            entries: [TicketEntry {
                tid: [0; TID_LEN],
                lifetime_s: 0,
            }; MAX_BATCH],
        }
    }

    /// Add a ticket; false if the batch is full.
    pub fn push(&mut self, entry: TicketEntry) -> bool {
        match self.entries.get_mut(usize::from(self.len)) {
            Some(slot) => {
                *slot = entry;
                self.len += 1;
                true
            }
            None => false,
        }
    }

    /// The tickets.
    pub fn entries(&self) -> &[TicketEntry] {
        self.entries.get(..usize::from(self.len)).unwrap_or_default()
    }

    /// Read a batch.
    ///
    /// # Errors
    /// [`WireError::Unexpected`] for a count over [`MAX_BATCH`], [`WireError::Truncated`] for a short buffer.
    pub fn read(r: &mut Reader<'_>) -> Result<Self, WireError> {
        let count = usize::from(r.read_u8()?);
        if count > MAX_BATCH {
            return Err(WireError::Unexpected("ticket count"));
        }
        let mut batch = Self::new();
        for _ in 0..count {
            let tid = r.read_array::<TID_LEN>()?;
            let lifetime_s = r.read_u32()?;
            batch.push(TicketEntry { tid, lifetime_s });
        }
        Ok(batch)
    }

    /// Parse a batch that fills `buf` exactly.
    ///
    /// # Errors
    /// As [`TicketBatch::read`], and [`WireError::Unexpected`] for a trailing byte.
    pub fn parse(buf: &[u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(buf);
        let batch = Self::read(&mut r)?;
        if r.is_empty() {
            Ok(batch)
        } else {
            Err(WireError::Unexpected("trailing bytes"))
        }
    }

    /// Append the batch.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn write(&self, w: &mut Writer<'_>) -> Result<(), WireError> {
        w.put_u8(self.len)?;
        for e in self.entries() {
            w.put_slice(&e.tid)?;
            w.put_u32(e.lifetime_s)?;
        }
        Ok(())
    }

    /// The batch as bytes in `buf`, and their count.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if `buf` is under 81 bytes.
    pub fn encode(&self, buf: &mut [u8]) -> Result<usize, WireError> {
        let mut w = Writer::new(buf);
        self.write(&mut w)?;
        Ok(w.written().len())
    }
}

/// A ticket taken from a [`ClientTickets`] store to start a resumption.
#[derive(Clone)]
pub struct Ticket {
    pub(crate) tid: [u8; TID_LEN],
    pub(crate) psk: Secret<32>,
    pub(crate) peer: NodeId,
    pub(crate) alpn: Alpn,
    pub(crate) aead: Aead,
    pub(crate) expiry: u64,
    pub(crate) credit: CreditRecord,
}

impl core::fmt::Debug for Ticket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Ticket")
            .field("peer", &self.peer)
            .finish_non_exhaustive()
    }
}

impl Ticket {
    /// The node the ticket resumes with.
    pub const fn peer(&self) -> &NodeId {
        &self.peer
    }

    /// The nanosecond after which the ticket is no longer valid.
    pub const fn expiry(&self) -> u64 {
        self.expiry
    }

    /// The issuer's credit record of the session that issued this ticket: what 0-RTT data may rely on.
    pub const fn peer_credit(&self) -> &CreditRecord {
        &self.credit
    }
}

/// Pick the slot to fill: an empty one, else an expired one, else the one with the lowest stamp. A slot index for
/// which `protected` holds is never picked.
fn victim<T>(
    slots: &[Option<T>],
    protected: impl Fn(usize) -> bool,
    now: u64,
    expiry_of: impl Fn(&T) -> u64,
    stamp_of: impl Fn(&T) -> u64,
) -> Option<usize> {
    let open = || (0..slots.len()).filter(|i| !protected(*i));
    open()
        .find(|i| slots.get(*i).is_some_and(Option::is_none))
        .or_else(|| {
            open().find(|i| {
                slots
                    .get(*i)
                    .and_then(Option::as_ref)
                    .is_some_and(|s| expiry_of(s) < now)
            })
        })
        .or_else(|| {
            open()
                .filter_map(|i| slots.get(i)?.as_ref().map(|s| (stamp_of(s), i)))
                .min()
                .map(|(_, i)| i)
        })
}

pub(crate) struct ServerSlot {
    pub(crate) tid: [u8; TID_LEN],
    pub(crate) psk: Secret<32>,
    pub(crate) peer: NodeId,
    pub(crate) alpn: Alpn,
    pub(crate) aead: Aead,
    pub(crate) expiry: u64,
    pub(crate) credit: CreditRecord,
    stamp: u64,
}

/// The issuer's store of outstanding tickets. Each slot is about 140 bytes; at the default 4000 slots place it in a
/// static or a box.
pub struct ServerTickets<const N: usize = DEFAULT_SERVER_TICKETS> {
    slots: [Option<ServerSlot>; N],
    clock: u64,
}

impl<const N: usize> core::fmt::Debug for ServerTickets<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ServerTickets")
            .field("len", &self.len())
            .field("capacity", &N)
            .finish()
    }
}

impl<const N: usize> Default for ServerTickets<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> ServerTickets<N> {
    /// An empty store.
    pub const fn new() -> Self {
        Self {
            slots: [const { None }; N],
            clock: 0,
        }
    }

    /// How many tickets are stored.
    pub fn len(&self) -> usize {
        self.slots.iter().flatten().count()
    }

    /// Whether the store is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The capacity `N`.
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Issue `count` (at most [`MAX_BATCH`]) fresh single-use tickets for `session` and store them. The batch is
    /// sent to the peer inside the session's protected channel; it holds fewer tickets than asked (none, if `N` is
    /// 0) when the store has no room: a ticket of the batch never evicts another of the same batch, so every ticket
    /// returned is in the store when the call returns.
    ///
    /// # Errors
    /// [`Failure::Randomness`] if the generator refuses; [`Failure::TicketId`] if no id different from every stored one
    /// turned up in [`ID_ATTEMPTS`] draws.
    pub fn issue_batch<P: Provider>(
        &mut self,
        env: &mut Env<'_, P>,
        session: &Established,
        count: usize,
        lifetime_s: u32,
    ) -> Result<TicketBatch, Failure> {
        let mut batch = TicketBatch::new();
        let mut mine = [usize::MAX; MAX_BATCH];
        for n in 0..count.min(MAX_BATCH) {
            let tid = self.fresh_id(env)?;
            self.clock = self.clock.wrapping_add(1);
            let slot = ServerSlot {
                tid,
                psk: ticket_psk(&session.resume, &tid, session.local_credit),
                credit: session.local_credit,
                peer: session.peer,
                alpn: session.alpn,
                aead: session.traffic.aead,
                expiry: expiry(env.now, lifetime_s),
                stamp: self.clock,
            };
            let at = victim(&self.slots, |i| mine.contains(&i), env.now, |s| s.expiry, |s| s.stamp);
            let Some((i, s)) = at.and_then(|i| self.slots.get_mut(i).map(|s| (i, s))) else {
                break;
            };
            *s = Some(slot);
            if let Some(m) = mine.get_mut(n) {
                *m = i;
            }
            batch.push(TicketEntry { tid, lifetime_s });
        }
        Ok(batch)
    }

    /// A ticket id that no stored ticket has, drawn from the generator in at most [`ID_ATTEMPTS`] tries.
    fn fresh_id<P: Provider>(&self, env: &mut Env<'_, P>) -> Result<[u8; TID_LEN], Failure> {
        for _ in 0..ID_ATTEMPTS {
            let tid = env.random::<TID_LEN>()?;
            if self.find(&tid).is_none() {
                return Ok(tid);
            }
        }
        Err(Failure::TicketId)
    }

    pub(crate) fn find(&self, tid: &[u8; TID_LEN]) -> Option<usize> {
        self.slots
            .iter()
            .position(|s| s.as_ref().is_some_and(|s| &s.tid == tid))
    }

    pub(crate) fn get(&self, index: usize) -> Option<&ServerSlot> {
        self.slots.get(index)?.as_ref()
    }

    /// The slot table in index order, for trace validation: the id and the expiry of each stored ticket, `None` for
    /// an empty slot.
    #[cfg(feature = "trace")]
    pub fn slot_table(&self) -> impl Iterator<Item = Option<([u8; TID_LEN], u64)>> + '_ {
        self.slots.iter().map(|s| s.as_ref().map(|s| (s.tid, s.expiry)))
    }

    pub(crate) fn remove(&mut self, index: usize) -> Option<ServerSlot> {
        self.slots.get_mut(index)?.take()
    }
}

struct ClientSlot {
    ticket: Ticket,
    stamp: u64,
}

/// The dialer's store of tickets received from peers: one per peer, the newest replacing the older.
pub struct ClientTickets<const N: usize = DEFAULT_CLIENT_TICKETS> {
    slots: [Option<ClientSlot>; N],
    clock: u64,
}

impl<const N: usize> core::fmt::Debug for ClientTickets<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ClientTickets")
            .field("len", &self.len())
            .field("capacity", &N)
            .finish()
    }
}

impl<const N: usize> Default for ClientTickets<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> ClientTickets<N> {
    /// An empty store.
    pub const fn new() -> Self {
        Self {
            slots: [const { None }; N],
            clock: 0,
        }
    }

    /// How many tickets (one per peer) are stored.
    pub fn len(&self) -> usize {
        self.slots.iter().flatten().count()
    }

    /// Whether the store is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Keep `ticket`, replacing the peer's older one; with no free slot the oldest stored ticket makes room.
    fn insert(&mut self, ticket: Ticket, now: u64) {
        self.clock = self.clock.wrapping_add(1);
        let slot = ClientSlot {
            ticket,
            stamp: self.clock,
        };
        let same = self
            .slots
            .iter()
            .position(|s| s.as_ref().is_some_and(|s| s.ticket.peer == slot.ticket.peer));
        let at = same.or_else(|| victim(&self.slots, |_| false, now, |s| s.ticket.expiry, |s| s.stamp));
        if let Some(s) = at.and_then(|i| self.slots.get_mut(i)) {
            *s = Some(slot);
        }
    }

    /// Store the tickets of `batch`, which the peer of `session` issued at time `now`. Each replaces the peer's
    /// earlier ticket, so the last of the batch is the one kept.
    pub fn accept_batch(&mut self, session: &Established, batch: &TicketBatch, now: u64) {
        for e in batch.entries() {
            self.insert(
                Ticket {
                    tid: e.tid,
                    psk: ticket_psk(&session.resume, &e.tid, session.peer_credit),
                    credit: session.peer_credit,
                    peer: session.peer,
                    alpn: session.alpn,
                    aead: session.traffic.aead,
                    expiry: expiry(now, e.lifetime_s),
                },
                now,
            );
        }
    }

    /// Store the tickets in `bytes`, a batch received over the protected channel of `session`.
    ///
    /// # Errors
    /// A [`WireError`] if `bytes` is not exactly one well-formed batch; nothing is stored then.
    pub fn accept_bytes(&mut self, session: &Established, bytes: &[u8], now: u64) -> Result<(), WireError> {
        let batch = TicketBatch::parse(bytes)?;
        self.accept_batch(session, &batch, now);
        Ok(())
    }

    /// Take the unexpired ticket for `peer` if it is for `alpn`, removing it (a ticket is used once). Expired
    /// tickets are dropped on the way.
    pub fn take(&mut self, peer: &NodeId, alpn: &[u8], now: u64) -> Option<Ticket> {
        for s in &mut self.slots {
            if s.as_ref().is_some_and(|s| s.ticket.expiry < now) {
                *s = None;
            }
        }
        let at = self.slots.iter().position(|s| {
            s.as_ref()
                .is_some_and(|s| &s.ticket.peer == peer && s.ticket.alpn.as_bytes() == alpn)
        })?;
        self.slots.get_mut(at)?.take().map(|s| s.ticket)
    }

    /// Write the state for persistence: the newest at most `max` (and at most [`MAX_EXPORT_TICKETS`], 255: the
    /// count is one byte) unexpired tickets, oldest first, as
    /// `version(1) count(1)` and then per ticket `alg(1) node(32) alpn_len(1) alpn tid(16) psk(32) aead(1)
    /// expiry(8) credit(6)`. Returns the length written.
    ///
    /// The bytes hold pre-shared keys: they are secret. The caller seals them (the key store's `seal`) before they
    /// reach a disk and zeroizes `out` afterwards. Tickets stay in the store, which is harmless: a ticket is single
    /// use at the issuer, so a restored copy of a used one is only rejected.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if `out` cannot hold the state; size it with
    /// `2 + max * MAX_EXPORT_ENTRY_LEN`.
    // vertexia: the live slots are ordered through two N-entry stack arrays, a bounded selection if N grows past a
    // few thousand.
    pub fn export(&self, now: u64, max: usize, out: &mut [u8]) -> Result<usize, WireError> {
        let mut live: [Option<&ClientSlot>; N] = [const { None }; N];
        for (l, s) in live.iter_mut().zip(&self.slots) {
            *l = s.as_ref().filter(|s| s.ticket.expiry >= now);
        }
        let count = live.iter().flatten().count().min(max).min(MAX_EXPORT_TICKETS);
        let skip = live.iter().flatten().count() - count;
        let mut order: [(u64, usize); N] = [(0, 0); N];
        let mut n = 0;
        for (i, s) in live.iter().enumerate() {
            if let (Some(s), Some(o)) = (s, order.get_mut(n)) {
                *o = (s.stamp, i);
                n += 1;
            }
        }
        let order = order.get_mut(..n).unwrap_or_default();
        order.sort_unstable();
        let mut w = Writer::new(out);
        w.put_u8(EXPORT_VERSION)?;
        w.put_u8(u8::try_from(count).map_err(|_| WireError::VarintOverflow)?)?;
        for (_, i) in order.iter().skip(skip) {
            let Some(t) = live.get(*i).copied().flatten().map(|s| &s.ticket) else {
                continue;
            };
            w.put_u8(t.peer.alg.tag())?;
            w.put_slice(&t.peer.bytes)?;
            w.put_u8(u8::try_from(t.alpn.as_bytes().len()).map_err(|_| WireError::VarintOverflow)?)?;
            w.put_slice(t.alpn.as_bytes())?;
            w.put_slice(&t.tid)?;
            w.put_slice(t.psk.expose())?;
            w.put_u8(aead_tag(t.aead))?;
            w.put_u64(t.expiry)?;
            w.put_slice(&t.credit.encode())?;
        }
        Ok(w.written().len())
    }

    /// Load a state written by [`ClientTickets::export`] (after the caller unsealed it): every entry that has not
    /// expired by `now` is stored as [`ClientTickets::accept_batch`] stores tickets. Returns how many of them the store
    /// holds when this returns (a ticket replaced or evicted by a later one is not counted; a state holds at most
    /// [`MAX_EXPORT_TICKETS`]).
    ///
    /// # Errors
    /// A [`WireError`] if `bytes` is not exactly one well-formed state; nothing is stored then.
    pub fn restore(&mut self, bytes: &[u8], now: u64) -> Result<usize, WireError> {
        let mut check = Reader::new(bytes);
        let count = read_export_header(&mut check)?;
        for _ in 0..count {
            read_export_entry(&mut check)?;
        }
        if !check.is_empty() {
            return Err(WireError::Unexpected("trailing bytes"));
        }
        let mut r = Reader::new(bytes);
        read_export_header(&mut r)?;
        let before = self.clock;
        for _ in 0..count {
            let t = read_export_entry(&mut r)?;
            if t.expiry >= now {
                self.insert(t, now);
            }
        }
        // Every slot written here carries a stamp above `before`; one overwritten by a later ticket counts once.
        Ok(self.slots.iter().flatten().filter(|s| s.stamp > before).count())
    }
}

fn read_export_header(r: &mut Reader<'_>) -> Result<usize, WireError> {
    if r.read_u8()? != EXPORT_VERSION {
        return Err(WireError::Unexpected("ticket state version"));
    }
    Ok(usize::from(r.read_u8()?))
}

fn read_export_entry(r: &mut Reader<'_>) -> Result<Ticket, WireError> {
    let alg = IdentityAlg::from_tag(r.read_u8()?).ok_or(WireError::Unexpected("identity algorithm"))?;
    let bytes = r.read_array::<32>()?;
    let alpn_len = usize::from(r.read_u8()?);
    let alpn = Alpn::new(r.read_bytes(alpn_len)?).ok_or(WireError::Unexpected("alpn length"))?;
    let tid = r.read_array::<TID_LEN>()?;
    let psk = Secret::new(r.read_array::<32>()?);
    let aead = aead_from_tag(r.read_u8()?).ok_or(WireError::Unexpected("unknown aead"))?;
    let expiry = r.read_u64()?;
    let credit = CreditRecord::decode(&r.read_array::<CREDIT_RECORD_LEN>()?);
    Ok(Ticket {
        tid,
        psk,
        peer: NodeId { alg, bytes },
        alpn,
        aead,
        expiry,
        credit,
    })
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::assert_is_empty, reason = "tests assert")]
mod tests {
    use super::*;
    use pinc_crypto::{Drbg, Software};

    use crate::session::Traffic;

    fn session() -> Established {
        Established {
            peer: NodeId {
                alg: IdentityAlg::Ed25519,
                bytes: [7; 32],
            },
            alpn: Alpn::new(b"pinc/1").unwrap(),
            traffic: Traffic {
                aead: Aead::Aes128Gcm,
                send: Secret::new([1; 32]),
                recv: Secret::new([2; 32]),
            },
            resume: Secret::new([5; 32]),
            tickets: TicketBatch::new(),
            resumed: false,
            peer_credit: CreditRecord::NONE,
            local_credit: CreditRecord::NONE,
            remembered_credit: CreditRecord::NONE,
            cid_secret: Secret::new([3; 32]),
        }
    }

    fn issue<const N: usize>(store: &mut ServerTickets<N>, drbg: &mut Drbg, count: usize) -> TicketBatch {
        let p = Software;
        let mut env = Env {
            provider: &p,
            now: 1_000,
            drbg,
        };
        store.issue_batch(&mut env, &session(), count, 60).unwrap()
    }

    #[test]
    fn a_batch_never_evicts_its_own_ticket() {
        let mut drbg = Drbg::new(&[9; 32]);
        // A batch larger than the capacity ends at the capacity, and every ticket it returns is stored.
        let mut small: ServerTickets<2> = ServerTickets::new();
        let b = issue(&mut small, &mut drbg, 4);
        assert_eq!((b.entries().len(), small.len()), (2, 2));
        assert!(b.entries().iter().all(|e| small.find(&e.tid).is_some()));
        // Into a full store, the batch evicts the oldest tickets and keeps its own.
        let mut full: ServerTickets<4> = ServerTickets::new();
        let old = issue(&mut full, &mut drbg, 4);
        let b = issue(&mut full, &mut drbg, 3);
        assert_eq!((b.entries().len(), full.len()), (3, 4));
        assert!(b.entries().iter().all(|e| full.find(&e.tid).is_some()));
        assert_eq!(old.entries().iter().filter(|e| full.find(&e.tid).is_some()).count(), 1);
        // No room at all: an empty batch.
        let mut none: ServerTickets<0> = ServerTickets::new();
        assert!(issue(&mut none, &mut drbg, 2).entries().is_empty());
    }
}
