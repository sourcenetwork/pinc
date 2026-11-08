//! Single-use resumption tickets and their two bounded stores.
//!
//! A ticket is a 16-byte id `tid` and a pre-shared key `psk = expand(resume, "ticket", tid)`, where `resume` is the
//! resumption secret of the session that issued it. The side that issues tickets keeps them in a [`ServerTickets`]
//! store; the side that dials with them keeps them in a [`ClientTickets`] store. Invariants: a ticket is used at
//! most once (the store removes it on use, which is the replay defence for 0-RTT data); both stores hold at most `N`
//! tickets, evicting expired tickets first and then the oldest; `N = 0` is valid and stores nothing, and then no
//! ticket is handed out; a [`ServerTickets`] store has no way to read a pre-shared key out, list its tickets or
//! serialize, so it can be neither persisted nor exported (a store restored from an old snapshot would allow
//! replay; after a restart a client simply falls back to a full handshake). Expiry is in the caller's nanoseconds.
// vertexia: linear scans over N slots, a hash index if the server store grows far beyond its 4000 default.

use vinc_crypto::{Aead, NodeId, Provider, Secret};
use vinc_wire::{Reader, WireError, Writer};

use crate::error::Failure;
use crate::ids::Alpn;
use crate::schedule::ticket_psk;
use crate::session::{Env, Established};

/// The length of a ticket id.
pub const TID_LEN: usize = 16;
/// The most tickets in one batch.
pub const MAX_BATCH: usize = 4;
/// The default lifetime of a ticket: 24 hours.
pub const DEFAULT_TICKET_LIFETIME_S: u32 = 86_400;
/// The default capacity of a [`ServerTickets`] store.
pub const DEFAULT_SERVER_TICKETS: usize = 4000;
/// The default capacity of a [`ClientTickets`] store.
pub const DEFAULT_CLIENT_TICKETS: usize = 48;

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
}

/// Pick the slot to fill: an empty one, else an expired one, else the one with the lowest stamp.
fn victim<T>(
    slots: &[Option<T>],
    now: u64,
    expiry_of: impl Fn(&T) -> u64,
    stamp_of: impl Fn(&T) -> u64,
) -> Option<usize> {
    slots
        .iter()
        .position(Option::is_none)
        .or_else(|| {
            slots
                .iter()
                .position(|s| s.as_ref().is_some_and(|s| expiry_of(s) < now))
        })
        .or_else(|| {
            slots
                .iter()
                .enumerate()
                .filter_map(|(i, s)| s.as_ref().map(|s| (stamp_of(s), i)))
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
    /// 0) when the store has no room.
    ///
    /// # Errors
    /// [`Failure::Randomness`] if the generator refuses.
    pub fn issue_batch<P: Provider>(
        &mut self,
        env: &mut Env<'_, P>,
        session: &Established,
        count: usize,
        lifetime_s: u32,
    ) -> Result<TicketBatch, Failure> {
        let mut batch = TicketBatch::new();
        for _ in 0..count.min(MAX_BATCH) {
            let tid = env.random::<TID_LEN>()?;
            self.clock = self.clock.wrapping_add(1);
            let slot = ServerSlot {
                tid,
                psk: ticket_psk(&session.resume, &tid),
                peer: session.peer,
                alpn: session.alpn,
                aead: session.traffic.aead,
                expiry: expiry(env.now, lifetime_s),
                stamp: self.clock,
            };
            let at = victim(&self.slots, env.now, |s| s.expiry, |s| s.stamp);
            if let Some(s) = at.and_then(|i| self.slots.get_mut(i)) {
                *s = Some(slot);
                batch.push(TicketEntry { tid, lifetime_s });
            }
        }
        Ok(batch)
    }

    pub(crate) fn find(&self, tid: &[u8; TID_LEN]) -> Option<usize> {
        self.slots
            .iter()
            .position(|s| s.as_ref().is_some_and(|s| &s.tid == tid))
    }

    pub(crate) fn get(&self, index: usize) -> Option<&ServerSlot> {
        self.slots.get(index)?.as_ref()
    }

    pub(crate) fn remove(&mut self, index: usize) -> Option<ServerSlot> {
        self.slots.get_mut(index)?.take()
    }
}

struct ClientSlot {
    ticket: Ticket,
    stamp: u64,
}

/// The dialer's store of tickets received from peers.
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

    /// How many tickets are stored.
    pub fn len(&self) -> usize {
        self.slots.iter().flatten().count()
    }

    /// Whether the store is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Store the tickets of `batch`, which the peer of `session` issued at time `now`.
    pub fn accept_batch(&mut self, session: &Established, batch: &TicketBatch, now: u64) {
        for e in batch.entries() {
            self.clock = self.clock.wrapping_add(1);
            let slot = ClientSlot {
                ticket: Ticket {
                    tid: e.tid,
                    psk: ticket_psk(&session.resume, &e.tid),
                    peer: session.peer,
                    alpn: session.alpn,
                    aead: session.traffic.aead,
                    expiry: expiry(now, e.lifetime_s),
                },
                stamp: self.clock,
            };
            let at = victim(&self.slots, now, |s| s.ticket.expiry, |s| s.stamp);
            if let Some(s) = at.and_then(|i| self.slots.get_mut(i)) {
                *s = Some(slot);
            }
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

    /// Take the newest unexpired ticket for `peer` and `alpn`, removing it (a ticket is used once). Expired tickets
    /// are dropped on the way.
    pub fn take(&mut self, peer: &NodeId, alpn: &[u8], now: u64) -> Option<Ticket> {
        for s in &mut self.slots {
            if s.as_ref().is_some_and(|s| s.ticket.expiry < now) {
                *s = None;
            }
        }
        let best = self
            .slots
            .iter()
            .enumerate()
            .filter_map(|(i, s)| s.as_ref().map(|s| (i, s)))
            .filter(|(_, s)| &s.ticket.peer == peer && s.ticket.alpn.as_bytes() == alpn)
            .max_by_key(|(_, s)| s.stamp)
            .map(|(i, _)| i)?;
        self.slots.get_mut(best)?.take().map(|s| s.ticket)
    }
}
