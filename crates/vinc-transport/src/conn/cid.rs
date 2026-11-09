//! Connection ids, derived from the session secret.
//!
//! Index 0 of each direction is the random id the handshake carried. Every later index `i` is
//! `keyed_hash(cid_secret, direction || i)[..len]`, so each side can compute the other side's ids without any frame
//! to announce them, and an observer without the secret cannot link two ids to one session. A sender takes the next
//! index each time a path needs an id of its own and never reuses one. The receiver accepts index 0 and a window of
//! derived indices: every index it has seen on an authenticated packet that it still holds, and the next
//! [`LOOKAHEAD`] indices after the highest seen, so a packet on a fresh path is routable even when the first packet
//! of the previous path was lost.
//!
//! Invariants: the table holds at most [`LOCAL_SLOTS`] derived ids; when it is full the least recently used one that
//! is not a lookahead entry makes room (an entry used by a packet, or stale: below the highest index seen and never
//! used, as the peer's path that was to use it never delivered); the lookahead entries are never evicted, so the
//! indices after the highest one seen are always held once the secret is installed; a received id is only a candidate (another session of the same endpoint may
//! derive the same four bytes): the packet's authentication decides which session owns it.

use vinc_crypto::extract;
use vinc_security::ConnId;

/// Derived ids a receiver holds, besides index 0.
pub(crate) const LOCAL_SLOTS: usize = 8;
/// How many indices past the highest authenticated one the receiver accepts.
pub(crate) const LOOKAHEAD: u64 = 2;

/// The id of `index` for the receiver whose role is `to_client`, of `len` bytes.
fn derive(secret: &[u8; 32], to_client: bool, index: u64, len: usize) -> Option<ConnId> {
    let mut input = [0u8; 9];
    if let Some(d) = input.first_mut() {
        *d = u8::from(to_client);
    }
    input.get_mut(1..)?.copy_from_slice(&index.to_be_bytes());
    let hash = extract(secret, &input);
    ConnId::new(hash.get(..len)?)
}

#[derive(Debug, Clone, Copy)]
struct Entry {
    index: u64,
    cid: ConnId,
    used: u64,
    seen: bool,
}

/// The connection id tables of one connection.
#[derive(Debug)]
pub(crate) struct Cids {
    client: bool,
    first_local: ConnId,
    first_remote: Option<ConnId>,
    secret: Option<[u8; 32]>,
    entries: [Option<Entry>; LOCAL_SLOTS],
    highest: u64,
    tick: u64,
    next_send: u64,
}

impl Cids {
    pub(crate) const fn new(client: bool, first_local: ConnId) -> Self {
        Self {
            client,
            first_local,
            first_remote: None,
            secret: None,
            entries: [None; LOCAL_SLOTS],
            highest: 0,
            tick: 0,
            next_send: 0,
        }
    }

    /// Our id with index 0, the one the handshake carried.
    pub(crate) const fn first_local(&self) -> ConnId {
        self.first_local
    }

    /// The peer's id with index 0, learned from the first long header.
    pub(crate) const fn first_remote(&self) -> Option<ConnId> {
        self.first_remote
    }

    pub(crate) fn set_first_remote(&mut self, cid: ConnId) {
        self.first_remote.get_or_insert(cid);
    }

    /// Start deriving from the session secret: the lookahead ids become routable.
    pub(crate) fn install(&mut self, secret: &[u8; 32]) {
        self.secret = Some(*secret);
        self.refill();
    }

    fn local_len(&self) -> usize {
        self.first_local.as_bytes().len()
    }

    /// Make sure indices `highest + 1 ..= highest + LOOKAHEAD` are in the table.
    fn refill(&mut self) {
        let Some(secret) = self.secret else { return };
        for index in self.highest + 1..=self.highest + LOOKAHEAD {
            if self.entries.iter().flatten().any(|e| e.index == index) {
                continue;
            }
            let Some(cid) = derive(&secret, self.client, index, self.local_len()) else {
                continue;
            };
            let slot = match self.entries.iter().position(Option::is_none) {
                Some(i) => i,
                None => match self
                    .entries
                    .iter()
                    .enumerate()
                    .filter_map(|(i, e)| e.filter(|e| e.seen || e.index <= self.highest).map(|e| (e.used, i)))
                    .min()
                {
                    Some((_, i)) => i,
                    None => continue,
                },
            };
            if let Some(s) = self.entries.get_mut(slot) {
                *s = Some(Entry {
                    index,
                    cid,
                    used: self.tick,
                    seen: false,
                });
            }
        }
    }

    /// A number that changes whenever the set of accepted ids does.
    pub(crate) fn epoch(&self) -> u64 {
        self.highest
            .wrapping_mul(2)
            .wrapping_add(u64::from(self.secret.is_some()))
    }

    /// Whether `cid` is one of the ids this side accepts.
    pub(crate) fn is_local(&self, cid: &ConnId) -> bool {
        self.first_local == *cid || self.entries.iter().flatten().any(|e| e.cid == *cid)
    }

    /// Every id this side accepts now: the endpoint routes datagrams to the session by these.
    pub(crate) fn local(&self) -> impl Iterator<Item = ConnId> + '_ {
        core::iter::once(self.first_local).chain(self.entries.iter().flatten().map(|e| e.cid))
    }

    /// A packet to `cid` authenticated: its index counts as seen, and the lookahead moves up.
    pub(crate) fn on_authenticated(&mut self, cid: &ConnId) {
        self.tick += 1;
        let tick = self.tick;
        let Some(e) = self.entries.iter_mut().flatten().find(|e| e.cid == *cid) else {
            return;
        };
        e.seen = true;
        e.used = tick;
        if e.index > self.highest {
            self.highest = e.index;
            self.refill();
        }
    }

    /// The peer's id for a path that needs one of its own: the next index, never reused. `None` before the secret is
    /// known (only index 0 exists then) or while the peer's index 0 is unknown.
    pub(crate) fn claim_remote(&mut self) -> Option<(u64, ConnId)> {
        let first = self.first_remote?;
        let index = self.next_send;
        let cid = if index == 0 {
            first
        } else {
            let secret = self.secret?;
            derive(&secret, !self.client, index, first.as_bytes().len())?
        };
        self.next_send += 1;
        Some((index, cid))
    }
}

/// Test-only drivers of the connection id tables, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
pub(super) mod trace {
    use super::{Cids, ConnId, LOCAL_SLOTS, derive};

    /// The state of a table: per slot the derived index, the tick of its last use and whether a packet used it.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct CidView {
        /// The slots.
        pub entries: [Option<(u64, u64, bool)>; LOCAL_SLOTS],
        /// The highest index seen on an authenticated packet.
        pub highest: u64,
        /// The use counter.
        pub tick: u64,
        /// The next index the sender takes.
        pub next_send: u64,
        /// Whether the session secret is installed.
        pub secret: bool,
        /// Whether the peer's first id is known.
        pub first_remote: bool,
        /// The epoch number.
        pub epoch: u64,
    }

    /// A connection id table driven by index: the id of index `i` is the one the code derives for it.
    #[derive(Debug)]
    pub struct CidTable {
        cids: Cids,
        secret: Option<[u8; 32]>,
        client: bool,
    }

    impl CidTable {
        /// A table for a client or a server whose first id is `first_local`.
        pub fn new(client: bool, first_local: &[u8]) -> Option<Self> {
            Some(Self {
                cids: Cids::new(client, ConnId::new(first_local)?),
                secret: None,
                client,
            })
        }

        /// The peer's first id is known.
        pub fn set_first_remote(&mut self, first_remote: &[u8]) {
            if let Some(id) = ConnId::new(first_remote) {
                self.cids.set_first_remote(id);
            }
        }

        /// Install the session secret.
        pub fn install(&mut self, secret: &[u8; 32]) {
            self.secret = Some(*secret);
            self.cids.install(secret);
        }

        fn id_of(&self, index: u64) -> Option<ConnId> {
            if index == 0 {
                return Some(self.cids.first_local());
            }
            derive(
                &self.secret?,
                self.client,
                index,
                self.cids.first_local().as_bytes().len(),
            )
        }

        /// A packet addressed to the id of `index` authenticated.
        pub fn on_authenticated(&mut self, index: u64) {
            // an index the table cannot derive (no secret yet) is an id it does not hold
            let id = self.id_of(index).unwrap_or_default();
            self.cids.on_authenticated(&id);
        }

        /// Whether the id of `index` is one this side accepts.
        pub fn is_local(&self, index: u64) -> bool {
            self.id_of(index).is_some_and(|id| self.cids.is_local(&id))
        }

        /// The ids this side accepts now: the first and every derived one held.
        pub fn local_count(&self) -> usize {
            self.cids.local().count()
        }

        /// The id the sender takes for a path of its own: its index and whether the id is the one derived for that index
        /// (index 0 is the peer's first id).
        pub fn claim_remote(&mut self) -> Option<(u64, bool)> {
            let (index, id) = self.cids.claim_remote()?;
            let derived = index == 0
                || self
                    .secret
                    .and_then(|s| derive(&s, !self.client, index, id.as_bytes().len()))
                    .is_some_and(|want| want == id);
            Some((index, derived))
        }

        /// The state of the table.
        pub fn view(&self) -> CidView {
            CidView {
                entries: self.cids.entries.map(|e| e.map(|e| (e.index, e.used, e.seen))),
                highest: self.cids.highest,
                tick: self.cids.tick,
                next_send: self.cids.next_send,
                secret: self.cids.secret.is_some(),
                first_remote: self.cids.first_remote.is_some(),
                epoch: self.cids.epoch(),
            }
        }
    }
}
