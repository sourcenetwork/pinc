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
//! is not a lookahead entry makes room; a received id is only a candidate (another session of the same endpoint may
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
                    .filter_map(|(i, e)| e.filter(|e| e.seen).map(|e| (e.used, i)))
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
