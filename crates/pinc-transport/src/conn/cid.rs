//! Connection ids, derived from the session secret.
//!
//! Index 0 of each direction is the random id the handshake carried. Every later index `i` is
//! `keyed_hash(cid_secret, direction || i)[..len]`, so each side can compute the other side's ids without any frame
//! to announce them, and an observer without the secret cannot link two ids to one session. A sender takes the next
//! index each time a path needs an id of its own, but only while that index is within [`LOOKAHEAD`] of the highest
//! index the peer has answered on; past that it takes an id of that window again, turn by turn, and a path gives up
//! an id the peer never answered on once the window moved past it. So the sender never uses an id the receiver may
//! not accept, however many paths never deliver. The receiver accepts index 0 and a window of derived indices: every
//! index it holds less than [`LOOKAHEAD`] below the highest seen (the range a sender may still use), every older one
//! it has not needed to evict, and the next [`LOOKAHEAD`] indices after the highest seen, so a packet on a fresh path
//! is routable even when the first packet of the previous path was lost.
//!
//! Invariants: the table holds at most [`LOCAL_SLOTS`] derived ids; when it is full the least recently used entry whose
//! newest index (an entry stands for every index that derives its id) is at least [`LOOKAHEAD`] below the highest
//! index seen makes room; the entries from there up are never evicted, so the
//! indices after the highest one seen are always held once the secret is installed; the sender's id is index 0 or an
//! index above the highest one the peer answered on, and at most [`LOOKAHEAD`] above it; a received id is only a
//! candidate (another session of the same endpoint may derive the same four bytes): the packet's authentication
//! decides which session owns it.

use pinc_crypto::extract;
use pinc_security::ConnId;

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
    /// The highest index the peer acknowledged a packet on.
    confirmed: u64,
    /// How many ids of the window were handed out again.
    reuse: u64,
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
            confirmed: 0,
            reuse: 0,
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

    /// Make sure [`LOOKAHEAD`] indices after `highest` are in the table. An index whose derived id equals one the
    /// table already holds (the first id, or the id of another index) is not kept twice: the next index takes its
    /// place, within a window twice as wide. A peer can search for such a pair, so no id is ever listed twice. An
    /// entry whose id another index derives stands for that index too, so it is evicted only once the newest index
    /// it stands for is out of the sender's range.
    fn refill(&mut self) {
        let Some(secret) = self.secret else { return };
        let mut covered = 0;
        let mut index = self.highest;
        while covered < LOOKAHEAD && index < self.highest + 2 * LOOKAHEAD {
            index += 1;
            if self.entries.iter().flatten().any(|e| e.index == index) {
                covered += 1;
                continue;
            }
            let Some(cid) = derive(&secret, self.client, index, self.local_len()) else {
                continue;
            };
            if self.first_local == cid {
                continue;
            }
            // the held entry now also stands for this index: it is kept while the newest one it stands for may be used
            if let Some(e) = self.entries.iter_mut().flatten().find(|e| e.cid == cid) {
                e.index = e.index.max(index);
                continue;
            }
            let slot = match self.entries.iter().position(Option::is_none) {
                Some(i) => i,
                None => match self
                    .entries
                    .iter()
                    .enumerate()
                    .filter_map(|(i, e)| e.filter(|e| e.index + LOOKAHEAD <= self.highest).map(|e| (e.used, i)))
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
                covered += 1;
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

    /// The peer's id for a path that needs one of its own: the next index while it is within [`LOOKAHEAD`] of the
    /// highest one the peer answered on, otherwise an index of that window again, turn by turn. `None` before the
    /// session secret is known (only index 0 exists then) or while the peer's index 0 is unknown.
    pub(crate) fn claim_remote(&mut self) -> Option<(u64, ConnId)> {
        let first = self.first_remote?;
        let fresh = self.next_send <= self.confirmed + LOOKAHEAD;
        let index = if fresh {
            self.next_send
        } else {
            self.confirmed + 1 + self.reuse % LOOKAHEAD
        };
        let cid = if index == 0 {
            first
        } else {
            let secret = self.secret?;
            derive(&secret, !self.client, index, first.as_bytes().len())?
        };
        if fresh {
            self.next_send += 1;
        } else {
            self.reuse += 1;
        }
        Some((index, cid))
    }

    /// The peer acknowledged a packet sent with the id of `index`.
    pub(crate) fn confirm_remote(&mut self, index: u64) {
        self.confirmed = self.confirmed.max(index);
    }

    /// Whether the peer is known to accept the id of `index`: index 0, or one above the highest it answered on.
    pub(crate) const fn remote_usable(&self, index: u64) -> bool {
        index == 0 || index > self.confirmed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(
        clippy::unwrap_used,
        clippy::indexing_slicing,
        clippy::cast_possible_truncation,
        clippy::panic
    )]
    fn an_id_equal_to_one_held_is_not_kept_twice() {
        // One-byte ids collide within a few hundred secrets.
        for n in 0..=u16::MAX {
            let mut secret = [0u8; 32];
            secret[..2].copy_from_slice(&n.to_be_bytes());
            let (a, b) = (derive(&secret, false, 1, 1), derive(&secret, false, 2, 1));
            let Some(a) = a.filter(|a| Some(*a) == b) else { continue };
            let first = ConnId::new(&[a.as_bytes()[0].wrapping_add(1)]).unwrap();
            let mut c = Cids::new(false, first);
            c.install(&secret);
            for (k, id) in c.local().enumerate() {
                assert!(!c.local().take(k).any(|o| o == id), "{id:?} is listed twice");
            }
            assert_eq!(
                c.entries.iter().flatten().count(),
                LOOKAHEAD as usize,
                "the window kept its width"
            );
            return;
        }
        panic!("no colliding secret found");
    }

    /// Ids of two bytes: a pair collides once in 65536 secrets, three or more at once almost never.
    const LEN: usize = 2;

    #[allow(clippy::unwrap_used)]
    fn id_of(secret: &[u8; 32], index: u64, len: usize) -> ConnId {
        derive(secret, false, index, len).unwrap()
    }

    /// A secret under which index `pair.0` derives the id of index `pair.1` and no other two of the indices 1..=14
    /// (nor the first id) share one.
    #[allow(clippy::panic, clippy::indexing_slicing)]
    fn colliding_secret(first: ConnId, pair: (u64, u64)) -> [u8; 32] {
        for n in 0..=u32::MAX {
            let mut secret = [0u8; 32];
            secret[..4].copy_from_slice(&n.to_be_bytes());
            let id = |i| id_of(&secret, i, LEN);
            if id(pair.0) != id(pair.1) {
                continue;
            }
            let clean = (1..=14).all(|a| id(a) != first && (1..a).all(|b| (id(a) == id(b)) == ((a, b) == pair)));
            if clean {
                return secret;
            }
        }
        panic!("no colliding secret found");
    }

    /// The id of every index in `from..=to` (from 1 on) is accepted.
    fn assert_accepted(c: &Cids, secret: &[u8; 32], from: u64, to: u64, what: &str) {
        for j in from.max(1)..=to {
            let cid = id_of(secret, j, c.local_len());
            assert!(
                c.is_local(&cid),
                "the id of index {j}, {what}, is accepted (highest seen {})",
                c.highest
            );
        }
    }

    /// Authenticate packets to the ids of `indices`, in order, and check `window` of the table after each.
    fn drive(first: ConnId, pair: (u64, u64), indices: &[u64], window: impl Fn(&Cids, &[u8; 32])) {
        let secret = colliding_secret(first, pair);
        let mut c = Cids::new(false, first);
        c.install(&secret);
        window(&c, &secret);
        for &i in indices {
            c.on_authenticated(&id_of(&secret, i, LEN));
            window(&c, &secret);
        }
    }

    #[allow(clippy::unwrap_used)]
    fn first() -> ConnId {
        ConnId::new(&[0xff; LEN]).unwrap()
    }

    /// The witness of the model's lookahead check: index 9 has the id of index 1, a refill at the highest index 7
    /// passes 9 over, and the refill at 8 must not evict the entry that is also the id of 9, an index the sender takes
    /// next.
    #[test]
    fn a_collision_does_not_evict_the_id_of_an_index_ahead() {
        drive(first(), (9, 1), &[1, 3, 5, 7, 8], |c, s| {
            assert_accepted(c, s, c.highest + 1, c.highest + LOOKAHEAD, "ahead of the highest seen");
        });
    }

    /// The witness of the model's window check: index 8 has the id of index 1, and the refill at the highest index 9
    /// must not evict the entry that is also the id of 8, which the sender may still use.
    #[test]
    fn a_collision_does_not_evict_the_id_of_an_index_the_sender_may_still_use() {
        drive(first(), (8, 1), &[1, 3, 5, 7, 9], |c, s| {
            assert_accepted(
                c,
                s,
                (c.highest + 1).saturating_sub(LOOKAHEAD),
                c.highest,
                "one the sender may still use",
            );
        });
    }

    /// Whatever ids collide, every index from `LOOKAHEAD` below the highest seen up to `LOOKAHEAD` above it is accepted.
    #[test]
    #[allow(clippy::unwrap_used, clippy::indexing_slicing)]
    fn every_index_the_sender_may_use_is_accepted_under_random_collisions() {
        // ids of one byte collide in most sessions
        let mut x = 0x9e37_79b9_7f4a_7c15_u64;
        let mut next = move || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for _ in 0..2000 {
            let mut secret = [0u8; 32];
            secret[..8].copy_from_slice(&next().to_be_bytes());
            let first = ConnId::new(&[u8::try_from(next() & 0xff).unwrap()]).unwrap();
            let mut c = Cids::new(false, first);
            c.install(&secret);
            for _ in 0..60 {
                let from = c.highest.saturating_sub(3);
                let index = from + next() % (c.highest + 6 - from);
                c.on_authenticated(&id_of(&secret, index, 1));
                let (lo, hi) = ((c.highest + 1).saturating_sub(LOOKAHEAD), c.highest + LOOKAHEAD);
                assert_accepted(&c, &secret, lo, hi, "one the sender may use");
            }
        }
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
        /// The highest index the peer acknowledged a packet on.
        pub confirmed: u64,
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

        /// The peer acknowledged a packet sent with the id of `index`.
        pub fn confirm_remote(&mut self, index: u64) {
            self.cids.confirm_remote(index);
        }

        /// Whether the peer is known to accept the id of `index`.
        pub fn remote_usable(&self, index: u64) -> bool {
            self.cids.remote_usable(index)
        }

        /// The state of the table.
        pub fn view(&self) -> CidView {
            CidView {
                entries: self.cids.entries.map(|e| e.map(|e| (e.index, e.used, e.seen))),
                highest: self.cids.highest,
                tick: self.cids.tick,
                next_send: self.cids.next_send,
                confirmed: self.cids.confirmed,
                secret: self.cids.secret.is_some(),
                first_remote: self.cids.first_remote.is_some(),
                epoch: self.cids.epoch(),
            }
        }
    }
}
