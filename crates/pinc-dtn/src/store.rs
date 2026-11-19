//! The charged store: one byte budget and one eviction rule for everything a node keeps on behalf of others.
//!
//! The [`Ledger`] is the accounting and the policy. It holds one [`Entry`] per kept item (a bundle here, a mailbox
//! item for the mailbox layer, told apart by [`Key::space`]) with its size, its [`Class`] and its expiry. The owner
//! keeps the bytes wherever it likes and drops them when the ledger reports an eviction or a release; the ledger
//! never holds more than its budget, so the real resource (bytes) is what is bounded.
//!
//! Eviction order when an admission needs room: expired items first (of any class), then [`Class::Transit`] items,
//! oldest admission first. A [`Class::Custody`] item is never evicted before it expires; if that is what the budget
//! would force, the admission is refused ([`StoreError::CustodyRefused`] for custody, [`StoreError::Full`] otherwise)
//! and nothing live is evicted.
//!
//! Admission sweeps the expired items first, so a key that expired but was not yet swept is admitted fresh, and an item
//! that is already expired at admission is refused with [`StoreError::Expired`].
//!
//! Invariants: `used()` equals the sum of the entries' sizes and never exceeds `budget()`; an item whose expiry is
//! after `now` and whose class is custody leaves only through [`Ledger::release`] (delivery) or [`Ledger::reclass`]
//! to transit (custody handed on); a failed admission changes nothing except removing expired items; all scans are
//! over a fixed array of `N` slots in index order, so behaviour is deterministic.

// vertexia: linear scans over the slot array, O(N) per operation. N is small and fixed; an ordered index by
// admission sequence and by expiry is the upgrade if a node ever keeps tens of thousands of bundles.

/// The owner of a key: which layer the item belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Space(pub u8);

impl Space {
    /// Delay-tolerant bundles.
    pub const DTN: Self = Self(1);
    /// Mailbox items.
    pub const MAILBOX: Self = Self(2);
}

/// What a kept item is called: the layer that owns it and its 32-byte id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Key {
    /// The owning layer.
    pub space: Space,
    /// The item id (a bundle id for [`Space::DTN`]).
    pub id: [u8; 32],
}

/// How an item may be evicted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Class {
    /// A node accepted responsibility: kept until it expires or is released.
    Custody,
    /// Carried for others: may be evicted, oldest first, to make room.
    Transit,
}

/// One kept item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Entry {
    /// The item.
    pub key: Key,
    /// Its charged size in bytes.
    pub bytes: u64,
    /// Its class.
    pub class: Class,
    /// The physical time (milliseconds) at which it expires.
    pub expires: u64,
    seq: u64,
}

/// Why an admission or change was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StoreError {
    /// A custody item cannot be kept without evicting live custody: custody is refused.
    CustodyRefused,
    /// A transit item does not fit even after evicting every evictable item.
    Full,
    /// The key is already kept (after the expired items left).
    Duplicate,
    /// The item is already expired at the time of admission.
    Expired,
    /// The key is not kept.
    Unknown,
}

impl core::fmt::Display for StoreError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::CustodyRefused => "no room for custody without evicting custody",
            Self::Full => "the store is full",
            Self::Duplicate => "the item is already kept",
            Self::Expired => "the item is already expired",
            Self::Unknown => "the item is not kept",
        })
    }
}

impl core::error::Error for StoreError {}

/// The charged store ledger with room for `N` items.
#[derive(Debug, Clone)]
pub struct Ledger<const N: usize> {
    budget: u64,
    used: u64,
    next_seq: u64,
    slots: [Option<Entry>; N],
}

impl<const N: usize> Ledger<N> {
    /// An empty ledger that charges at most `budget` bytes.
    pub const fn new(budget: u64) -> Self {
        Self {
            budget,
            used: 0,
            next_seq: 0,
            slots: [None; N],
        }
    }

    /// The byte budget.
    pub const fn budget(&self) -> u64 {
        self.budget
    }

    /// The bytes charged now.
    pub const fn used(&self) -> u64 {
        self.used
    }

    /// The number of items kept.
    pub fn len(&self) -> usize {
        self.slots.iter().flatten().count()
    }

    /// Whether nothing is kept.
    pub fn is_empty(&self) -> bool {
        self.slots.iter().all(Option::is_none)
    }

    /// The kept items, in slot order.
    pub fn iter(&self) -> impl Iterator<Item = &Entry> + '_ {
        self.slots.iter().flatten()
    }

    /// The entry for `key`.
    pub fn get(&self, key: &Key) -> Option<&Entry> {
        self.iter().find(|e| e.key == *key)
    }

    /// Whether `key` is kept.
    pub fn contains(&self, key: &Key) -> bool {
        self.get(key).is_some()
    }

    fn take(&mut self, at: usize) -> Option<Entry> {
        let entry = self.slots.get_mut(at)?.take()?;
        self.used -= entry.bytes;
        Some(entry)
    }

    /// The earliest expiry of any item kept, if there is one.
    pub fn next_expiry(&self) -> Option<u64> {
        self.slots.iter().flatten().map(|e| e.expires).min()
    }

    /// Remove every item expired at `now` (`expires <= now`), reporting each to `on_evict`; returns how many.
    pub fn expire(&mut self, now: u64, mut on_evict: impl FnMut(&Entry)) -> usize {
        let mut n = 0;
        for at in 0..N {
            if self
                .slots
                .get(at)
                .and_then(Option::as_ref)
                .is_some_and(|e| e.expires <= now)
                && let Some(e) = self.take(at)
            {
                on_evict(&e);
                n += 1;
            }
        }
        n
    }

    /// The slot of the oldest transit item, if any.
    fn oldest_transit(&self) -> Option<usize> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(at, s)| s.as_ref().filter(|e| e.class == Class::Transit).map(|e| (e.seq, at)))
            .min()
            .map(|(_, at)| at)
    }

    /// Keep `bytes` bytes under `key`, evicting as the module docs describe and reporting every eviction to
    /// `on_evict`.
    ///
    /// # Errors
    /// Expired items leave first, so a key that expired but was not yet swept is admitted fresh. Then:
    /// [`StoreError::Duplicate`] if `key` is kept; [`StoreError::Expired`] if `expires <= now`;
    /// [`StoreError::CustodyRefused`] or [`StoreError::Full`] if the item cannot fit without evicting live custody.
    /// Expired items are removed even when the admission fails.
    pub fn admit(
        &mut self,
        key: Key,
        bytes: u64,
        class: Class,
        expires: u64,
        now: u64,
        mut on_evict: impl FnMut(&Entry),
    ) -> Result<(), StoreError> {
        self.expire(now, &mut on_evict);
        if self.contains(&key) {
            return Err(StoreError::Duplicate);
        }
        if expires <= now {
            return Err(StoreError::Expired);
        }
        let refused = match class {
            Class::Custody => StoreError::CustodyRefused,
            Class::Transit => StoreError::Full,
        };
        let (transit_bytes, transit_count) = self
            .iter()
            .filter(|e| e.class == Class::Transit)
            .fold((0u64, 0usize), |(b, c), e| (b.saturating_add(e.bytes), c + 1));
        let free_slots = N - self.len();
        let free_bytes = self.budget.saturating_sub(self.used);
        let fits = free_bytes.saturating_add(transit_bytes) >= bytes && (free_slots > 0 || transit_count > 0);
        if !fits {
            return Err(refused);
        }
        while self.budget.saturating_sub(self.used) < bytes || self.len() == N {
            let at = self.oldest_transit().ok_or(refused)?;
            if let Some(e) = self.take(at) {
                on_evict(&e);
            }
        }
        let seq = self.next_seq;
        self.next_seq += 1;
        let slot = self.slots.iter_mut().find(|s| s.is_none()).ok_or(refused)?;
        *slot = Some(Entry {
            key,
            bytes,
            class,
            expires,
            seq,
        });
        self.used += bytes;
        Ok(())
    }

    /// Remove `key` on purpose (it was delivered), custody included.
    pub fn release(&mut self, key: &Key) -> Option<Entry> {
        let at = self
            .slots
            .iter()
            .position(|s| s.as_ref().is_some_and(|e| e.key == *key))?;
        self.take(at)
    }

    /// Change the class of a kept item. It needs no extra room, so it cannot fail for lack of space.
    ///
    /// # Errors
    /// [`StoreError::Unknown`] if `key` is not kept.
    pub fn reclass(&mut self, key: &Key, class: Class) -> Result<(), StoreError> {
        let entry = self
            .slots
            .iter_mut()
            .flatten()
            .find(|e| e.key == *key)
            .ok_or(StoreError::Unknown)?;
        entry.class = class;
        Ok(())
    }
}
