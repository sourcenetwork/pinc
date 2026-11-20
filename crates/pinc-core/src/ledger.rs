//! The amplification ledger: every outgoing datagram to an address passes one gate.
//!
//! Per remote address the ledger keeps `[rx, tx, validated]`. An address that wrote to us first is held to three times
//! the bytes it sent until it answers something we sent it; an address we wrote to first (we dialed it) is validated
//! from the start, and so is an address the host dials, even one that wrote first. Each sent datagram counts its size
//! plus 28 bytes (the IP and UDP headers).
//!
//! Invariants (while an address's byte counts are below 2^64, where they saturate): the ledger holds at most
//! [`LEDGER_ENTRIES`] addresses and evicts the one inserted first when full; for an address that is not validated the
//! bytes charged never exceed three times the bytes received, so a spoofed
//! source gets at most three times what it sent; the address of an evicted entry that is later written to counts as
//! one we spoke to first, which is the bound the eviction trades for the fixed table.

use core::net::SocketAddr;

use crate::table::Table;

/// The most addresses the ledger tracks.
pub const LEDGER_ENTRIES: usize = 1024;
/// Header bytes added to every sent datagram.
pub const DATAGRAM_OVERHEAD: u64 = 28;
/// Bytes that may be sent to an unvalidated address per byte it sent.
pub const FACTOR: u64 = 3;

/// What the ledger knows about one address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LedgerEntry {
    /// Bytes received from the address.
    pub rx: u64,
    /// Bytes charged for datagrams sent to it.
    pub tx: u64,
    /// Whether the address answered something we sent, or was dialed by us.
    pub validated: bool,
}

/// The ledger; see the module docs.
#[derive(Debug)]
pub struct Ledger {
    table: Table<SocketAddr, LedgerEntry, LEDGER_ENTRIES>,
}

impl Ledger {
    crate::store::store_fn! {
    /// An empty ledger whose table hash is keyed by `seed`.
    pub fn new(seed: u64) -> Self {
        Self {
            table: Table::new(seed),
        }
    }
    }

    /// How many addresses are tracked.
    pub const fn len(&self) -> usize {
        self.table.len()
    }

    /// Whether no address is tracked.
    pub const fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    /// The entry of `addr`.
    pub fn get(&self, addr: &SocketAddr) -> Option<LedgerEntry> {
        self.table.get(addr).copied()
    }

    /// Count a datagram of `n` bytes received from `addr`. A first datagram creates the entry unvalidated; a later one
    /// validates the address if we sent to it meanwhile. Returns whether the address is held after it (not validated).
    pub fn on_receive(&mut self, addr: SocketAddr, n: u64) -> bool {
        if let Some(e) = self.table.get_mut(&addr) {
            e.rx = e.rx.saturating_add(n);
            if e.tx > 0 {
                e.validated = true;
            }
            return !e.validated;
        }
        self.table.insert(
            addr,
            LedgerEntry {
                rx: n,
                tx: 0,
                validated: false,
            },
        );
        true
    }

    /// The host dials `addr`: the address counts as one we spoke to first, whatever it sent before. A peer that still
    /// holds a session with us keeps writing to the address we restarted on, and that must not hold back our dial.
    pub fn open(&mut self, addr: SocketAddr) {
        match self.table.get_mut(&addr) {
            Some(e) => e.validated = true,
            None => {
                self.table.insert(
                    addr,
                    LedgerEntry {
                        rx: 0,
                        tx: 0,
                        validated: true,
                    },
                );
            }
        }
    }

    /// Ask to send a datagram of `n` bytes (without headers) to `addr`: true charges it, false holds it.
    pub fn allow_send(&mut self, addr: SocketAddr, n: u64) -> bool {
        let charge = n.saturating_add(DATAGRAM_OVERHEAD);
        match self.table.get_mut(&addr) {
            None => {
                self.table.insert(
                    addr,
                    LedgerEntry {
                        rx: 0,
                        tx: charge,
                        validated: true,
                    },
                );
                true
            }
            Some(e) if e.validated => {
                e.tx = e.tx.saturating_add(charge);
                true
            }
            Some(e) => {
                if u128::from(e.tx) + u128::from(charge) > u128::from(e.rx) * u128::from(FACTOR) {
                    false
                } else {
                    e.tx = e.tx.saturating_add(charge);
                    true
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn a(n: u8) -> SocketAddr {
        SocketAddr::from(([10, 0, 0, n], 4000))
    }

    #[test]
    fn a_dialed_address_is_open_and_a_spoofed_one_is_held_to_three_times() {
        let mut l = Ledger::new(1);
        assert!(l.allow_send(a(1), 1200));
        assert!(l.allow_send(a(1), 1200));
        assert!(l.on_receive(a(2), 100), "a first datagram leaves the address held");
        let mut sent = 0;
        while l.allow_send(a(2), 10) {
            sent += 10 + DATAGRAM_OVERHEAD;
        }
        assert!(sent <= 3 * 100);
        assert!(sent + 10 + DATAGRAM_OVERHEAD > 300);
    }

    #[test]
    fn dialing_an_address_that_wrote_first_opens_it() {
        let mut l = Ledger::new(1);
        assert!(l.on_receive(a(4), 25));
        assert!(!l.allow_send(a(4), 1200));
        l.open(a(4));
        assert!(!l.on_receive(a(4), 25), "an address we dialed is not held");
        assert!(l.allow_send(a(4), 1200));
        l.open(a(5));
        assert_eq!(l.get(&a(5)).map(|e| (e.rx, e.tx, e.validated)), Some((0, 0, true)));
    }

    #[test]
    fn answering_validates() {
        let mut l = Ledger::new(1);
        assert!(l.on_receive(a(3), 50));
        assert!(!l.allow_send(a(3), 1000));
        assert!(l.allow_send(a(3), 20));
        assert!(
            !l.on_receive(a(3), 50),
            "after it answered what we sent, the address is not held"
        );
        assert_eq!(l.get(&a(3)).map(|e| e.validated), Some(true));
        assert!(l.allow_send(a(3), 60_000));
    }

    #[test]
    fn the_table_is_bounded_and_evicts_the_first_inserted() {
        let mut l = Ledger::new(9);
        for i in 0..(LEDGER_ENTRIES as u32 + 10) {
            l.on_receive(SocketAddr::from((i.to_be_bytes(), 1)), 1);
        }
        assert_eq!(l.len(), LEDGER_ENTRIES);
        assert!(l.get(&SocketAddr::from((0u32.to_be_bytes(), 1))).is_none());
        assert!(
            l.get(&SocketAddr::from(((LEDGER_ENTRIES as u32 + 9).to_be_bytes(), 1)))
                .is_some()
        );
    }
}
