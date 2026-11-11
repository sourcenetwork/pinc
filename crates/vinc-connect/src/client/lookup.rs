//! The lookup client: ask the home relay for a peer's signed record, verify the answer.
//!
//! A query goes to the home relay over UDP (DNSQ). If no answer came within [`RETRY_NS`] it is asked again, and the
//! retry is also sent to every other relay (records are replicated to all of them). A node that never heard a UDP
//! datagram asks over its open home carrier instead (CARRIER_DNS): the stream is reliable, so the query is not
//! repeated to every relay and a new one waits at least [`CARRIER_WAIT_NS`]; with no carrier open nothing is sent
//! and the query is asked again once one opens. An answer too large for a datagram is asked again over the carrier.
//!
//! A thin node (round trip of 250 ms or more) repeats a query only after twice its round trip, at most
//! [`THIN_WAIT_MAX_NS`], so the repeat does not leave before the answer could have arrived.
//!
//! The asker never trusts the relay: [`verify`] parses the returned record and checks its signature, and the record
//! must belong to the peer asked about.
//!
//! Invariants: the table is bounded and a full table refuses a new query rather than forgetting an old one; a query
//! is outstanding from the moment it is asked until it is answered or [`Lookups::clear`]ed; a record that fails
//! verification is never returned.

use core::net::SocketAddr;

use vinc_crypto::NodeId;

use crate::carrier::frame::DnsAnswer;
use crate::record::{MAX_ADDRS, MAX_HINT_LEN, Reach, Record, RecordError};

/// The wait before a lookup is repeated over UDP.
pub const RETRY_NS: u64 = 300_000_000;
/// The longest wait before a thin node repeats a lookup.
pub const THIN_WAIT_MAX_NS: u64 = 8_000_000_000;
/// The least wait before a lookup is repeated over a carrier.
pub const CARRIER_WAIT_NS: u64 = 2_000_000_000;

/// How a query is to be sent.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ask {
    /// An earlier query is still within its wait.
    Skip,
    /// Send over UDP to the home relay; with `others` also to every other relay (this is a repeat). The first query
    /// of a dark node with no carrier open also takes this form.
    Udp {
        /// Also send to every other relay.
        others: bool,
    },
    /// Send over the open home carrier.
    Carrier,
    /// A carrier is needed and none is open: nothing is sent now, the query is asked again after a wait.
    Later,
}

#[derive(Debug, Clone, Copy)]
struct Item {
    peer: NodeId,
    at: u64,
    tried: bool,
    carrier_only: bool,
    again: bool,
    /// The wait after `at` before the query is repeated.
    wait: u64,
}

/// The outstanding queries, at most `N`.
#[derive(Debug, Clone, Copy)]
pub struct Lookups<const N: usize> {
    items: [Option<Item>; N],
}

impl<const N: usize> Default for Lookups<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Lookups<N> {
    /// No query outstanding.
    pub const fn new() -> Self {
        Self { items: [None; N] }
    }

    /// How many queries are outstanding.
    pub fn len(&self) -> usize {
        self.items.iter().flatten().count()
    }

    /// Whether none is.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Whether a query for `peer` is outstanding.
    pub fn contains(&self, peer: &NodeId) -> bool {
        self.items.iter().flatten().any(|i| i.peer == *peer)
    }

    /// Ask for `peer` at `now`. `udp_any` says a UDP datagram was ever heard; `carrier_open` that the home carrier is
    /// open. `thin` is the node's round trip when the node is thin, else `None`: a repeat then waits for twice that
    /// (at most [`THIN_WAIT_MAX_NS`]) if longer than [`RETRY_NS`]. Returns how to send, or [`Ask::Skip`] when the
    /// previous query is still inside its wait.
    pub fn ask(&mut self, now: u64, peer: &NodeId, udp_any: bool, carrier_open: bool, thin: Option<u64>) -> Ask {
        let at = match self.items.iter().position(|i| i.is_some_and(|i| i.peer == *peer)) {
            Some(p) => p,
            None => match self.items.iter().position(Option::is_none) {
                Some(p) => p,
                None => return Ask::Skip,
            },
        };
        let Some(slot) = self.items.get_mut(at) else {
            return Ask::Skip;
        };
        let mut item = slot.unwrap_or(Item {
            peer: *peer,
            at: 0,
            tried: false,
            carrier_only: false,
            again: false,
            wait: RETRY_NS,
        });
        if slot.is_some() && !item.again && now < item.at.saturating_add(item.wait) {
            return Ask::Skip;
        }
        item.again = false;
        item.wait = RETRY_NS.max(thin.map_or(0, |r| THIN_WAIT_MAX_NS.min(r.saturating_mul(2))));
        let retry = item.tried;
        item.tried = true;
        item.at = now;
        let by_carrier = !udp_any || item.carrier_only;
        let out = if by_carrier {
            item.at = now.saturating_add(CARRIER_WAIT_NS - RETRY_NS);
            if carrier_open {
                Ask::Carrier
            } else if retry {
                Ask::Later
            } else {
                // The first query goes over UDP even from a dark node: the answer may still come, and a carrier
                // that opens later asks again after the wait.
                item.at = now;
                Ask::Udp { others: false }
            }
        } else {
            Ask::Udp { others: retry }
        };
        *slot = Some(item);
        out
    }

    /// The answer for `peer` arrived (or was refused): forget the query.
    pub fn answered(&mut self, peer: &NodeId) {
        for s in &mut self.items {
            if s.is_some_and(|i| i.peer == *peer) {
                *s = None;
            }
        }
    }

    /// The answer was too large for a datagram: ask again over the carrier from now on.
    pub fn too_large(&mut self, peer: &NodeId) {
        for i in self.items.iter_mut().flatten() {
            if i.peer == *peer {
                i.carrier_only = true;
                i.again = true;
            }
        }
    }

    /// Forget every query (a carrier was reset); waiting dials ask again.
    pub fn clear(&mut self) {
        self.items = [None; N];
    }

    /// The peers whose query has waited past its time at `now`, oldest slot first.
    pub fn due(&self, now: u64) -> impl Iterator<Item = NodeId> + '_ {
        self.items
            .iter()
            .flatten()
            .filter(move |i| now > i.at.saturating_add(i.wait))
            .map(|i| i.peer)
    }

    /// The first instant a query becomes due.
    pub fn next_deadline(&self) -> Option<u64> {
        self.items
            .iter()
            .flatten()
            .map(|i| i.at.saturating_add(i.wait).saturating_add(1))
            .min()
    }
}

/// A verified record, copied out of the answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Found {
    /// The peer's home relay.
    pub home: NodeId,
    /// The reachability class the peer published.
    pub reach: Reach,
    /// The record's sequence number.
    pub seq: u64,
    addrs: [Option<SocketAddr>; MAX_ADDRS],
    hints: [u8; MAX_HINT_LEN],
    hint_len: u8,
}

impl Found {
    /// The ticket hints the peer published, at most [`MAX_HINT_LEN`] bytes.
    pub fn hints(&self) -> &[u8] {
        self.hints.get(..usize::from(self.hint_len)).unwrap_or_default()
    }

    /// The peer's addresses.
    pub fn addrs(&self) -> impl Iterator<Item = SocketAddr> + '_ {
        self.addrs.iter().flatten().copied()
    }
}

/// Why an answer was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LookupError {
    /// The record is malformed or its signature does not verify.
    Record(RecordError),
    /// The record belongs to another node than the one asked about.
    WrongNode,
    /// The relay holds a record that did not fit a datagram: ask again over the carrier.
    TooLarge,
}

/// Check an answer to a query for `peer`. `Ok(None)` means the relay holds no record.
///
/// # Errors
/// [`LookupError`]; the answer is not used.
pub fn verify(peer: &NodeId, answer: &DnsAnswer<'_>) -> Result<Option<Found>, LookupError> {
    match answer {
        DnsAnswer::Absent => Ok(None),
        DnsAnswer::TooLarge => Err(LookupError::TooLarge),
        DnsAnswer::Record(bytes) => {
            let r = Record::parse_verified(bytes).map_err(LookupError::Record)?;
            if r.node != *peer {
                return Err(LookupError::WrongNode);
            }
            let mut addrs = [None; MAX_ADDRS];
            for (d, a) in addrs.iter_mut().zip(r.addrs()) {
                *d = Some(a);
            }
            let mut hints = [0u8; MAX_HINT_LEN];
            let hint_len = r.hints.len().min(MAX_HINT_LEN);
            if let (Some(d), Some(s)) = (hints.get_mut(..hint_len), r.hints.get(..hint_len)) {
                d.copy_from_slice(s);
            }
            Ok(Some(Found {
                home: r.home,
                reach: r.reach,
                seq: r.seq,
                addrs,
                hints,
                hint_len: u8::try_from(hint_len).unwrap_or(0),
            }))
        }
    }
}
