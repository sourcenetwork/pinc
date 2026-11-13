//! What a VINC node program tells the orchestrator about its delay-tolerant layer: every event and trace record of a
//! bundle, by bundle tag and peer name, and the payloads it makes and checks.
//!
//! A payload is the shape of a `DefraDB` document update for a peer: its first eight bytes are its content seed, the rest
//! is the content that seed makes, so the destination checks it without being told anything.
//!
//! Invariants: an entry names peers by their scenario names (an unknown peer by its tag); a payload is intact only if
//! every byte is the one its seed makes.

use std::collections::BTreeMap;

use vinc_node::trace::{btag, tag};
use vinc_node::{NodeEvent, NodeTrace};

use super::core::node_id;
use crate::node::data::Content;
use crate::node::proto::{DtnEntry, DtnWhat};

/// The payload of `size` bytes (at least 8) made from `seed`.
pub fn payload(seed: u64, size: u64) -> Vec<u8> {
    let n = usize::try_from(size).unwrap_or(0).max(8);
    let mut v = vec![0u8; n];
    if let Some((head, rest)) = v.split_first_chunk_mut::<8>() {
        *head = seed.to_le_bytes();
        Content::new(seed, size).fill(8, rest);
    }
    v
}

fn intact(p: &[u8]) -> bool {
    p.first_chunk::<8>()
        .is_some_and(|s| payload(u64::from_le_bytes(*s), p.len() as u64) == p)
}

/// The name of a refusal code of the delay-tolerant wire.
fn refusal(code: u64) -> String {
    match code {
        1 => "malformed",
        2 => "expired",
        3 => "no-room",
        4 => "bad-proof",
        5 => "inconsistent",
        6 => "cannot-open",
        7 => "no-signer",
        8 => "busy",
        _ => "unknown",
    }
    .into()
}

/// The log of one node.
pub struct DtnLog {
    names: BTreeMap<u64, String>,
    /// Every entry, in order.
    pub log: Vec<DtnEntry>,
    /// Trace records the node dropped.
    pub lost: u64,
}

impl DtnLog {
    /// A log that names the scenario's nodes `peers`.
    pub fn new<'a>(peers: impl Iterator<Item = &'a str>) -> Self {
        let names = peers
            .filter_map(|n| node_id(n).ok().map(|id| (tag(&id.bytes), n.to_owned())))
            .collect();
        Self {
            names,
            log: Vec::new(),
            lost: 0,
        }
    }

    fn name(&self, t: u64) -> String {
        self.names.get(&t).cloned().unwrap_or_else(|| format!("{t:08x}"))
    }

    fn push(&mut self, ms: u64, bundle: u64, what: DtnWhat) {
        self.log.push(DtnEntry {
            ms,
            bundle: format!("{bundle:016x}"),
            what,
        });
    }

    /// A trace record of the layer.
    pub fn trace(&mut self, ms: u64, t: NodeTrace) {
        let (bundle, what) = match t {
            NodeTrace::DtnCreated { bundle, copies } => (bundle, DtnWhat::Created { copies }),
            NodeTrace::DtnOffer { bundle, peer, copies } => (
                bundle,
                DtnWhat::Offer {
                    peer: self.name(peer),
                    copies,
                },
            ),
            NodeTrace::DtnSymbols { bundle, peer, first } => (
                bundle,
                DtnWhat::Symbols {
                    peer: self.name(peer),
                    first,
                },
            ),
            NodeTrace::DtnLost { bundle, peer, symbol } => (
                bundle,
                DtnWhat::Lost {
                    peer: self.name(peer),
                    symbol,
                },
            ),
            NodeTrace::DtnParity { bundle, peer, symbols } => (
                bundle,
                DtnWhat::Parity {
                    peer: self.name(peer),
                    symbols,
                },
            ),
            NodeTrace::DtnComplete { bundle, peer } => (bundle, DtnWhat::Complete { peer: self.name(peer) }),
            NodeTrace::DtnCustody { bundle, peer } => (bundle, DtnWhat::Custody { peer: self.name(peer) }),
            NodeTrace::DtnAcked { bundle, peer, relieved } => (
                bundle,
                DtnWhat::Acked {
                    peer: self.name(peer),
                    relieved: relieved == 1,
                },
            ),
            NodeTrace::DtnRefused { bundle, peer, reason } => (
                bundle,
                DtnWhat::Refused {
                    peer: self.name(peer),
                    reason: refusal(reason),
                },
            ),
            NodeTrace::DtnReleased { bundle, delivered } => (
                bundle,
                DtnWhat::Released {
                    delivered: delivered == 1,
                },
            ),
            NodeTrace::Lost { count } => {
                self.lost += count;
                return;
            }
            _ => return,
        };
        self.push(ms, bundle, what);
    }

    /// An application event of the layer; other events are ignored.
    pub fn event(&mut self, ms: u64, ev: &NodeEvent) {
        let (bundle, what) = match ev {
            NodeEvent::DtnReceived {
                bundle,
                source,
                payload,
            } => (
                bundle,
                DtnWhat::Received {
                    source: self.name(tag(source)),
                    intact: intact(payload),
                    bytes: payload.len() as u64,
                },
            ),
            NodeEvent::DtnHandedOff { bundle, to } => (bundle, DtnWhat::HandedOff { to: self.name(tag(to)) }),
            NodeEvent::DtnDelivered { bundle } => (bundle, DtnWhat::Delivered),
            NodeEvent::DtnExpired { bundle } => (bundle, DtnWhat::Expired),
            _ => return,
        };
        self.push(ms, btag(bundle), what);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_payload_is_checked_from_its_own_bytes() {
        let mut p = payload(7, 4096);
        assert_eq!(p.len(), 4096);
        assert!(intact(&p));
        if let Some(b) = p.get_mut(2000) {
            *b ^= 1;
        }
        assert!(!intact(&p));
    }
}
