//! What survives a restart: the resumption tickets, the round trips and prekey caches the endpoint keeps per peer, and
//! the address book.
//!
//! The host stores the bytes [`export_state`](Core::export_state) makes and gives them back to a restarted endpoint
//! with [`restore_state`](Core::restore_state); the first dial to a peer from before the restart then resumes its
//! session, with data in the first flight. The bytes hold pre-shared keys: seal them with the identity's key store
//! before they reach a disk (`Endpoint::seal_state`).
//!
//! Format, all integers big-endian: `version(1) core_len(4) core addresses(2) { alg(1) node(32) n(1) { tag(1) ip(4 or 16)
//! port(2) } } record_seq(8)`, where `core` is the endpoint's own state (`vinc-core`) and `record_seq` is the sequence
//! number of the last record the node published, which keeps the numbers rising across a restart. Version 1 is the same
//! without `record_seq`; it is still read, and a restore from it leaves the number as it is.
//!
//! Invariants: restoring bytes that are not exactly one well-formed state changes nothing; the address book never holds
//! more than [`BOOK_MAX`] nodes or eight addresses of one.

use std::net::{IpAddr, SocketAddr};

use vinc_core::state_len;
use vinc_crypto::{IdentityAlg, NodeId};
use vinc_keystore::KeyStore;

use super::{Admit, Core};
use crate::error::{Error, Result};
use crate::mem::CLIENT_TICKETS;

/// The state format version written. Version 1, without the record number, is still read.
const VERSION: u8 = 2;
/// The format before the record number.
const VERSION_1: u8 = 1;
/// The most nodes the address book holds.
pub(crate) const BOOK_MAX: usize = 4096;
/// The most addresses kept for one node.
pub(crate) const ADDRS_MAX: usize = 8;

/// What a restore loaded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Restored {
    /// Resumption tickets stored.
    pub tickets: usize,
    /// Peers with a remembered handshake round trip.
    pub peers: usize,
    /// Peers known to cache this node's prekey.
    pub prekeys: usize,
    /// Nodes whose addresses went into the address book.
    pub addresses: usize,
}

fn put_addr(out: &mut Vec<u8>, a: &SocketAddr) {
    match a.ip() {
        IpAddr::V4(ip) => {
            out.push(4);
            out.extend_from_slice(&ip.octets());
        }
        IpAddr::V6(ip) => {
            out.push(6);
            out.extend_from_slice(&ip.octets());
        }
    }
    out.extend_from_slice(&a.port().to_be_bytes());
}

/// A cursor over the bytes of a state.
struct Cursor<'a>(&'a [u8]);

impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        Some(head)
    }

    fn u8(&mut self) -> Option<u8> {
        self.take(1)?.first().copied()
    }

    fn array<const N: usize>(&mut self) -> Option<[u8; N]> {
        self.take(N)?.try_into().ok()
    }

    fn addr(&mut self) -> Option<SocketAddr> {
        let ip: IpAddr = match self.u8()? {
            4 => self.array::<4>()?.into(),
            6 => self.array::<16>()?.into(),
            _ => return None,
        };
        Some(SocketAddr::new(ip, u16::from_be_bytes(self.array()?)))
    }
}

/// The address book as a state holds it: each node with its addresses.
type Book = Vec<(NodeId, Vec<SocketAddr>)>;

/// The state split into its parts, every part checked: the core's bytes, the address book and the last record's number
/// (absent in version 1).
fn parse(bytes: &[u8]) -> Option<(&[u8], Book, Option<u64>)> {
    let mut c = Cursor(bytes);
    let version = c.u8()?;
    if version != VERSION && version != VERSION_1 {
        return None;
    }
    let len = usize::try_from(u32::from_be_bytes(c.array()?)).ok()?;
    let core = c.take(len)?;
    let count = usize::from(u16::from_be_bytes(c.array()?));
    if count > BOOK_MAX {
        return None;
    }
    let mut book = Vec::with_capacity(count);
    for _ in 0..count {
        let alg = IdentityAlg::from_tag(c.u8()?)?;
        let node = NodeId { alg, bytes: c.array()? };
        let n = usize::from(c.u8()?);
        if n > ADDRS_MAX {
            return None;
        }
        let addrs = (0..n).map(|_| c.addr()).collect::<Option<Vec<_>>>()?;
        book.push((node, addrs));
    }
    let seq = if version == VERSION {
        Some(u64::from_be_bytes(c.array()?))
    } else {
        None
    };
    c.0.is_empty().then_some((core, book, seq))
}

impl<S: KeyStore, A: Admit> Core<S, A> {
    /// The state to store across a restart.
    pub(crate) fn export_state(&mut self, now: u64) -> Result<Vec<u8>> {
        let mut core = vec![0u8; state_len(CLIENT_TICKETS)];
        let n = self
            .node
            .endpoint()
            .export_state(now, &mut core)
            .map_err(|_| Error::config("the state does not fit its buffer"))?;
        let mut out = Vec::with_capacity(8 + n);
        out.push(VERSION);
        out.extend_from_slice(
            &u32::try_from(n)
                .map_err(|_| Error::config("the state is too large"))?
                .to_be_bytes(),
        );
        out.extend_from_slice(core.get(..n).unwrap_or_default());
        let entries: Vec<_> = self.book.iter().take(BOOK_MAX).collect();
        out.extend_from_slice(&u16::try_from(entries.len()).unwrap_or(u16::MAX).to_be_bytes());
        for (node, addrs) in entries {
            out.push(node.alg.tag());
            out.extend_from_slice(&node.bytes);
            out.push(u8::try_from(addrs.len().min(ADDRS_MAX)).unwrap_or(0));
            for a in addrs.iter().take(ADDRS_MAX) {
                put_addr(&mut out, a);
            }
        }
        out.extend_from_slice(&self.node.connectivity().record_seq().to_be_bytes());
        Ok(out)
    }

    /// Load state made by [`export_state`](Self::export_state); nothing changes if it is not exactly one state.
    pub(crate) fn restore_state(&mut self, now: u64, bytes: &[u8]) -> Result<Restored> {
        let bad = || Error::config("the bytes are not a state of this endpoint");
        let (core, book, seq) = parse(bytes).ok_or_else(bad)?;
        let r = self.node.endpoint_mut().restore_state(now, core).map_err(|_| bad())?;
        if let Some(seq) = seq {
            self.node.restore_record_seq(seq);
        }
        let addresses = book.len();
        for (node, addrs) in book {
            for a in addrs {
                self.add_address(node, a);
            }
        }
        Ok(Restored {
            tickets: r.tickets,
            peers: r.peers,
            prekeys: r.prekeys,
            addresses,
        })
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn a_state_with_a_wrong_version_a_cut_or_extra_byte_is_not_parsed() {
        let mut ok = vec![VERSION_1, 0, 0, 0, 0, 0, 0];
        assert!(parse(&ok).is_some());
        assert!(parse(&ok[..ok.len() - 1]).is_none());
        ok.push(0);
        assert!(parse(&ok).is_none());
        assert!(parse(&[VERSION + 1, 0, 0, 0, 0, 0, 0]).is_none());
        // One address of an unknown family.
        let mut book = vec![VERSION_1, 0, 0, 0, 0, 0, 1, IdentityAlg::Ed25519.tag()];
        book.extend_from_slice(&[0; 32]);
        book.extend_from_slice(&[1, 9, 0, 0, 0, 0, 0]);
        assert!(parse(&book).is_none());
    }

    #[test]
    fn an_address_book_entry_round_trips() {
        let a: SocketAddr = "[2001:db8::1]:4433".parse().unwrap();
        let b: SocketAddr = "10.1.2.3:9".parse().unwrap();
        let mut bytes = vec![VERSION_1, 0, 0, 0, 0, 0, 1, IdentityAlg::Ed25519.tag()];
        bytes.extend_from_slice(&[7; 32]);
        bytes.push(2);
        put_addr(&mut bytes, &a);
        put_addr(&mut bytes, &b);
        let (core, book, seq) = parse(&bytes).unwrap();
        assert_eq!(seq, None);
        assert_eq!(core, &[] as &[u8]);
        assert_eq!(book.len(), 1);
        assert_eq!(book[0].1, vec![a, b]);
        assert_eq!(book[0].0.alg, IdentityAlg::Ed25519);
    }

    #[test]
    fn the_record_number_is_read_from_a_current_state_and_absent_from_the_old_one() {
        let mut v2 = vec![VERSION, 0, 0, 0, 0, 0, 0];
        v2.extend_from_slice(&41u64.to_be_bytes());
        assert_eq!(parse(&v2).unwrap().2, Some(41));
        assert!(parse(&v2[..v2.len() - 1]).is_none());
        // A current state without the number is cut short, and an old one with it has trailing bytes.
        assert!(parse(&[VERSION, 0, 0, 0, 0, 0, 0]).is_none());
        let mut v1 = vec![VERSION_1, 0, 0, 0, 0, 0, 0];
        v1.extend_from_slice(&41u64.to_be_bytes());
        assert!(parse(&v1).is_none());
    }
}
