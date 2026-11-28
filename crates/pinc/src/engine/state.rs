//! What survives a restart: the resumption tickets, the round trips and prekey caches the endpoint keeps per peer, and
//! the address book.
//!
//! The host stores the bytes [`export_state`](Core::export_state) makes and gives them back to a restarted endpoint
//! with [`restore_state`](Core::restore_state); the first dial to a peer from before the restart then resumes its
//! session, with data in the first flight. The bytes hold pre-shared keys: seal them with the identity's key store
//! before they reach a disk (`Endpoint::seal_state`).
//!
//! Format, all integers big-endian: `version(1) core_len(4) core addresses(2) { alg(1) node(32) n(1) { tag(1) ip(4 or 16)
//! port(2) } } record_seq(8)`, where `core` is the endpoint's own state (`pinc-core`) and `record_seq` is the sequence
//! number of the last record the node published, which keeps the numbers rising across a restart. Version 1 is the same
//! without `record_seq`; it is still read, and a restore from it leaves the number as it is.
//!
//! Invariants: restoring bytes that are not exactly one well-formed state changes nothing; the address book never holds
//! more than [`BOOK_MAX`] nodes or eight addresses of one.

use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;
use core::net::{IpAddr, SocketAddr};

use pinc_core::state_len;
use pinc_crypto::{IdentityAlg, NodeId};
use pinc_keystore::KeyStore;

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
    /// Resumption tickets of the input the client store holds after the restore (one replaced or evicted by a later
    /// one of the same input is not counted).
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
        // Every address is offered (`|` does not short-circuit); a node counts once if the book kept one of them,
        // however many entries of the state name it. The set holds at most one key per entry of the state.
        let mut counted = BTreeSet::new();
        for (node, addrs) in book {
            if addrs.iter().fold(false, |kept, a| self.add_address(node, *a) | kept) {
                counted.insert((node.alg.tag(), node.bytes));
            }
        }
        let addresses = counted.len();
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

    use alloc::collections::BTreeSet;
    use alloc::format;
    use alloc::string::String;
    use core::fmt::Write as _;

    use crate::engine::adjacent_tests::{C, core as new_core};
    use crate::trace_util::{below, jb, mix, write_trace};

    const NOW: u64 = 1_000_000;

    fn node_of(i: u8) -> NodeId {
        NodeId {
            alg: IdentityAlg::Ed25519,
            bytes: [i; 32],
        }
    }

    fn v4(i: u8) -> SocketAddr {
        SocketAddr::new(IpAddr::from([10, 0, 0, i]), 4433)
    }

    fn v6(i: u16) -> SocketAddr {
        SocketAddr::new(IpAddr::from([0x2001, 0xdb8, 0, 0, 0, 0, 0, i]), 9)
    }

    /// A state as its parts, so a source can break a bound the encoder keeps.
    #[derive(Clone)]
    struct Src {
        len: u32,
        core: Vec<u8>,
        count: u16,
        entries: Vec<u8>,
        seq: u64,
    }

    impl Src {
        fn of(core: &[u8], book: &Book, seq: u64) -> Self {
            let mut entries = Vec::new();
            for (node, addrs) in book {
                let a: Vec<u8> = addrs.iter().flat_map(addr_bytes).collect();
                entries.extend(entry(
                    node.alg.tag(),
                    node.bytes,
                    u8::try_from(addrs.len()).unwrap(),
                    &a,
                ));
            }
            Self {
                len: u32::try_from(core.len()).unwrap(),
                core: core.to_vec(),
                count: u16::try_from(book.len()).unwrap(),
                entries,
                seq,
            }
        }

        fn bytes(&self, version: u8) -> Vec<u8> {
            let mut o = vec![version];
            o.extend_from_slice(&self.len.to_be_bytes());
            o.extend_from_slice(&self.core);
            o.extend_from_slice(&self.count.to_be_bytes());
            o.extend_from_slice(&self.entries);
            if version == VERSION {
                o.extend_from_slice(&self.seq.to_be_bytes());
            }
            o
        }
    }

    fn addr_bytes(a: &SocketAddr) -> Vec<u8> {
        let mut b = Vec::new();
        put_addr(&mut b, a);
        b
    }

    fn entry(tag: u8, node: [u8; 32], n: u8, addrs: &[u8]) -> Vec<u8> {
        let mut e = vec![tag];
        e.extend_from_slice(&node);
        e.push(n);
        e.extend_from_slice(addrs);
        e
    }

    /// The core's own state in the layout of `CoreStateOps.Enc`: no tickets, one round trip of 5 to `[7; 32]`.
    fn core_with_round_trip() -> Vec<u8> {
        let mut c = vec![1, 0, 0, 0, 2, 1, 0, 0, 1, 1];
        c.extend_from_slice(&[7; 32]);
        c.extend_from_slice(&5u64.to_be_bytes());
        c.extend_from_slice(&[0, 0]);
        c
    }

    fn live(kind: usize) -> C {
        let mut c = new_core();
        match kind {
            1 => {
                let src = Src::of(&core_with_round_trip(), &vec![(node_of(3), vec![v4(1), v6(1)])], 5);
                c.restore_state(NOW, &src.bytes(VERSION)).unwrap();
            }
            2 => {
                for i in 0..8 {
                    assert!(c.add_address(node_of(4), v4(i)));
                }
                assert!(c.add_address(node_of(5), v4(1)));
                c.node.restore_record_seq(u64::MAX - 1);
            }
            _ => {}
        }
        c
    }

    fn jbook(book: &Book) -> String {
        let rows: Vec<String> = book
            .iter()
            .map(|(n, addrs)| {
                let a: Vec<String> = addrs.iter().map(|x| jb(&addr_bytes(x))).collect();
                format!(
                    r#"{{"alg":{},"bytes":{},"addrs":[{}]}}"#,
                    n.alg.tag(),
                    jb(&n.bytes),
                    a.join(",")
                )
            })
            .collect();
        format!("[{}]", rows.join(","))
    }

    /// A live state: the export, the book sorted by node and the record number.
    fn snap(c: &mut C) -> String {
        let export = c.export_state(NOW).unwrap();
        let (_, book, seq) = parse(&export).unwrap();
        assert_eq!(seq, Some(c.node.connectivity().record_seq()));
        let mut live: Book = c.book.iter().map(|(n, a)| (*n, a.clone())).collect();
        live.sort_by_key(|(n, _)| (n.alg.tag(), n.bytes));
        assert_eq!(book.len(), live.len());
        let seq = c.node.connectivity().record_seq().to_be_bytes();
        format!(
            r#"{{"export":{},"book":{},"seq":{}}}"#,
            jb(&export),
            jbook(&live),
            jb(&seq)
        )
    }

    fn sources() -> Vec<Src> {
        let mut out = Vec::new();
        let mut core0 = Vec::new();
        for kind in 0..3 {
            let export = live(kind).export_state(NOW).unwrap();
            let (core, book, seq) = parse(&export).unwrap();
            if kind == 0 {
                core0 = core.to_vec();
            }
            out.push(Src::of(core, &book, seq.unwrap()));
        }
        let one = vec![(node_of(1), vec![v4(1)])];
        let base = Src::of(&core0, &one, 0);
        let with = |f: &dyn Fn(&mut Src)| {
            let mut s = base.clone();
            f(&mut s);
            s
        };
        out.push(Src::of(&core0[..core0.len() - 1], &one, 0));
        out.push(Src::of(
            &core0,
            &vec![(node_of(1), vec![v4(1)]), (node_of(1), vec![v6(1)])],
            0,
        ));
        out.push(Src::of(&core0, &vec![(node_of(1), vec![v4(1), v4(1)])], 0));
        out.push(Src::of(&core0, &vec![(node_of(1), vec![])], 0));
        out.push(Src::of(&core0, &one, 3));
        out.push(Src::of(&core0, &one, u64::MAX));
        let nine: Book = (0..9u8)
            .map(|i| {
                (
                    node_of(i + 1),
                    if i == 0 { (0..8).map(v4).collect() } else { vec![v4(i)] },
                )
            })
            .collect();
        out.push(Src::of(&core0, &nine, 0));
        out.push(with(&|s| s.count = u16::try_from(BOOK_MAX + 1).unwrap()));
        out.push(with(&|s| s.count = u16::MAX));
        out.push(Src::of(&core0, &vec![(node_of(1), (0..9).map(v4).collect())], 0));
        for tag in [0, 5] {
            out.push(with(&|s| s.entries = entry(tag, [1; 32], 0, &[])));
        }
        for fam in [0, 5, 255] {
            out.push(with(&|s| s.entries = entry(1, [1; 32], 1, &[fam, 0, 0, 0, 0, 0, 9])));
        }
        for len in [u32::MAX, 0x8000_0000] {
            out.push(with(&|s| s.len = len));
        }
        out
    }

    /// Every input the spec derives from the sources, without repeats, and the random ones.
    fn inputs() -> Vec<Vec<u8>> {
        let mut set = BTreeSet::new();
        // Every source in the current format, and the three live ones in the old format too; a few cuts, one extra byte
        // and a changed byte at the start, the count and the end of each, so every refusal is still met and the file
        // stays small.
        for (k, src) in sources().into_iter().enumerate() {
            for version in [VERSION, VERSION_1].into_iter().take(if k < 3 { 2 } else { 1 }) {
                let bs = src.bytes(version);
                set.insert(bs.clone());
                for cut in [0, bs.len() - 1] {
                    set.insert(bs[..cut].to_vec());
                }
                set.insert([bs.clone(), vec![0]].concat());
                for i in [0, 4, bs.len() - 1] {
                    let mut m = bs.clone();
                    m[i] = bs[i].wrapping_add(1);
                    set.insert(m);
                }
            }
        }
        let mut seed = 7u64;
        for _ in 0..20 {
            let mut bs: Vec<u8> = (0..below(&mut seed, 80))
                .map(|_| mix(&mut seed).to_le_bytes()[0])
                .collect();
            if let Some(first) = bs.first_mut() {
                *first = u8::try_from(1 + below(&mut seed, 2)).unwrap();
            }
            set.insert(bs);
        }
        set.into_iter().collect()
    }

    fn parse_json(bs: &[u8]) -> String {
        match parse(bs) {
            None => r#"{"ok":false}"#.into(),
            Some((core, book, seq)) => format!(
                r#"{{"ok":true,"ver":{},"core":{},"book":{},"seq":{}}}"#,
                bs[0],
                jb(core),
                jbook(&book),
                seq.map_or_else(|| "[]".into(), |s| jb(&s.to_be_bytes()))
            ),
        }
    }

    /// Restores of every input into three live cores, and a full book, recorded with the live state around each.
    #[test]
    fn trace_state() {
        let mut out = String::new();
        let inputs = inputs();
        // Accepted in each format, and a good framing the core refused.
        let (mut v1, mut v2, mut refused) = (0, 0, 0);
        for kind in 0..3 {
            let mut c = live(kind);
            let mut before = snap(&mut c);
            for bs in &inputs {
                let r = c.restore_state(NOW, bs);
                let ok = r.is_ok();
                if parse(bs).is_none() {
                    assert!(!ok);
                } else if !ok {
                    refused += 1;
                } else if bs[0] == VERSION_1 {
                    v1 += 1;
                } else {
                    v2 += 1;
                }
                let after = snap(&mut c);
                if !ok {
                    assert_eq!(after, before, "a refused restore changed the state");
                }
                let res = r.map_or([0; 4], |r| [r.tickets, r.peers, r.prekeys, r.addresses]);
                writeln!(
                    out,
                    r#"{{"t":"state","op":"restore","bs":{},"parse":{},"ok":{},"res":{res:?},"before":{before},"after":{after}}}"#,
                    jb(bs),
                    parse_json(bs),
                    ok
                )
                .unwrap();
                if after != before {
                    c = live(kind);
                    before = snap(&mut c);
                }
            }
        }

        let mut c = new_core();
        for i in 0..BOOK_MAX {
            let mut bytes = [0u8; 32];
            bytes[..8].copy_from_slice(&u64::try_from(i).unwrap().to_be_bytes());
            let node = NodeId {
                alg: IdentityAlg::Ed25519,
                bytes,
            };
            assert!(c.add_address(node, v4(1)));
        }
        let core0 = parse(&live(0).export_state(NOW).unwrap()).unwrap().0.to_vec();
        let new: Book = (0..3u8).map(|i| (node_of(200 + i), vec![v4(i)])).collect();
        let r = c.restore_state(NOW, &Src::of(&core0, &new, 0).bytes(VERSION));
        let (ok, addresses) = (r.is_ok(), r.map_or(0, |r| r.addresses));
        let added = new.iter().filter(|(n, _)| c.book.contains_key(n)).count();
        assert_eq!((c.book.len(), added), (BOOK_MAX, 0));
        writeln!(
            out,
            r#"{{"t":"state","op":"full","before":{BOOK_MAX},"after":{},"ok":{ok},"added":{added},"addresses":{addresses}}}"#,
            c.book.len()
        )
        .unwrap();
        assert!(
            v1 > 0 && v2 > 0 && refused > 0,
            "a branch was not met: {v1} {v2} {refused}"
        );
        assert_eq!(addresses, 0, "a full book kept an address");
        assert!(out.len() < 2_000_000, "the trace is {} bytes", out.len());
        write_trace("facade_state.ndjson", &out);
    }
}
