//! WHOLE_GROUP: a group is hashed once all of its bytes are buffered, not as each packet of it arrives.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    missing_docs,
    reason = "tests assert freely"
)]

extern crate std;

use core::ops::Range;
use std::vec;
use std::vec::Vec;

use pinc_dag::ranges::VerifiedRanges;
use pinc_dag::tree::{Layout, build_outboard};
use pinc_transport::stream::{StreamId, StreamSource};

use super::super::{Fetch, FetchSpec, In, Io};
use crate::knobs::{GROUP, GROUP_BYTES, GROUP_LOG};
use crate::session::{OpenError, Outbound, PeerInfo, Provider, Session};
use crate::source::ValueSource;
use crate::store::{StoreError, ValueRead, ValueStore, verified_after};

/// The datagram payload the stream bytes arrive in.
const PACKET: usize = 1200;
/// The transport keeps received bytes in chunks of this size, so a read never crosses a multiple of it.
const RING: u64 = 16 * 1024;
/// The request stream the fetch opens.
const STREAM: StreamId = 7;

/// A session holding one response stream, of which the first `avail` bytes have arrived.
#[derive(Default)]
struct Net {
    bytes: Vec<u8>,
    avail: u64,
    connected: bool,
}

impl Session for Net {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, stream: StreamId, from: u64, mut f: F) {
        let mut at = from;
        while stream == STREAM && at < self.avail {
            let end = self.avail.min((at / RING + 1) * RING);
            let piece = &self.bytes[at as usize..end as usize];
            let n = f(piece);
            at += n as u64;
            if n < piece.len() {
                break;
            }
        }
    }
    fn has(&self, stream: StreamId, from: u64, len: u64) -> bool {
        stream == STREAM && from + len <= self.avail
    }
    fn consume(&mut self, _: StreamId, _: u64) {}
    fn write(&mut self, _: StreamId, _: &[u8], _: bool) -> bool {
        true
    }
    fn reset(&mut self, _: StreamId, _: u64) {}
    fn send_ext(&mut self, _: StreamId, _: u64, _: &[u8]) -> bool {
        true
    }
}

impl Outbound for Net {
    fn is_connected(&self, _: Provider) -> bool {
        self.connected
    }
    fn dial(&mut self, _: Provider) {}
    fn hangup(&mut self, _: Provider) {}
    fn open_stream(&mut self, _: Provider, _: u8) -> Result<StreamId, OpenError> {
        Ok(STREAM)
    }
    fn peer_info(&self, _: Provider) -> Option<PeerInfo> {
        None
    }
}

/// The provider's side: the value and its outboard.
struct Served<'a> {
    value: &'a [u8],
    outboard: &'a [u8],
}

impl ValueRead for Served<'_> {
    fn servable_len(&self, _: &[u8; 32]) -> Option<u64> {
        Some(self.value.len() as u64)
    }
    fn read_at(&self, _: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let src = self.value.get(offset as usize..).unwrap_or_default();
        let n = src.len().min(dst.len());
        dst[..n].copy_from_slice(&src[..n]);
        n
    }
    fn read_outboard(&self, _: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let src = self.outboard.get(offset as usize..).unwrap_or_default();
        let n = src.len().min(dst.len());
        dst[..n].copy_from_slice(&src[..n]);
        n
    }
}

/// The fetching side's store.
#[derive(Default)]
struct Got {
    data: Vec<u8>,
    verified: VerifiedRanges<64>,
}

impl ValueRead for Got {
    fn servable_len(&self, _: &[u8; 32]) -> Option<u64> {
        None
    }
    fn read_at(&self, _: &[u8; 32], _: u64, _: &mut [u8]) -> usize {
        0
    }
    fn read_outboard(&self, _: &[u8; 32], _: u64, _: &mut [u8]) -> usize {
        0
    }
}

impl ValueStore for Got {
    fn verified_from(&self, _: &[u8; 32], from: u64) -> Option<Range<u64>> {
        verified_after(&self.verified, from)
    }
    fn write_at(&mut self, _: &[u8; 32], offset: u64, data: &[u8]) -> Result<(), StoreError> {
        let end = offset as usize + data.len();
        if self.data.len() < end {
            self.data.resize(end, 0);
        }
        self.data[offset as usize..end].copy_from_slice(data);
        Ok(())
    }
    fn commit(&mut self, _: &[u8; 32], range: Range<u64>) -> Result<(), StoreError> {
        Ok(self.verified.insert(range)?)
    }
}

/// Bytes verified from the start of the value.
fn verified(got: &Got) -> u64 {
    verified_after(&got.verified, 0)
        .filter(|r| r.start == 0)
        .map_or(0, |r| r.end)
}

/// A value of nine groups whose response arrives one packet at a time: each group is hashed in at most two calls (one
/// per receive chunk it lies in), never once per packet, and every byte still reaches the store verified.
#[test]
fn a_group_is_hashed_once_it_is_whole_not_once_per_packet() {
    let len = 9 * GROUP - 100;
    let value: Vec<u8> = (0..len).map(|i| (i * 31 % 251) as u8).collect();
    let mut outboard = vec![0u8; Layout::new(len, GROUP_LOG).unwrap().outboard_size() as usize];
    let root = build_outboard(&value, GROUP_LOG, &mut outboard).unwrap();

    let (mut net, mut got, mut out) = (Net::default(), Got::default(), ());
    let mut f = Fetch::new();
    let spec = FetchSpec {
        root,
        length: len,
        ranges: &[],
        providers: &[Provider(0)],
        deadline: None,
    };
    {
        let mut io = Io {
            session: &mut net,
            store: &mut got,
            out: &mut out,
        };
        f.start(&mut io, 0, &spec).unwrap();
        io.session.connected = true;
        f.on_event(&mut io, 0, &In::Connected(Provider(0)));
    }
    let plan = f.rx.iter().flatten().next().unwrap().plan.clone();
    let mut bytes = vec![0u8; plan.total() as usize];
    let served = Served {
        value: &value,
        outboard: &outboard,
    };
    assert_eq!(
        ValueSource::new(&served, root, plan).read_at(0, &mut bytes),
        bytes.len()
    );
    net.bytes = bytes;

    let deliver = |f: &mut Fetch, net: &mut Net, got: &mut Got| {
        assert!(
            net.avail < net.bytes.len() as u64,
            "every byte arrived and the fetch is not done"
        );
        net.avail = (net.avail + PACKET as u64).min(net.bytes.len() as u64);
        let mut io = Io {
            session: net,
            store: got,
            out: &mut (),
        };
        f.on_event(
            &mut io,
            0,
            &In::Readable {
                stream: STREAM,
                bytes: PACKET,
            },
        );
    };
    while verified(&got) < 8 * GROUP {
        deliver(&mut f, &mut net, &mut got);
    }
    let rx = f.rx.iter().flatten().next().unwrap();
    assert!(
        rx.feeds <= 2 * 8,
        "eight groups of {GROUP_BYTES} bytes arrived in {PACKET}-byte packets and were hashed in {} calls",
        rx.feeds
    );

    while !f.is_done() {
        deliver(&mut f, &mut net, &mut got);
    }
    assert_eq!(verified(&got), len);
    assert_eq!(got.data, value);
}
