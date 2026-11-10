//! Unit tests of the scheduler that need the private state of a [`Fetch`]: the steal on states the harness cannot reach.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    missing_docs,
    reason = "tests assert freely"
)]

use super::super::{Io, Prov};
use super::*;
use crate::knobs::NS;
use crate::session::{OpenError, PeerInfo, Provider};
use crate::store::{StoreError, ValueRead};
use core::ops::Range;
use vinc_transport::stream::StreamId;

/// A session that only counts what the steal does to streams.
#[derive(Default)]
struct Net {
    resets: usize,
    opened: u64,
}

impl Session for Net {
    fn visit<F: FnMut(&[u8]) -> usize>(&mut self, _: StreamId, _: u64, _: F) {}
    fn has(&self, _: StreamId, _: u64, _: u64) -> bool {
        false
    }
    fn consume(&mut self, _: StreamId, _: u64) {}
    fn write(&mut self, _: StreamId, _: &[u8], _: bool) -> bool {
        true
    }
    fn reset(&mut self, _: StreamId, _: u64) {
        self.resets += 1;
    }
    fn send_ext(&mut self, _: StreamId, _: u64, _: &[u8]) -> bool {
        true
    }
}

impl Outbound for Net {
    fn is_connected(&self, _: Provider) -> bool {
        true
    }
    fn dial(&mut self, _: Provider) {}
    fn hangup(&mut self, _: Provider) {}
    fn open_stream(&mut self, _: Provider, _: u8) -> Result<StreamId, OpenError> {
        self.opened += 1;
        Ok(100 + self.opened)
    }
    fn peer_info(&self, _: Provider) -> Option<PeerInfo> {
        None
    }
}

/// A store with nothing verified.
struct Empty;

impl ValueRead for Empty {
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

impl ValueStore for Empty {
    fn verified_from(&self, _: &[u8; 32], _: u64) -> Option<Range<u64>> {
        None
    }
    fn write_at(&mut self, _: &[u8; 32], _: u64, _: &[u8]) -> Result<(), StoreError> {
        Ok(())
    }
    fn commit(&mut self, _: &[u8; 32], _: Range<u64>) -> Result<(), StoreError> {
        Ok(())
    }
}

struct Sink;

impl Out for Sink {
    fn event(&mut self, _: u64, _: Event) {}
}

/// Two providers, 10 s into a fetch of a 16 MiB value: provider 1 holds 16 groups and has verified `victim_bytes`
/// since its first group, provider 0 holds nothing and has verified `thief_bytes`. Provider 1 has one open stream.
fn world(victim_bytes: u64, thief_bytes: u64) -> Fetch {
    let mut f = Fetch::new();
    f.state = State::Running;
    f.striped = true;
    f.nprov = 2;
    f.length = 1 << 24;
    let held = 16 * GROUP;
    f.provs[0] = Prov {
        in_provs: true,
        in_assign: true,
        conn: true,
        pt: Some(0),
        pb: thief_bytes,
        lp: Some(9 * NS),
        ..Prov::new(Provider(0))
    };
    f.provs[1] = Prov {
        in_provs: true,
        in_assign: true,
        conn: true,
        pt: Some(0),
        pb: victim_bytes,
        lp: Some(9 * NS),
        ..Prov::new(Provider(1))
    };
    f.provs[1].assign.push(Span { off: 0, len: held });
    let plan = Plan::new(f.length, &[Span { off: 0, len: held }]).unwrap();
    f.rx[0] = Some(Rx::new(1, 7, plan, &f.root));
    f
}

/// A thief 327 times slower than the victim: the victim holds 801 ms of work, so it is a candidate, but `keep` rounds
/// up to the whole list. Nothing moves, so the victim's stream must not be reset and the request not repeated.
#[test]
fn a_steal_that_would_move_nothing_leaves_the_victim_alone() {
    let mut f = world(327 * 10_000, 10_000);
    let (mut net, mut st, mut out) = (Net::default(), Empty, Sink);
    let mut io = Io {
        session: &mut net,
        store: &mut st,
        out: &mut out,
    };
    let new = f.steal(&mut io, 10 * NS, 0);
    assert!(new.is_empty());
    assert_eq!(net.resets, 0, "the victim's stream was reset for nothing");
    assert_eq!(net.opened, 0, "the victim's work was requested again for nothing");
    assert!(f.rx[0].is_some());
    assert_eq!(f.provs[1].assign.total(), 16 * GROUP);
    assert!(f.tw > 10 * NS, "the steal is looked at again later");
}

/// The same victim and a thief as fast: the tail moves, the victim's stream is reset and its head requested again.
#[test]
fn a_steal_moves_the_tail_of_a_slow_victim_to_a_fast_thief() {
    let mut f = world(327 * 10_000, 327 * 10_000);
    let (mut net, mut st, mut out) = (Net::default(), Empty, Sink);
    let mut io = Io {
        session: &mut net,
        store: &mut st,
        out: &mut out,
    };
    let new = f.steal(&mut io, 10 * NS, 0);
    assert_eq!(new.total(), 8 * GROUP);
    assert_eq!(f.provs[1].assign.total(), 8 * GROUP);
    assert_eq!(net.resets, 1);
    assert!(f.rx[0].is_none() || f.rx.iter().flatten().all(|r| r.stream != 7));
}

/// A provider is not limited to a few request streams: a fifth is opened while four are in use, bounded only by the
/// fetch's table of streams.
#[test]
fn a_provider_with_four_request_streams_open_is_given_a_fifth() {
    let mut f = world(0, 0);
    let plan = Plan::new(f.length, &[Span { off: 0, len: GROUP }]).unwrap();
    for (i, stream) in (8..11).enumerate() {
        f.rx[i + 1] = Some(Rx::new(1, stream, plan.clone(), &f.root));
    }
    assert_eq!(f.streams_of(1), 4);
    let (mut net, mut st, mut out) = (Net::default(), Empty, Sink);
    let mut io = Io {
        session: &mut net,
        store: &mut st,
        out: &mut out,
    };
    assert!(f.open_request(&mut io, 10 * NS, 1, &[Span { off: 0, len: GROUP }]));
    assert_eq!(f.streams_of(1), 5);
    // The table of the fetch still bounds it.
    for slot in f.rx.iter_mut().filter(|s| s.is_none()) {
        *slot = Some(Rx::new(1, 99, plan.clone(), &f.root));
    }
    assert!(!f.open_request(&mut io, 10 * NS, 1, &[Span { off: 0, len: GROUP }]));
}
