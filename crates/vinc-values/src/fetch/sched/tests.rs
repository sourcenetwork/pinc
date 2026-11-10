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

/// Byte liveness: bytes arriving are progress. The stall wait grows to three times the gap between stream bytes (twice the
/// delay of the first bytes after the first request), up to the cap, and the stall clock counts from the last bytes.
#[test]
fn stream_bytes_stretch_the_stall_wait_by_their_own_gaps_and_restart_its_clock() {
    use crate::knobs::{BYTE_GAP_CAP, STALL_WAIT};
    let mut f = world(0, 0);
    let (mut net, mut st, mut out) = (Net::default(), Empty, Sink);
    let mut io = Io {
        session: &mut net,
        store: &mut st,
        out: &mut out,
    };
    f.treq = NS;
    f.sw = STALL_WAIT;
    // First bytes 5 s after the request: twice that delay.
    f.on_readable(&mut io, 6 * NS, 7, 100);
    assert_eq!((f.sw, f.lastb), (10 * NS, 6 * NS));
    // A 4 s gap: three times the gap.
    f.on_readable(&mut io, 10 * NS, 7, 100);
    assert_eq!((f.sw, f.lastb), (12 * NS, 10 * NS));
    // The wait never shrinks, and an empty read is not progress.
    f.on_readable(&mut io, 11 * NS, 7, 0);
    assert_eq!((f.sw, f.lastb), (12 * NS, 10 * NS));
    // The stall clock counts from the last bytes.
    assert_eq!(f.poll_timeout(), Some(10 * NS + 12 * NS));
    // A long gap is capped.
    f.on_readable(&mut io, 100 * NS, 7, 100);
    assert_eq!(f.sw, BYTE_GAP_CAP);
    assert_eq!(f.poll_timeout(), Some(100 * NS + BYTE_GAP_CAP));
}

/// The steal re-check timer is armed also when no provider is a candidate for a steal yet (the busy one is fast and not idle),
/// and the call at that time looks again: by then it has been idle long enough to be robbed.
#[test]
fn the_steal_recheck_timer_is_armed_for_a_busy_provider_and_fires_a_new_look() {
    let mut f = world(1_000_000_000, 10_000);
    let (mut net, mut st, mut out) = (Net::default(), Empty, Sink);
    let mut io = Io {
        session: &mut net,
        store: &mut st,
        out: &mut out,
    };
    // One second after its last granule the victim is not idle: nothing to steal, the look is scheduled.
    let new = f.steal(&mut io, 10 * NS, 0);
    assert!(new.is_empty());
    let recheck = 10 * NS + crate::knobs::STEAL_IDLE / 2;
    assert_eq!(f.tw, recheck, "the re-check is armed");
    assert_eq!(f.poll_timeout(), Some(recheck), "and offered to the host");
    // At that time the victim has been silent for two seconds: the call looks again and its work moves.
    f.on_timeout(&mut io, recheck);
    assert!(net.resets >= 1, "the idle victim's stream was reset by the new look");
    assert!(net.opened >= 1, "its work was requested again from another provider");
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
