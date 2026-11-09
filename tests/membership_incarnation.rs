//! Incarnations and the address tag: a counter with seal and unseal hooks, a hybrid clock that never goes below a
//! remembered value, record sequences that never wrap backwards, and restarts across clock jumps.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::struct_excessive_bools,
    clippy::cast_possible_truncation,
    clippy::doc_markdown,
    clippy::bool_to_int_with_if,
    clippy::manual_range_contains,
    clippy::manual_assert_eq,
    clippy::redundant_closure_for_method_calls,
    clippy::assert_is_empty,
    clippy::len_zero,
    clippy::unused_self,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::too_many_arguments
)]

#[path = "membership_world.rs"]
mod world;

use proptest::prelude::*;
use vinc_membership::codec::{Alive, Entry, Frame, Record};
use vinc_membership::incarnation::{AddressTag, Incarnation, IncarnationError, MOVE_SETTLE};
use vinc_membership::session::StoreError;
use vinc_membership::{Config, Event, Local, Membership, StartError, Trace};
use world::{Host, SEC, World, id};

#[derive(Default)]
struct L {
    persistent: bool,
    sealed: Option<u64>,
    fail_seal: bool,
    fail_unseal: bool,
    reflexive: bool,
    ticket: u8,
}

impl Local for L {
    fn version(&self) -> u16 {
        1
    }
    fn reflexive_known(&self) -> bool {
        self.reflexive
    }
    fn address_hash(&self, moves: u8) -> [u8; 8] {
        [self.ticket, moves, 0, 0, 0, 0, 0, 0]
    }
    fn persistent(&self) -> bool {
        self.persistent
    }
    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        if self.fail_unseal {
            Err(StoreError)
        } else {
            Ok(self.sealed)
        }
    }
    fn seal_counter(&mut self, epoch: u64) -> Result<(), StoreError> {
        if self.fail_seal {
            return Err(StoreError);
        }
        self.sealed = Some(epoch);
        Ok(())
    }
}

#[test]
fn a_counter_grows_on_every_restart_whatever_the_clock_says() {
    let mut l = L {
        persistent: true,
        ..L::default()
    };
    let mut last = 0;
    for wall in [5_000_000u64, 10, 4_000_000_000, 0, 0, 7] {
        let inc = Incarnation::start(&mut l, wall, 0).unwrap();
        assert_eq!(
            inc.epoch(),
            last + 1,
            "one more than the unsealed value, not the wall clock"
        );
        assert_eq!(l.sealed, Some(inc.epoch()), "sealed before it is used");
        assert_eq!(inc.word(), inc.epoch() << 16);
        last = inc.epoch();
    }
    // A remembered floor from elsewhere lifts it.
    assert_eq!(Incarnation::start(&mut l, 0, 100).unwrap().epoch(), 101);
}

#[test]
fn a_store_that_cannot_be_read_or_written_stops_the_start() {
    let mut l = L {
        persistent: true,
        fail_unseal: true,
        ..L::default()
    };
    assert_eq!(
        Incarnation::start(&mut l, 1, 0),
        Err(IncarnationError::Store(StoreError))
    );
    l.fail_unseal = false;
    l.fail_seal = true;
    assert_eq!(
        Incarnation::start(&mut l, 1, 0),
        Err(IncarnationError::Store(StoreError))
    );
    // The node refuses to start rather than guess an epoch.
    let mut h = Host {
        me: id(0),
        persistent: true,
        fail_seal: true,
        ..Host::default()
    };
    let cfg = Config {
        me: id(0),
        is_hub: true,
        hubs: &[],
        trace: false,
    };
    assert!(matches!(
        Membership::start(&cfg, &mut h, 0, 1, 0),
        Err(StartError::Incarnation(IncarnationError::Store(_)))
    ));
}

#[test]
fn the_hybrid_clock_never_goes_below_a_remembered_value() {
    let mut l = L::default();
    let a = Incarnation::start(&mut l, 1_000, 0).unwrap();
    assert_eq!(a.epoch(), 1_001, "the wall clock plus one, as milliseconds");
    assert_eq!(l.sealed, None, "nothing is persisted without a persistent store");
    // The clock jumped back an hour; the host remembered the old epoch.
    let b = Incarnation::start(&mut l, 5, a.epoch()).unwrap();
    assert!(b.word() > a.word());
    // Without a remembered value the epoch is low; a peer reporting the old one moves it above.
    let mut c = Incarnation::start(&mut l, 5, 0).unwrap();
    assert!(c.word() < a.word());
    assert_eq!(c.observe(&mut l, a.word()), Ok(true));
    assert!(c.word() > a.word());
    assert_eq!(
        c.observe(&mut l, a.word()),
        Ok(false),
        "at or below ours: nothing to do"
    );
    assert_eq!(c.observe(&mut l, c.word()), Ok(false));
}

#[test]
fn the_record_sequence_never_wraps_backwards() {
    let mut l = L {
        persistent: true,
        ..L::default()
    };
    let mut inc = Incarnation::start(&mut l, 0, 0).unwrap();
    let mut last = inc.word();
    for _ in 0..70_000 {
        let w = inc.next_record(&mut l).unwrap();
        assert!(w > last);
        last = w;
    }
    assert_eq!(inc.epoch(), 2, "a full sequence started the next epoch");
    assert_eq!(l.sealed, Some(2), "and sealed it");
    // A wrap whose epoch cannot be sealed leaves the value unchanged.
    let mut inc = Incarnation::start(&mut l, 0, 0).unwrap();
    for _ in 0..65_535 {
        inc.next_record(&mut l).unwrap();
    }
    let before = inc;
    l.fail_seal = true;
    assert!(inc.next_record(&mut l).is_err());
    assert_eq!(inc, before);
    // The epoch space ends loudly.
    let mut l = L {
        persistent: true,
        sealed: Some((1 << 48) - 1),
        ..L::default()
    };
    assert_eq!(Incarnation::start(&mut l, 0, 0), Err(IncarnationError::Exhausted));
}

proptest! {
    #[test]
    fn the_word_never_decreases(
        persistent in any::<bool>(),
        wall in any::<u32>(),
        ops in proptest::collection::vec((0u8..3, any::<u64>(), any::<bool>()), 0..200),
    ) {
        let mut l = L { persistent, ..L::default() };
        let mut inc = Incarnation::start(&mut l, u64::from(wall), 0).unwrap();
        let mut last = inc.word();
        for (op, seen, fail) in ops {
            l.fail_seal = fail;
            let _ = match op {
                0 => inc.next_record(&mut l).map(|_| ()),
                1 => inc.observe(&mut l, seen >> 17).map(|_| ()),
                _ => inc.observe(&mut l, last.saturating_add(seen % 70_000)).map(|_| ()),
            };
            prop_assert!(inc.word() >= last, "{} < {}", inc.word(), last);
            last = inc.word();
        }
    }

    #[test]
    fn a_restart_from_a_sealed_epoch_is_above_every_earlier_life(
        wall in proptest::collection::vec(any::<u32>(), 1..12),
    ) {
        let mut l = L { persistent: true, ..L::default() };
        let mut prev = 0;
        for w in wall {
            let inc = Incarnation::start(&mut l, u64::from(w), 0).unwrap();
            prop_assert!(inc.word() > prev);
            prev = inc.word();
        }
    }
}

#[test]
fn the_address_tag_counts_a_move_once_per_instant_and_settles() {
    let mut l = L {
        reflexive: true,
        ticket: 3,
        ..L::default()
    };
    let mut tag = AddressTag::default();
    let t0 = tag.tag(0, &l);
    assert_eq!(t0, [3, 0, 0, 0, 0, 0, 0, 0]);
    tag.moved(10);
    tag.moved(10);
    assert_eq!(tag.moves(), 1, "two address changes at one instant are one move");
    assert_eq!(
        tag.tag(10, &l),
        [3, 1, 0, 0, 0, 0, 0, 0],
        "the counter alone changes the tag"
    );
    // A move while the reflexive address is unknown keeps the previous tag for the settle time.
    l.reflexive = false;
    tag.moved(100);
    assert_eq!(tag.tag(101, &l), [3, 1, 0, 0, 0, 0, 0, 0]);
    l.ticket = 9;
    assert_eq!(
        tag.tag(100 + MOVE_SETTLE - 1, &l),
        [3, 1, 0, 0, 0, 0, 0, 0],
        "still settling"
    );
    assert_eq!(tag.tag(100 + MOVE_SETTLE, &l), [9, 2, 0, 0, 0, 0, 0, 0], "settled");
    // Once the address is known the new tag is taken at once.
    l.reflexive = true;
    l.ticket = 4;
    tag.moved(500);
    assert_eq!(tag.tag(501, &l), [4, 3, 0, 0, 0, 0, 0, 0]);
    // The counter wraps modulo 256 without a panic.
    for t in 1000..1300u64 {
        tag.moved(t);
    }
    assert_eq!(tag.moves(), ((3 + 300) % 256) as u8);
}

#[test]
fn a_clock_that_went_back_across_a_restart_is_lifted_above_the_hub_roster() {
    let mut w = World::new(2, 2, 100 * SEC);
    w.attach_all();
    w.run(5 * SEC);
    let old = w.nodes[2].m.incarnation();
    assert!(old >> 16 > 1_000_000);
    // Restart with a wall clock an hour in the past and nothing remembered.
    let hubs = [id(0), id(1)];
    let mut host = Host {
        me: id(2),
        version: 1,
        ticket: 2,
        reflexive: true,
        ..Host::default()
    };
    let cfg = Config {
        me: id(2),
        is_hub: false,
        hubs: &hubs,
        trace: true,
    };
    w.nodes[2].m = Membership::start(&cfg, &mut host, w.now, 10, 0).unwrap();
    w.nodes[2].h = host;
    assert!(
        w.nodes[2].m.incarnation() < old,
        "the restart came up below the old life"
    );
    for hub in 0..2 {
        w.close_session(2, hub, 0);
    }
    w.run(SEC);
    for hub in 0..2 {
        w.connect(2, hub);
    }
    w.run(5 * SEC);
    let new = w.nodes[2].m.incarnation();
    assert!(
        new > old,
        "a hub told the node about its old incarnation and it moved above"
    );
    assert!(
        w.traces[2]
            .iter()
            .any(|t| matches!(t, Trace::Incarnation { inc } if *inc == new))
    );
    for i in [0, 1, 3] {
        let seen = w.nodes[i].m.members().find(|(m, _)| **m == id(2)).unwrap().1.inc;
        assert_eq!(seen, new, "node {i} follows the new life");
    }
    assert!(
        w.count_events(3, |e| matches!(e, Event::MemberJoined { member } if *member == id(2))) >= 2,
        "a restart is a rejoin"
    );
    // The roster at a hub never went below the old record.
    for hub in 0..2 {
        assert!(w.nodes[hub].m.members().all(|(_, r)| r.inc >= 1 << 16));
    }
}

#[test]
fn a_hub_reports_a_stale_incarnation_without_regressing_its_roster() {
    let mut w = World::new(1, 1, 100 * SEC);
    w.attach_all();
    w.run(5 * SEC);
    let cur = w.nodes[1].m.incarnation();
    let low = Record {
        inc: cur - (1 << 16),
        ver: 1,
        thash: [1; 8],
    };
    w.inject(
        0,
        1,
        &Frame::Hello(vinc_membership::codec::Hello {
            rec: low,
            snap: false,
            homed: false,
        }),
    );
    let held = w.nodes[0].m.members().find(|(m, _)| **m == id(1)).unwrap().1.inc;
    assert_eq!(held, cur, "the roster kept the newer record");
    // And the delta about the node itself went back to it.
    let sent = w.frames.iter().filter(|f| f.1 == 0 && f.2 == 1 && f.3[4] == 3).count();
    assert!(sent >= 1);
}

#[test]
fn an_unsealable_observation_is_loud_and_leaves_the_word_alone() {
    let mut w = World::new(1, 1, 100 * SEC);
    w.attach_all();
    w.run(5 * SEC);
    w.nodes[1].h.persistent = true;
    w.nodes[1].h.fail_seal = true;
    let cur = w.nodes[1].m.incarnation();
    let rec = Record {
        inc: cur + (5 << 16),
        ver: 1,
        thash: [0; 8],
    };
    let me = id(1);
    w.inject(
        1,
        0,
        &Frame::Delta(Entry {
            member: &me,
            rec,
            alive: Alive::Alive,
        }),
    );
    assert!(w.nodes[1].m.seal_failed());
    assert_eq!(w.nodes[1].m.incarnation(), cur);
}
