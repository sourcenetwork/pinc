//! The id tables place ids by a keyed hash, so a sender cannot choose where its ids land, and no walk passes the
//! probe bound.

#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]

use super::*;

const KEY: IdKey = IdKey::from_seed(0x5eed);

/// Ids that all share their low bits, which under a placement by those bits all start at one slot.
fn colliding_low_bits(n: u64) -> impl Iterator<Item = u64> {
    (0..n).map(|i| (i << 32) | 5)
}

/// The slots a lookup of `key` walks: the distance from its home to where it is.
fn probe_len(m: &MidMap, key: u64) -> usize {
    (m.slot(key).unwrap() + m.keys.len() - m.home(key)) % m.keys.len() + 1
}

/// `n` ids that start at slot `home` of a map of `cap` entries under `key`, found by search.
fn same_home(cap: usize, key: IdKey, home: usize, n: usize) -> Vec<u64> {
    let m = MidMap::with_capacity(cap, key);
    (0u64..).filter(|id| m.home(*id) == home).take(n).collect()
}

#[test]
fn ids_that_collide_by_their_low_bits_cost_a_bounded_number_of_probes() {
    let mut m = MidMap::with_capacity(8192, KEY);
    for id in colliding_low_bits(4096) {
        assert_eq!(m.insert(id, id), Ok(()), "id {id:#x}");
    }
    let lens: Vec<usize> = colliding_low_bits(4096).map(|id| probe_len(&m, id)).collect();
    let (max, total) = (lens.iter().max().unwrap(), lens.iter().sum::<usize>());
    assert!(*max <= 40, "the longest probe was {max}");
    assert!(total <= 4096 * 4, "the probes added up to {total}");
    assert!(colliding_low_bits(4096).all(|id| m.get(id) == Some(id)));
}

#[test]
fn the_slot_depends_on_the_key_and_not_on_the_low_bits_of_the_id() {
    let (a, b) = (
        MidMap::with_capacity(8192, KEY),
        MidMap::with_capacity(8192, IdKey::from_seed(0x5eee)),
    );
    let homes: alloc::collections::BTreeSet<usize> = colliding_low_bits(4096).map(|id| a.home(id)).collect();
    assert!(
        homes.len() > 2000,
        "4096 ids with equal low bits start at {} slots",
        homes.len()
    );
    let moved = colliding_low_bits(4096).filter(|id| a.home(*id) != b.home(*id)).count();
    assert!(
        moved > 4000,
        "only {moved} of 4096 ids start elsewhere under another key"
    );
}

#[test]
fn a_run_past_the_bound_is_refused_and_a_lookup_across_it_is_told_so() {
    let mut m = MidMap::with_capacity(8192, KEY);
    let ids = same_home(8192, KEY, 0, PROBE_MAX + 2);
    for id in &ids[..PROBE_MAX] {
        assert_eq!(m.insert(*id, 1), Ok(()));
    }
    let (over, next) = (ids[PROBE_MAX], ids[PROBE_MAX + 1]);
    assert_eq!(m.insert(over, 1), Err(Refused::Probe));
    assert_eq!(m.lookup(over), Err(ProbeLimit));
    assert!(!m.fits_probe(over) && m.get(over).is_none());
    assert_eq!(
        m.lookup(ids[PROBE_MAX - 1]),
        Ok(Some(1)),
        "the last one inside the bound is found"
    );
    // Removing one makes room: the walk is bounded, the table is not stuck.
    assert_eq!(m.remove(ids[3]), Some(1));
    assert_eq!(m.insert(next, 2), Ok(()));
    assert_eq!(m.get(next), Some(2));
    assert!(
        ids[..PROBE_MAX]
            .iter()
            .filter(|id| **id != ids[3])
            .all(|id| m.get(*id) == Some(1))
    );
}

#[test]
fn the_dedupe_set_refuses_an_id_past_the_bound_and_keeps_the_rest() {
    let mut s = Seen::with_capacity(8192, KEY);
    let ids = same_home(8192, KEY, 7, PROBE_MAX + 1);
    for id in &ids[..PROBE_MAX] {
        assert_eq!(s.insert(*id, 10, false), Ok(()));
    }
    assert_eq!(s.insert(ids[PROBE_MAX], 10, false), Err(Refused::Probe));
    assert_eq!(s.insert(ids[PROBE_MAX], 10, true), Err(Refused::Probe));
    assert_eq!(s.lookup(ids[PROBE_MAX], 10), Err(ProbeLimit));
    assert_eq!(s.lookup(ids[0], 10), Ok(true));
    assert_eq!(s.len(), PROBE_MAX, "a refused id is not queued for expiry");
}
