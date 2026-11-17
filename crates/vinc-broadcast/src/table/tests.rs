//! The id tables place ids by a keyed hash, so a sender cannot choose where its ids land; no walk is refused, a long
//! one is counted, and a print kept beside an entry moves with its slot.

#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    reason = "tests assert"
)]

use super::*;

fn key(seed: u64) -> IdKey {
    IdKey::new(seed, &TEST_SECRETS).unwrap()
}

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
    let mut m = MidMap::with_capacity(8192, key(0x5eed));
    for id in colliding_low_bits(4096) {
        assert!(m.insert(id, id), "id {id:#x}");
    }
    let lens: Vec<usize> = colliding_low_bits(4096).map(|id| probe_len(&m, id)).collect();
    let (max, total) = (lens.iter().max().unwrap(), lens.iter().sum::<usize>());
    assert!(*max <= 40, "the longest probe was {max}");
    assert!(total <= 4096 * 4, "the probes added up to {total}");
    assert!(colliding_low_bits(4096).all(|id| m.get(id) == Some(id)));
}

#[test]
fn ids_in_a_row_are_spread_under_a_key_that_lines_them_up_in_one_step() {
    // A first secret near a power of two keeps the keyed multiply of small ids below the fold, so one step alone puts
    // ids in a row on slots in a row; the finishing multiply must break that up.
    static LINED_UP: [u64; 7] = [
        0x9e37_79b9_7f4a_4000,
        0xbf58_476d_1ce4_e5b9,
        0x94d0_49bb_1331_11eb,
        0x2545_f491_4f6c_dd1d,
        0xd6e8_feb8_6659_fd93,
        0xff51_afd7_ed55_8ccd,
        0xc4ce_b9fe_1a85_ec53,
    ];
    let mut m = MidMap::with_capacity(8192, IdKey::new(0, &LINED_UP).unwrap());
    for id in 1..=4096u64 {
        assert!(m.insert(id, id), "id {id}");
    }
    let lens: Vec<usize> = (1..=4096u64).map(|id| probe_len(&m, id)).collect();
    let (max, total) = (lens.iter().max().unwrap(), lens.iter().sum::<usize>());
    assert!(*max <= 40, "the longest probe was {max}");
    assert!(total <= 4096 * 4, "the probes added up to {total}");
}

#[test]
fn the_slot_depends_on_the_key_and_not_on_the_low_bits_of_the_id() {
    let (a, b) = (
        MidMap::with_capacity(8192, key(0x5eed)),
        MidMap::with_capacity(8192, key(0x5eee)),
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

/// The home slot of `id` by the documented formula, in 128-bit arithmetic of the test's own: the keyed multiply of
/// `id ^ seed` by the first secret, folded (low half xor high half); then the finishing multiply of that by the
/// hasher's public constant, folded; the low bits of the result.
fn home_by_formula(id: u64, seed: u64, first_secret: u64, slots: u64) -> u64 {
    const PUBLIC: u64 = 0x8bb8_4b93_962e_acc9;
    let fold = |a: u64, b: u64| {
        let r = u128::from(a) * u128::from(b);
        (r as u64) ^ ((r >> 64) as u64)
    };
    fold(fold(id ^ seed, first_secret), PUBLIC) & (slots - 1)
}

#[test]
fn ids_are_placed_by_the_two_step_hash_of_the_endpoints_map_keys() {
    for seed in [0x5eed, 0] {
        let m = MidMap::with_capacity(8192, key(seed));
        let slots = m.keys.len() as u64;
        for id in (0..64u64).map(|i| i.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ i) {
            let want = home_by_formula(id, seed, TEST_SECRETS[0], slots);
            assert_eq!(
                u64::try_from(m.home(id)).unwrap(),
                want,
                "id {id:#x} under seed {seed:#x}"
            );
        }
    }
    // Three answers worked out once and kept as literals.
    let m = MidMap::with_capacity(8192, key(0x5eed));
    assert_eq!((m.home(1), m.home(0xdead_beef)), (1155, 9858));
    assert_eq!(MidMap::with_capacity(8192, key(0)).home(1), 3766);
}

#[test]
fn a_zero_first_secret_is_refused_and_any_other_is_taken() {
    static ZERO_FIRST: [u64; 7] = [0, 2, 3, 4, 5, 6, 7];
    static ZERO_OTHER: [u64; 7] = [1, 0, 0, 0, 0, 0, 0];
    assert_eq!(IdKey::new(5, &ZERO_FIRST), Err(StartError::InvalidKey));
    assert!(IdKey::new(5, &ZERO_OTHER).is_ok());
    assert!(IdKey::new(0, &TEST_SECRETS).is_ok());
}

#[test]
fn a_long_run_is_walked_and_counted_not_refused() {
    let mut m = MidMap::with_capacity(8192, key(0x5eed));
    let ids = same_home(8192, key(0x5eed), 0, 300);
    assert_eq!(m.long_walks(), 0);
    for id in &ids {
        assert!(m.insert(*id, 1), "id {id:#x}");
    }
    assert!(ids.iter().all(|id| m.get(*id) == Some(1)), "every id is found");
    assert!(m.long_walks() > 0, "the long walks are counted");
    assert!(ids.iter().all(|id| m.remove(*id) == Some(1)));
    assert_eq!(m.len, 0);
}

#[test]
fn a_forced_insert_on_a_long_run_drops_only_the_oldest() {
    let slots = 16384usize;
    // Ids that start well away from the run, so they do not shorten or lengthen it.
    let far = |h: usize| {
        let d = (h + slots - 9) % slots;
        (300..=slots - 300).contains(&d)
    };
    let probe = MidMap::with_capacity(8192, key(0x5eed));
    let mut s = Seen::with_capacity(8192, key(0x5eed));
    let run = same_home(8192, key(0x5eed), 9, PROBE_LONG + 1);
    let mut fresh = (1u64 << 40..).filter(|id| far(probe.home(*id)));
    let old = fresh.next().unwrap();
    assert!(s.insert(old, 10, false));
    for id in &run[..PROBE_LONG] {
        assert!(s.insert(*id, 10, false));
    }
    while s.len() < 8192 {
        assert!(s.insert(fresh.next().unwrap(), 10, false));
    }
    assert!(
        !s.insert(run[PROBE_LONG], 10, false),
        "a full set refuses an unforced insert"
    );
    assert!(s.insert(run[PROBE_LONG], 10, true), "a forced one makes room");
    assert!(!s.contains(old, 10), "the oldest id left");
    assert!(
        run.iter().all(|id| s.contains(*id, 10)),
        "the run, and the new id, are all there"
    );
    assert_eq!(s.len(), 8192);
}

#[test]
fn a_print_moves_with_its_entry_and_leaves_with_it() {
    let mut m = MidMap::with_capacity(8192, key(0x5eed));
    m.with_prints();
    let ids = same_home(8192, key(0x5eed), 3, 6);
    for (k, id) in ids.iter().enumerate() {
        assert!(m.insert(*id, 1));
        m.set_print(*id, 100 + k as u64);
    }
    // Removing the second shifts the four behind it back by one slot, each with its print.
    assert_eq!(m.remove(ids[1]), Some(1));
    assert_eq!(m.print(ids[1]), 0, "an id that left has no print");
    for (k, id) in ids.iter().enumerate().filter(|(k, _)| *k != 1) {
        assert_eq!(m.print(*id), 100 + k as u64, "id {k} kept its print");
    }
    // The slot at the end of the run was cleared: an id that takes it starts with none.
    let next = same_home(8192, key(0x5eed), 3, 7)[6];
    assert!(m.insert(next, 1));
    assert_eq!(m.print(next), 0, "a new entry carries no stale print");
    // A map that keeps no prints answers none.
    let mut bare = MidMap::with_capacity(8, key(1));
    assert!(bare.insert(5, 1));
    bare.set_print(5, 9);
    assert_eq!(bare.print(5), 0);
}

#[test]
fn the_dedupe_set_keeps_the_print_of_an_id_that_left_the_log() {
    let mut s = Seen::with_capacity(8, key(0x5eed));
    s.keep_prints();
    s.keep(7, 42, 10);
    assert_eq!((s.contains(7, 10), s.print(7, 10)), (true, Some(42)));
    // An id already seen keeps its time and takes the print.
    assert!(s.insert(8, 11, false));
    assert_eq!(s.print(8, 11), None);
    s.keep(8, 43, 12);
    assert_eq!((s.len(), s.print(8, 12)), (2, Some(43)));
    // The print lapses with the id.
    assert_eq!(s.print(7, 10 + SEEN_TTL + 1), None);
    s.expire(10 + SEEN_TTL + 1);
    assert_eq!(s.print(7, 10 + SEEN_TTL + 1), None);
}
