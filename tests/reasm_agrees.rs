//! A handshake fragment that contradicts what the reassembly holds (another message length, other bytes at an offset
//! both cover) is refused and changes nothing, and the bytes a run holds are never overwritten: the first bytes win.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]

use pinc_transport::conn::ReasmProbe;
use proptest::prelude::*;

/// A fragment: the message length, the offset, and bytes from a small alphabet so forged and real bytes collide.
fn fragment() -> impl Strategy<Value = (usize, usize, Vec<u8>)> {
    (1usize..=24, 0usize..24, prop::collection::vec(0u8..3, 1..12)).prop_map(|(total, off, mut data)| {
        let off = off.min(total - 1);
        data.truncate(total - off);
        (total, off, data)
    })
}

proptest! {
    #[test]
    fn a_refused_fragment_changes_nothing_and_held_bytes_are_never_overwritten(
        calls in prop::collection::vec(fragment(), 1..40)
    ) {
        let mut p = ReasmProbe::new();
        for (total, off, data) in calls {
            let (view, buf) = (p.view(), p.buffer()[..64].to_vec());
            let held = |i: usize| view.runs.iter().any(|&(s, e)| s <= i && i < e);
            let refused = !view.runs.is_empty()
                && (view.total != total || (0..data.len()).any(|k| held(off + k) && buf[off + k] != data[k]));
            let _ = p.add(total, off, &data);
            if refused {
                prop_assert_eq!(p.view(), view, "a refused fragment moved the runs");
                prop_assert_eq!(&p.buffer()[..64], &buf[..], "a refused fragment wrote bytes");
            } else {
                for i in (0..64).filter(|i| held(*i)) {
                    prop_assert_eq!(p.buffer()[i], buf[i], "held byte {} overwritten", i);
                }
            }
        }
    }
}
