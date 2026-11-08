//! Integer helpers shared by the recovery modules: saturating narrowing and the cube root.

/// Narrow to `u64`, saturating at `u64::MAX`.
pub(crate) fn sat(v: u128) -> u64 {
    u64::try_from(v).unwrap_or(u64::MAX)
}

/// The integer cube root: the largest `r` with `r^3 <= n`. Never overflows (the candidate cube is checked).
pub(crate) fn icbrt(n: u128) -> u64 {
    let mut root: u64 = 0;
    // 2^43 cubed exceeds 2^128, so the root fits in 43 bits.
    for bit in (0..43).rev() {
        let cand = root | (1u64 << bit);
        if u128::from(cand).checked_pow(3).is_some_and(|c| c <= n) {
            root = cand;
        }
    }
    root
}
