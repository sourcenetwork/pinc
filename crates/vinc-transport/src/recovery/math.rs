//! Integer helpers shared by the recovery modules: saturating narrowing, widening multiply-divide, cube root.

/// Narrow to `u64`, saturating at `u64::MAX`.
pub(crate) fn sat(v: u128) -> u64 {
    u64::try_from(v).unwrap_or(u64::MAX)
}

/// `a * n / d` rounded down, saturating. Callers keep `n < 2^64` and `d >= 1`, so the product is below 2^128.
pub(crate) fn mul_div(a: u64, n: u64, d: u64) -> u64 {
    sat(u128::from(a) * u128::from(n) / u128::from(d.max(1)))
}

/// `ceil(a * n / d)`, saturating. Same bounds as [`mul_div`].
pub(crate) fn mul_div_ceil(a: u64, n: u64, d: u64) -> u64 {
    let d = u128::from(d.max(1));
    sat((u128::from(a) * u128::from(n)).div_ceil(d))
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
