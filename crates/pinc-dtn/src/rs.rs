//! Systematic Reed-Solomon over GF(2^8) in bounded blocks of at most 255 symbols.
//!
//! A block has `k` data symbols followed by `m` parity symbols, all of the same length, in one contiguous buffer.
//! The code is a Cauchy code: parity symbol `j` is the sum over data symbols `i` of `d_i / ((k + j) ^ i)`, so the
//! generator `[I; C]` is MDS and any `k` of the `k + m` symbols determine the block. Because `k + m <= 255` the
//! values `i` and `k + j` are distinct field elements.
//!
//! Invariants: encoding is a pure function of the data symbols; [`Rs::reconstruct`] needs no scratch memory and no
//! matrix inversion at run time: the `e` missing data symbols are solved from `e` present parity symbols with the
//! closed-form inverse of a Cauchy matrix, `B[i][j] = F_i * G_j / (x_j + y_i)`, where `F_i = prod_l (y_i + x_l) /
//! prod_{l != i} (y_i + y_l)` and `G_j = prod_l (x_j + y_l) / prod_{l != j} (x_j + x_l)`. The cost is `O(e^3)`
//! table loads for the coefficients plus `O(e * (k - e + e) * len)` for the byte work. No path panics or allocates.

use crate::error::DtnError;
use crate::gf256::{inv, mul, mul_add, scale};

/// The most symbols (data plus parity) in one block.
pub const MAX_SYMBOLS: usize = 255;
/// The most symbols that can be missing from one decode: `min(k, m) <= 127` when `k + m <= 255`.
const MAX_ERASURES: usize = 127;

/// A `(k, m)` systematic Reed-Solomon code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rs {
    k: u8,
    m: u8,
}

/// The Cauchy coefficient of data symbol `data` in parity symbol `parity`.
fn coef(k: u8, parity: usize, data: usize) -> u8 {
    // `parity < m` and `k + m <= 255`, so `k + parity` fits a byte; `data < k` so the two operands differ.
    let x = u8::try_from(usize::from(k) + parity).unwrap_or(0);
    let y = u8::try_from(data).unwrap_or(0);
    inv(x ^ y)
}

fn slot(buf: &[u8], i: usize, len: usize) -> Option<&[u8]> {
    buf.get(i.checked_mul(len)?..i.checked_add(1)?.checked_mul(len)?)
}

fn slot_mut(buf: &mut [u8], i: usize, len: usize) -> Option<&mut [u8]> {
    buf.get_mut(i.checked_mul(len)?..i.checked_add(1)?.checked_mul(len)?)
}

impl Rs {
    /// A code with `k` data and `m` parity symbols.
    ///
    /// # Errors
    /// [`DtnError::Params`] if `k` is 0 or `k + m` exceeds [`MAX_SYMBOLS`].
    pub fn new(k: usize, m: usize) -> Result<Self, DtnError> {
        if k == 0 || k.saturating_add(m) > MAX_SYMBOLS {
            return Err(DtnError::Params);
        }
        match (u8::try_from(k), u8::try_from(m)) {
            (Ok(k), Ok(m)) => Ok(Self { k, m }),
            _ => Err(DtnError::Params),
        }
    }

    /// The number of data symbols.
    pub const fn k(&self) -> usize {
        self.k as usize
    }

    /// The number of parity symbols.
    pub const fn m(&self) -> usize {
        self.m as usize
    }

    /// The number of symbols in a block.
    pub const fn n(&self) -> usize {
        self.k as usize + self.m as usize
    }

    /// Compute the parity symbols of `block`, which holds `n` symbols of `len` bytes: the data first, the parity
    /// last (overwritten).
    ///
    /// # Errors
    /// [`DtnError::Buffer`] if `len` is 0 or `block` is not `n * len` bytes.
    pub fn encode(&self, len: usize, block: &mut [u8]) -> Result<(), DtnError> {
        if len == 0 || self.n().checked_mul(len) != Some(block.len()) {
            return Err(DtnError::Buffer);
        }
        let (data, parity) = block.split_at_mut(self.k() * len);
        for (j, p) in parity.chunks_exact_mut(len).enumerate() {
            p.fill(0);
            for (i, d) in data.chunks_exact(len).enumerate() {
                mul_add(p, d, coef(self.k, j, i));
            }
        }
        Ok(())
    }

    /// Recover every missing symbol of `block` from any `k` present ones. `present[s]` says whether symbol `s` of
    /// the block holds valid bytes; the bytes of an absent symbol are ignored and overwritten. On success every
    /// symbol, data and parity, is valid.
    ///
    /// # Errors
    /// [`DtnError::Buffer`] if `len` is 0, `block` is not `n * len` bytes or `present` is not `n` entries;
    /// [`DtnError::Incomplete`] if fewer than `k` symbols are present (the block is then left unchanged).
    pub fn reconstruct(&self, len: usize, block: &mut [u8], present: &[bool]) -> Result<(), DtnError> {
        if present.len() != self.n() || len == 0 || self.n().checked_mul(len) != Some(block.len()) {
            return Err(DtnError::Buffer);
        }
        let k = self.k();
        let (data_present, parity_present) = present.split_at(k);
        let held = present.iter().filter(|p| **p).count();
        if held < k {
            return Err(DtnError::Incomplete);
        }
        // Missing data columns `y`, and as many present parity rows (`row` index, `x` value) as there are columns.
        let mut ys = [0u8; MAX_ERASURES];
        let mut e = 0;
        for (i, _) in data_present.iter().enumerate().filter(|(_, p)| !**p) {
            *ys.get_mut(e).ok_or(DtnError::Params)? = u8::try_from(i).map_err(|_| DtnError::Params)?;
            e += 1;
        }
        if e > 0 {
            self.solve(len, block, parity_present, ys.get(..e).ok_or(DtnError::Params)?)?;
        }
        self.encode(len, block)
    }

    /// Solve the `ys.len()` missing data symbols from the first present parity rows (see the module docs).
    fn solve(self, len: usize, block: &mut [u8], parity_present: &[bool], ys: &[u8]) -> Result<(), DtnError> {
        let (k, e) = (self.k(), ys.len());
        let mut rows = [0usize; MAX_ERASURES];
        let mut xs = [0u8; MAX_ERASURES];
        let used = parity_present.iter().enumerate().filter(|(_, p)| **p).take(e);
        for (t, (j, _)) in used.enumerate() {
            *rows.get_mut(t).ok_or(DtnError::Params)? = j;
            *xs.get_mut(t).ok_or(DtnError::Params)? = u8::try_from(k + j).map_err(|_| DtnError::Params)?;
        }
        let (rows, xs) = (
            rows.get(..e).ok_or(DtnError::Params)?,
            xs.get(..e).ok_or(DtnError::Params)?,
        );
        let (data, parity) = block.split_at_mut(k * len);
        let missing = |i: usize| ys.contains(&u8::try_from(i).unwrap_or(0));
        // Syndromes: the parity row minus the contribution of every known data symbol, scaled by G_t.
        for (t, &row) in rows.iter().enumerate() {
            let s = slot_mut(parity, row, len).ok_or(DtnError::Buffer)?;
            for (i, d) in data.chunks_exact(len).enumerate().filter(|(i, _)| !missing(*i)) {
                mul_add(s, d, coef(self.k, row, i));
            }
            let x = *xs.get(t).ok_or(DtnError::Params)?;
            scale(s, g_factor(x, t, xs, ys));
        }
        // Each missing data symbol is F_i times the Cauchy combination of the scaled syndromes.
        for (s_idx, &y) in ys.iter().enumerate() {
            let out = slot_mut(data, usize::from(y), len).ok_or(DtnError::Buffer)?;
            out.fill(0);
            for (t, &row) in rows.iter().enumerate() {
                let x = *xs.get(t).ok_or(DtnError::Params)?;
                mul_add(out, slot(parity, row, len).ok_or(DtnError::Buffer)?, inv(x ^ y));
            }
            scale(out, f_factor(y, s_idx, xs, ys));
        }
        Ok(())
    }
}

/// `prod_l (v + a_l)` over `a`.
fn prod_sum(v: u8, a: &[u8]) -> u8 {
    a.iter().fold(1, |acc, &l| mul(acc, v ^ l))
}

/// `prod_{l != skip} (v + a_l)` over `a`.
fn prod_sum_skip(v: u8, a: &[u8], skip: usize) -> u8 {
    a.iter()
        .enumerate()
        .filter(|(l, _)| *l != skip)
        .fold(1, |acc, (_, &l)| mul(acc, v ^ l))
}

/// `F_i = prod_l (y_i + x_l) / prod_{l != i} (y_i + y_l)`.
fn f_factor(y: u8, idx: usize, xs: &[u8], ys: &[u8]) -> u8 {
    mul(prod_sum(y, xs), inv(prod_sum_skip(y, ys, idx)))
}

/// `G_j = prod_l (x_j + y_l) / prod_{l != j} (x_j + x_l)`.
fn g_factor(x: u8, idx: usize, xs: &[u8], ys: &[u8]) -> u8 {
    mul(prod_sum(x, ys), inv(prod_sum_skip(x, xs, idx)))
}
